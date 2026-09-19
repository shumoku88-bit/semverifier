# node-semver upstream issue draft

Date: 2026-09-19

## Why this issue exists

This is a draft for discussion with node-semver maintainers.

The goal is **not** to open a pull request immediately.

The goal is to report that `Range.intersects()` currently disagrees with
actual range membership in more than one semantic direction, show minimal
reproductions, summarize the independent evidence, and ask whether a
range-level witness-based repair is a welcome direction.

The draft deliberately keeps the Semverifier background short. The upstream
issue should be understandable even if the maintainer has never seen Lean or
Semverifier.

## Plain-language meaning for the Semverifier project

What we are telling node-semver maintainers is:

> We found cases where `Range.intersects()` says two ranges do not intersect
> even though a concrete version satisfies both, and other cases where it says
> they do intersect even though no version satisfies both under the default
> prerelease rules.
>
> These are not isolated spellings. They reduce to a small number of semantic
> families and appear to come from doing the final Range-level decision through
> independent Comparator-pair overlap checks.
>
> We built and extensively tested a range-level witness-search prototype with
> substantial AI assistance. It fixes the observed disagreement set in our
> corpus, but it is slower on large disjoint unions. Before proposing a code change, we would like to know whether
> maintainers consider this semantic direction appropriate.

That is the entire purpose of the issue.

## Proposed title

```text
[BUG] Range.intersects() can disagree with actual shared-version existence
```

## Proposed issue body

### Is there an existing issue for this?

I searched the existing issues and pull requests.

This overlaps with the prerelease false-negative reported in #884 and the
near-zero comparator issue in #885, but the behavior described here is broader:
the same Range-level intersection path also produces false positives and
operand-order asymmetry.

### Current Behavior

`Range.intersects()` can disagree with the existence of a concrete SemVer
version that satisfies both ranges.

There are both false-negative and false-positive cases under the default
prerelease semantics.

A compact false negative:

```js
const semver = require('semver')

semver.intersects(
  '1.2.3-alpha.2',
  '1.2.3-alpha.2 - 1.2.3'
) // false

semver.satisfies(
  '1.2.3-alpha.2',
  '1.2.3-alpha.2'
) // true

semver.satisfies(
  '1.2.3-alpha.2',
  '1.2.3-alpha.2 - 1.2.3'
) // true
```

So `1.2.3-alpha.2` is a concrete shared version, but `intersects()` reports
no intersection.

There are also false positives.

For example:

```js
semver.intersects('*', '1.2.3-alpha.2') // true
semver.intersects('1.2.3-alpha.2', '*') // false
```

Under the default prerelease rule, `*` does not admit
`1.2.3-alpha.2`, so there is no shared version here.

The fact that reversing the operands changes the result also means the current
operation is not symmetric for this case.

Another false-positive shape is a stable open gap:

```js
semver.intersects('>0.0.0', '<0.0.1') // true
```

There is no stable SemVer strictly between `0.0.0` and `0.0.1`, and default
prerelease handling does not make an intervening prerelease admissible.

### Expected Behavior

`Range.intersects(a, b)` should be true exactly when there exists at least one
SemVer version accepted by both ranges under the selected options.

In particular:

- the result should be symmetric in `a` and `b`;
- a true result should have at least one concrete shared version;
- a false result should not discard a concrete shared version that both ranges
  accept.

### Steps To Reproduce

Using node-semver current main at:

```text
6e05b7637396ac66522cff8731f07cfe0ef49a29
```

run:

```js
const semver = require('semver')

console.log(
  semver.intersects(
    '1.2.3-alpha.2',
    '1.2.3-alpha.2 - 1.2.3'
  )
)

console.log(
  semver.satisfies(
    '1.2.3-alpha.2',
    '1.2.3-alpha.2'
  )
)

console.log(
  semver.satisfies(
    '1.2.3-alpha.2',
    '1.2.3-alpha.2 - 1.2.3'
  )
)

console.log(
  semver.intersects('*', '1.2.3-alpha.2')
)

console.log(
  semver.intersects('1.2.3-alpha.2', '*')
)

console.log(
  semver.intersects('>0.0.0', '<0.0.1')
)
```

Observed:

```text
false
true
true
true
false
true
```

### Additional investigation

Using an AI-assisted verification workflow, I compared current node-semver
`Range.intersects()` against a small verified SemVer range-intersection oracle:

https://github.com/shumoku88-bit/semverifier

This investigation used substantial AI assistance. The reproductions,
automated audits, generated test results, and supporting audit records are
preserved in that repository so the evidence can be inspected independently.

On a deterministic 202-range corpus:

```text
202 x 202 = 40,804 ordered pairs
```

the current node-semver result differed on:

```text
4  false negatives
90 false positives
34 asymmetric unordered pairs
```

The 90 ordered false positives reduce to 62 unordered pairs and partition into
four recurring semantic families:

```text
null-below-zero
exact-prerelease / ANY asymmetry
stable open gaps
prerelease-boundary overlap
```

This suggests the problem is broader than one prerelease spelling.

The current `Range.intersects()` implementation decomposes a Range pair into
Comparator pairs and asks `Comparator.intersects()` pairwise. That loses some
Range-level context, especially prerelease admission, and pairwise precedence
overlap is not always the same thing as existence of a concrete shared SemVer.

### Prototype repair direction

With AI assistance, I tested a local prototype that makes the final
Range-level decision extensionally:

1. collect a finite set of critical versions around comparator boundaries;
2. test those concrete versions against both original comparator sets using
   node-semver's existing `testSet`;
3. return true only when one concrete candidate satisfies both sets.

The candidate shape comes from stable cores, next patches, prerelease floors,
the boundary itself, and the immediate prerelease successor where relevant.

On the same 40,804-pair corpus, the prototype changed exactly the previously
observed 94 disagreements:

```text
4  false -> true
90 true  -> false
```

and changed none of the other 40,710 ordered pairs.

Additional local validation included:

```text
51 / 51 node-semver test suites passing
9,444 assertions passing
100% statement / branch / function / line coverage
ESLint clean
template-oss-check passing
14,035 generated range-pair checks with no new observed semantic counterexample
6,400 strict-vs-loose generated comparisons with no observed mismatch
```

### Performance trade-off

The witness-based prototype is slower than the current pairwise implementation.

Typical small-range cases remained in the single-digit microsecond range, but
an adversarial 20 x 20 disjoint union benchmark was about 17x slower.

So I do not want to assume this is the right implementation trade-off for
node-semver.

Before opening a pull request, would maintainers be interested in a
Range-level witness-based repair direction, or would you prefer a narrower
change that preserves the current performance structure?

If the range-level direction is welcome, I can prepare a minimal PR with a
small regression set covering the known semantic families and
`includePrerelease` behavior.

### Environment

```text
- node-semver: 7.8.5 (commit 6e05b7637396ac66522cff8731f07cfe0ef49a29)
- Node: v24.13.0
- npm: 11.6.2
- OS: macOS 15.7.9 (Darwin 24.6.0)
- architecture: x86_64
```

The local validation branch was:

```text
audit/range-intersects-proved-boundary
```

### Related

- #884: prerelease/shared-version false negative, closed unmerged
- #885: near-zero comparator false negative, currently open
- #521 / #538: historical `<0.0.0` / X-range intersection work

## What should not be copied into the upstream issue

Do not paste the entire Semverifier proof history.

Do not lead with Lean theorem names.

Do not claim that the JavaScript patch is formally proved correct for every
node-semver input.

Do not hide the performance regression.

Do not say the current implementation is simply "wrong" in every sense. The
issue is specifically that the observed Range-level result can diverge from
concrete shared-version existence under documented matching semantics.

## Before posting

Immediately before creating the upstream issue:

1. confirm node-semver `main` has not moved past the audited commit in a way
   that changes `Range.intersects()`;
2. confirm #885 is still open and #884 remains closed/unmerged;
3. search for a newer duplicate issue;
4. use the repository Bug issue template;
5. keep the first reproduction and expected behavior near the top;
6. link this Semverifier repository only as supporting evidence, not as a
   prerequisite for understanding the report;
7. keep the AI-assistance disclosure in the posted issue so authorship and
   verification provenance are transparent.
