# node-semver Intersection False-Positive Family Audit

Date: 2026-09-19

## Scope

This checkpoint partitions the 62 unordered differential false-positive pairs
recorded by the complete Semverifier/node-semver intersection matrix.

Pinned upstream target:

```text
npm/node-semver
6e05b7637396ac66522cff8731f07cfe0ef49a29
package version: 7.8.5
```

Semverifier baseline:

```text
shumoku88-bit/semverifier
60762b3af75ad489c9600927131bda235dbfcd37
```

The complete matrix remains described in
[NODE_SEMVER_FULL_INTERSECTION_AUDIT.md](NODE_SEMVER_FULL_INTERSECTION_AUDIT.md).

This document does not treat 62 pairs as 62 unrelated bugs. The goal is to
identify the smallest number of semantic mechanisms that explain every pair.

## Partition result

All 62 unordered false-positive pairs fall into exactly four families:

```text
null-below-zero                 17
exact-prerelease-asymmetry      34
stable-open-gap                  3
prerelease-boundary-overlap      8
                               ---
                                62
```

There are no unclassified pairs.

The first two families are driven by special-case control flow around
`Comparator.ANY` / exact comparators. The latter two are driven by a broader
mismatch between comparator-order overlap and actual range satisfiability.

## Family 1: null-below-zero

Count:

```text
17 unordered pairs
34 ordered false-positive rows
```

Representative:

```text
<0.0.0
*
```

Semverifier proves these ranges disjoint under default prerelease handling.
Pinned node-semver reports intersection in both argument orders.

### Why the semantic intersection is empty

Under node-semver's own documented default range semantics, prerelease versions
do not satisfy a comparator set unless the set contains a prerelease comparator
with the same major/minor/patch tuple.

There is no stable SemVer version below `0.0.0`. Therefore `<0.0.0` has no
matching version under default options.

### Current-source trace

Broad wildcard forms normalize to an empty comparator / ANY. In
`classes/range.js`, `replaceStars` removes `*`, while `replaceGTE0`
also reduces default `>=0.0.0` to ANY.

In `classes/comparator.js`, `Comparator.intersects()` handles exact/ANY
cases before the later null-lower-bound guards:

```text
if (this.operator === '') {
  if (this.value === '') {
    return true
  }
  ...
} else if (comp.operator === '') {
  if (comp.value === '') {
    return true
  }
  ...
}
```

Only afterward does the method check the default-mode `<0.0.0...` guard.

So when one side has normalized to ANY, intersection can return `true`
without consulting the null-lower-bound logic.

A second contributing boundary is `isSatisfiable` in `classes/range.js`.
For a one-comparator set, its pairwise loop has nothing to compare, so it
returns `true` without asking whether the comparator set actually contains
any version.

### Upstream history

This family overlaps historical issue #521, where maintainers explicitly
confirmed `<0.0.0` versus X-range intersection as a bug. Merged PR #538
added lower-bound guards and fixed the reported forms.

The current matrix demonstrates residual forms on the pinned current main,
especially forms that normalize to ANY and reach the earlier special-case
returns.

Older PR #271 introduced wildcard support for range intersection, and the
current ANY behavior should be considered when evaluating any repair.

### Minimal repair question

Do not simply move or duplicate the `<0.0.0` check yet.

The underlying question is whether ANY may short-circuit comparator
intersection when the other comparator denotes an empty range under the active
range-matching semantics.

That question should be answered together with Family 2 because both cross the
same exact/ANY control-flow boundary.

## Family 2: exact-prerelease-asymmetry

Count:

```text
34 unordered pairs
34 ordered false-positive rows
34 asymmetric unordered pairs
```

Every pair in this family is asymmetric.

Representative:

```text
*
1.2.3-alpha.2
```

Pinned node-semver behavior:

```text
Range("*").intersects(Range("1.2.3-alpha.2")) = true
Range("1.2.3-alpha.2").intersects(Range("*")) = false
```

Semverifier proves the ranges disjoint under default prerelease handling.

### Why the semantic intersection is empty

A wildcard range does not opt into prereleases by default. Therefore
`1.2.3-alpha.2` is not a member of `*`.

The exact prerelease range contains only that prerelease version, so there is
no common member.

### Current-source trace

The asymmetry follows directly from the two branches at the beginning of
`Comparator.intersects()`.

When ANY is `this`:

```text
if (this.operator === '') {
  if (this.value === '') {
    return true
  }
}
```

The method returns `true` immediately.

When the exact prerelease is `this` and ANY is the other comparator, the
opposite exact-comparator path builds a one-comparator Range and calls
`Range.test()`.

That path reaches `testSet`, which applies normal prerelease admission and
rejects `1.2.3-alpha.2` for a comparator set containing only ANY.

Thus the two argument orders follow different semantic paths.

The 34 corpus pairs are surface variants of the same mechanism. Examples such
as `*`, `x`, `X`, `^*`, `~*`, `* - *`, and default
`>=0.0.0` normalize to or expose an ANY branch. Both bare and explicit
`=1.2.3-alpha.2` exact syntax are represented.

### Upstream history

node-semver's own `test/ranges/intersects.js` deliberately checks each range
fixture in both argument orders with the same expected result, so symmetry is
an upstream test invariant, not merely a Semverifier preference.

Historical issue #239 reported a different asymmetric `intersects()` defect,
and merged PR #274 corrected that algorithmic ordering problem.

Issue #254 also documented prerelease inconsistency when an exact version is
compared with a range, though its concrete examples and implementation era
differ from this current ANY/prerelease case.

No current issue or PR was found that directly names this exact wildcard versus
exact-prerelease asymmetry on the pinned main.

### Minimal repair question

This family is a strong candidate for a focused upstream report because it has
three independent facts:

1. Semverifier proves disjointness;
2. node-semver's documented prerelease rule excludes the exact prerelease from
   the wildcard range;
3. node-semver returns different answers when the operands are swapped.

Any repair must preserve legitimate ANY behavior for stable versions.

## Family 3: stable-open-gap

Count:

```text
3 unordered pairs
6 ordered false-positive rows
```

Representatives:

```text
>0.0.0   vs <0.0.1
>0.0.0   vs ^0.0.0
>0.0.1   vs ^0.0.1
```

node-semver reports `true` in both orders. Semverifier proves each pair
disjoint.

### Why comparator order is not enough

For the compact pair:

```text
>0.0.0
<0.0.1
```

the comparator endpoints are ordered, so `Comparator.intersects()` takes the
opposite-direction branch and returns `true`.

But there is no stable SemVer version strictly between consecutive stable
versions `0.0.0` and `0.0.1`.

Versions such as `0.0.1-alpha` lie in precedence order below `0.0.1`, but
default range matching does not automatically admit prereleases. Neither
comparator set contains a prerelease comparator licensing that tuple.

The caret forms expose the same discreteness more sharply:

```text
^0.0.0 -> >=0.0.0 <0.0.1-0
^0.0.1 -> >=0.0.1 <0.0.2-0
```

The source transformation is visible in `replaceCaret` in
`classes/range.js`.

### Current-source trace

`Comparator.intersects()` treats two opposite-direction comparators as
intersecting when the lower comparator's SemVer endpoint compares below the
upper endpoint.

That proves overlap in the dense ordering intuition used by the comparator
test, but it does not prove that an admissible SemVer value exists between the
bounds under range-matching rules.

This family is therefore not an ANY short-circuit issue.

### Upstream history

No issue or PR directly matching the `>0.0.0` versus `<0.0.1`
intersection reproduction was found in the current repository search.

Older issue #223 is conceptually related: maintainers identified cases where
plain SemVer ordering was insufficient for `intersects()` because prerelease
range semantics matter. It is not the same reproduction.

### Minimal repair question

A repair should not special-case adjacent patch numbers.

The semantic property needed is stronger: comparator-set intersection must
establish existence of at least one admissible SemVer value, not merely ordered
endpoint overlap.

## Family 4: prerelease-boundary-overlap

Count:

```text
8 unordered pairs
16 ordered false-positive rows
```

Representative:

```text
<1.2.3
>1.2.3-alpha.2
```

node-semver reports `true` in both orders. Semverifier proves the ranges
disjoint.

Other corpus members include caret, tilde, hyphen, conjunction, and union forms
whose only precedence-space overlap with `<1.2.3` lies among `1.2.3`
prereleases.

### Why the semantic intersection is empty

The possible precedence values between `1.2.3-alpha.2` and stable
`1.2.3` are prerelease versions of the `1.2.3` tuple.

The left range `<1.2.3` contains no prerelease comparator. Under node-semver's
documented default rule, it therefore does not admit those prereleases.

So comparator precedence intervals overlap, but the actual range-matching sets
do not.

### Current-source trace

Again, the opposite-direction comparator branch in
`Comparator.intersects()` can return `true` solely from endpoint ordering.

Actual `Range.test()`, however, calls `testSet`. For a prerelease candidate,
`testSet` scans the whole comparator set and requires a comparator with a
prerelease on the same major/minor/patch tuple.

The two operations therefore answer subtly different questions:

- comparator intersection: do the comparator precedence intervals overlap?
- range satisfaction: does a concrete version satisfy comparator ordering and
  prerelease-admission rules?

For this family, the first answer is yes and the second has no witness.

### Upstream history

Historical issue #254 documented inconsistency between exact-prerelease and
range forms caused by the interaction between `intersects()` and
`satisfies()`.

Closed, unmerged PR #884 documents the opposite-direction manifestation of the
same broad set-level prerelease problem: pairwise comparator decomposition can
lose sibling prerelease admission and produce false negatives.

The current family is not identical to #884. Here pairwise endpoint overlap
over-approximates the real range set and produces false positives.

No existing upstream report was found that enumerates this current family as a
complete false-positive class.

## What the four families say about the abstraction boundary

The 62 pairs do not require 62 explanations.

They expose two deeper abstraction mismatches.

### A. Special-case comparator control flow is not extensional

Families 1 and 2 depend on which special branch of
`Comparator.intersects()` executes first. In Family 2 that even makes
intersection non-commutative.

### B. Pairwise comparator overlap is not equivalent to range intersection

Families 3 and 4 survive without ANY. They show that endpoint overlap can
exist without any concrete version satisfying both ranges.

The missing information is different in each case:

- Family 3: SemVer values are discrete and prereleases are not automatically
  admitted;
- Family 4: prerelease admission belongs to the comparator set, not merely to
  endpoint precedence.

This is the same architectural reason Semverifier defines intersection
extensionally over `Range.satisfies` and proves the finite witness search
complete.

## Upstream-status boundary

This audit does not yet propose an upstream fix.

The safest next step is to validate one representative from each family against
a small set of candidate repairs and measure the complete 40,804-pair delta.

In particular, do not assume one code edit should repair all four families.
The ANY asymmetry and the pairwise-overlap abstraction may require different
changes.

Before any upstream submission, re-read the current node-semver contribution
policy and run its complete tests, lint, and coverage checks.

## CI checkpoint

The full-matrix harness now also partitions every unordered differential
false-positive pair.

CI requires the exact family counts:

```text
exact-prerelease-asymmetry      34
null-below-zero                 17
prerelease-boundary-overlap      8
stable-open-gap                  3
```

Any unclassified pair is a CI failure.

This turns the partition itself into a reproducible audit artifact rather than
a prose-only interpretation.
