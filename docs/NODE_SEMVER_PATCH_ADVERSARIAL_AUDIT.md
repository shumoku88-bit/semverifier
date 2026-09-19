# node-semver Patch Adversarial Audit

Date: 2026-09-19

## Plain-language summary

Semverifier previously found 94 disagreements between its proved default range-
intersection semantics and pinned node-semver current main:

- 4 false negatives;
- 90 false positives;
- 34 asymmetric unordered pairs.

A local node-semver patch replaced pairwise comparator-overlap reasoning with a
finite boundary-candidate witness search. The patch then asks node-semver's own
`testSet` whether a concrete candidate satisfies both comparator sets.

This follow-up audit tried to break that patch.

No new semantic counterexample was found in the generated tests described
below. The patch still agrees with all 40,804 Semverifier corpus pairs and
remains symmetric across the additional generated cases.

The remaining concern is not a known correctness counterexample. It is
performance: the witness-based implementation can be substantially slower than
the current pairwise implementation on large disjoint unions.

This document records evidence. It is not a claim that the JavaScript patch is
formally proved correct for every node-semver option or syntax.

## Environment

Semverifier checkpoint:

```text
shumoku88-bit/semverifier
6ee9fceec77c784c5270f353e20b5e89c841795c
```

Pinned node-semver target:

```text
npm/node-semver
6e05b7637396ac66522cff8731f07cfe0ef49a29
package version 7.8.5
```

The node-semver patch was tested only on a local branch:

```text
audit/range-intersects-proved-boundary
```

No upstream pull request was opened as part of this audit.

## Patch shape under audit

The local patch changes `Range.prototype.intersects()` from pairwise
`Comparator.intersects()` reasoning to range-level witness search.

At a high level:

1. collect finitely many SemVer candidates from comparator boundaries;
2. include stable-core, next-patch, prerelease-floor, exact-boundary, and
   prerelease-successor candidates as appropriate;
3. when `includePrerelease` is active, include additional prerelease floors;
4. test each candidate with node-semver's existing `testSet`;
5. report intersection only when one concrete candidate satisfies both
   comparator sets.

The candidate shape is derived from the same boundary structure used by
Semverifier's proved finite intersection search.

The patch removes the old internal `isSatisfiable` helper from the
range-intersection path.

## Previously completed source-level validation

Before this adversarial follow-up, the local patch had already passed:

- all 51 node-semver test suites;
- 9,444 assertions with 0 failures;
- 100% line coverage;
- 100% branch coverage;
- 100% statement coverage;
- 100% function coverage;
- ESLint with 0 errors and 0 warnings;
- template-oss-check;
- the complete Semverifier 202 x 202 ordered-pair matrix.

On that 40,804-pair matrix, the patched node-semver result was:

```text
false negatives: 0
false positives: 0
asymmetric unordered pairs: 0
unexpected changes: 0
```

Exactly the 94 baseline disagreements changed:

```text
4  false -> true
90 true  -> false
```

The other 40,710 ordered pairs retained their previous node-semver result.

## Generated adversarial audit

The follow-up audit generated 14,035 valid Range pairs containing mixtures of:

- stable and prerelease boundaries;
- strict and inclusive comparisons;
- wildcards;
- conjunctions;
- unions;
- hyphen ranges;
- caret ranges;
- tilde ranges.

The same generated pairs were exercised under both default prerelease handling
and `includePrerelease: true`.

Observed violations:

```text
symmetry violations: 0
sampled false negatives: 0
sampled false positives: 0
default-true => includePrerelease-true monotonicity violations: 0
```

For every generated case where the patched implementation returned true, the
audit found a concrete candidate accepted by both sides.

### Important limitation

This is generated testing, not an exhaustive proof over node-semver's complete
input language.

The Semverifier completeness proof applies to Semverifier's supported default
range semantics. The JavaScript translation, `includePrerelease`, and
node-semver-only parser conveniences remain empirical validation layers.

## includePrerelease audit

The generated audit explicitly covered `includePrerelease: true`.

Important boundary examples included:

```text
<0.0.0  intersect  *          => true
witness: 0.0.0-0

>1.0.0  intersect  <1.0.1     => true
witness: 1.0.1-0

<0.0.0-0 intersect <0.1.0     => false
```

This required the patched candidate generator to include prerelease floors that
do not belong to the default Semverifier candidate interpretation.

The audit also checked option propagation through direct Range-object
intersection rather than only the public string API.

No generated `includePrerelease` counterexample was found.

## loose-mode audit

Strict forms were mechanically transformed into loose forms including examples
such as:

- leading `v`;
- `=v`;
- leading zeroes;
- whitespace variations.

Generated loose audit:

```text
pairs: 6,400
symmetry violations: 0
strict-normalization mismatches: 0
```

Candidate generation uses normalized numeric SemVer components, then reconstructs
strict candidate strings. No loose-only semantic discrepancy was found in this
audit.

## Symmetry audit

The patched implementation was symmetric across all observed sets:

```text
Semverifier corpus:          40,804 ordered pairs, 0 asymmetric pairs
generated range audit:       14,035 pairs,         0 asymmetric pairs
generated loose audit:        6,400 pairs,         0 asymmetric pairs
```

This removes the 34 asymmetric unordered pairs observed in the pinned baseline.

## Adversarial performance results

The patch is slower than the current implementation because it allocates a
candidate set and validates concrete SemVer values through `testSet`.

Measured examples:

| scenario | baseline | patched | slowdown | patched latency |
| --- | ---: | ---: | ---: | ---: |
| early match | 803,758 ops/s | 140,799 ops/s | 5.7x | about 7.1 us |
| small disjoint | 1,021,443 ops/s | 171,022 ops/s | 6.0x | about 5.8 us |
| dense conjunction | 61,803 ops/s | 20,591 ops/s | 3.0x | about 48.5 us |
| 20 x 20 disjoint union | 4,340 ops/s | 255 ops/s | 17.0x | about 3.9 ms |
| 20-branch union, late match | 58,680 ops/s | 5,127 ops/s | 11.4x | about 195 us |

The large disjoint-union case is the clearest current trade-off.

No claim should be made that this slowdown is automatically acceptable to
node-semver maintainers. It is an upstream design question.

## Candidate count and complexity

For one comparator-set pair, let

```text
K = |set1| + |set2|
```

The audit estimated at most:

```text
2 + 5K
```

candidate values before deduplication.

Each candidate is checked against both comparator sets, giving a worst-case
set-pair cost of approximately:

```text
O(K^2)
```

If the two ranges contain `S1` and `S2` disjunctive comparator sets, the
overall worst-case shape is:

```text
O(S1 * S2 * K^2)
```

This is polynomial, not exponential, but the allocation and parsing constants
are materially larger than the baseline implementation.

## Safe optimization experiments

The audit explored optimizations that do not intentionally change semantics:

- reuse global `0.0.0` and `0.0.0-0` SemVer objects;
- reuse already-parsed `comp.semver` where possible;
- deduplicate candidates before instantiating duplicate SemVer objects.

Observed improvement:

```text
small disjoint: about 1.29x faster
massive union:  about 1.12x faster
```

These are useful but do not erase the large-union slowdown.

For upstream discussion, the simpler candidate implementation is currently
easier to compare with the Semverifier proof structure. Optimization can be
considered separately if maintainers accept the semantic direction.

## Minimal upstream regression set

The audit reduced the larger local regression suite to eight representative
cases.

Five default-semantics fixtures:

```text
1.2.3-alpha.2  vs  1.2.3-alpha.2 - 1.2.3  => true
<0.0.0         vs  *                        => false
*               vs  1.2.3-alpha.2            => false
>0.0.0          vs  <0.0.1                   => false
<1.2.3          vs  >1.2.3-alpha.2           => false
```

Three `includePrerelease: true` cases:

```text
<0.0.0     vs *        => true
>0.0.0     vs <0.0.1   => true
<0.0.0-0   vs <0.1.0   => false
```

The existing fixture loops multiply these representatives across argument
order and related invocation forms.

## Relationship to existing upstream history

The patch overlaps existing node-semver reports but is broader than any one of
them.

### PR #884

Closed, unmerged.

It concerns the prerelease/hyphen false-negative family also observed by
Semverifier.

The current experiment additionally covers:

- the 90 ordered false positives;
- the 34 asymmetric unordered pairs;
- the null-below-zero family;
- stable open gaps;
- prerelease-boundary overlap.

### PR #885

Open at the time of this checkpoint.

It concerns a `<0.0.0-<prerelease>` comparator-intersection guard.

The witness-based patch operates at Range level and does not depend on
`Comparator.intersects()` being the final semantic oracle.

### Historical issue #521 / PR #538

These addressed part of the `<0.0.0` / X-range intersection problem.

The current matrix shows remaining null-range behavior through additional
ANY-normalizing forms.

### Historical issues #223 and #254

These are relevant background for prerelease/range intersection inconsistency,
but they do not substitute for the current source trace or the complete matrix
audit.

## Evidence status

The current evidence supports the following statements:

### Strongly established for this checkpoint

- the pinned baseline disagrees with Semverifier on 94 ordered corpus pairs;
- those disagreements reduce to documented semantic families;
- the local witness-based patch changes exactly those 94 pairs in the complete
  Semverifier corpus;
- the patch passes the current node-semver test, lint, coverage, and
  template-oss checks;
- no new counterexample was found in the additional generated audits;
- symmetry is restored throughout the observed data;
- the patch has a measurable performance cost, especially for large unions.

### Not established as a formal proof

- correctness for every possible node-semver input;
- correctness of every node-semver-only parser convenience;
- formal completeness for `includePrerelease: true`;
- that the measured performance trade-off is acceptable upstream;
- that node-semver maintainers will prefer this architectural repair.

## Next step

The next step is not another Semverifier semantic feature.

Prepare a concise upstream node-semver issue that:

1. gives a minimal false-negative reproduction;
2. gives one representative false-positive/asymmetry reproduction;
3. explains that the failures share a Range-level semantic cause;
4. notes the complete 40,804-pair independent audit;
5. mentions the local witness-based prototype and its validation;
6. discloses the performance trade-off clearly;
7. links existing PR #884 and PR #885 rather than competing with them silently;
8. asks maintainers whether a range-level witness-based repair is a welcome
   direction before opening a large implementation PR.

Do not open the upstream pull request until that discussion establishes the
preferred direction.
