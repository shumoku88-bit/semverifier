# node-semver Intersection Repair Strategy Experiment

Date: 2026-09-19

## Scope

This experiment compares candidate `Range.intersects()` repair strategies
against the complete Semverifier 202 x 202 ordered range matrix.

Pinned upstream target:

```text
npm/node-semver
6e05b7637396ac66522cff8731f07cfe0ef49a29
package version: 7.8.5
```

Semverifier baseline:

```text
shumoku88-bit/semverifier
9edb89a22b80ccc1a5e2cd1074d2cde5e141f363
```

The experiment does not patch node-semver source. Each strategy is modeled
outside the package and evaluated against the same 40,804 ordered pairs.

The Lean semantic kernel is unchanged.

## Baseline

Pinned node-semver current main has:

```text
4  false negatives
90 false positives
34 asymmetric unordered pairs
94 total disagreements
```

The disagreement families are documented in
[NODE_SEMVER_FALSE_POSITIVE_FAMILIES.md](NODE_SEMVER_FALSE_POSITIVE_FAMILIES.md).

## Strategy results

| strategy | false negatives | false positives | asymmetric pairs | baseline errors repaired | new errors introduced |
| --- | ---: | ---: | ---: | ---: | ---: |
| baseline | 4 | 90 | 34 | 0 | 0 |
| symmetric-pairwise | 4 | 56 | 0 | 34 | 0 |
| symmetric-pairwise + nonempty sets | 4 | 22 | 0 | 68 | 0 |
| set-min-witness | 1292 | 0 | 0 | 94 | 1292 |
| combined-set-min-witness | 1292 | 0 | 0 | 94 | 1292 |
| boundary-witness | 0 | 0 | 0 | 94 | 0 |
| proved-boundary-shape | 0 | 0 | 0 | 94 | 0 |

All counts are pinned in CI.

## Strategy 1: symmetric pairwise

The current node-semver algorithm checks:

```text
leftComparator.intersects(rightComparator)
```

The first repair model requires both:

```text
leftComparator.intersects(rightComparator)
rightComparator.intersects(leftComparator)
```

Result:

```text
34 baseline errors repaired
0 new errors
0 asymmetric unordered pairs
```

This exactly removes the 34-member `exact-prerelease-asymmetry` family.

That is useful evidence that this family is caused by directional special-case
control flow rather than by a broader disagreement in range semantics.

It does not address the remaining symmetric false positives or the four false
negatives.

## Strategy 2: symmetric pairwise plus nonempty comparator sets

The second model keeps symmetric cross-comparator checking and additionally
requires each conjunctive comparator set to have an actual node-semver
`minVersion`.

Result:

```text
68 baseline errors repaired
0 new errors
4 false negatives remain
22 false positives remain
```

The 22 residual false positives are exactly:

```text
stable-open-gap                 3 unordered / 6 ordered
prerelease-boundary-overlap     8 unordered / 16 ordered
```

So this strategy removes the complete `null-below-zero` and
`exact-prerelease-asymmetry` families without touching already-correct corpus
pairs.

That clean separation is informative even though this is not the final repair
shape.

## Rejected strategies: minVersion as the intersection oracle

Two variants were tested:

1. take the minimum of each comparator set independently and cross-test them;
2. combine the two comparator sets, ask `minVersion` for one candidate, then
   test that candidate against the original sets.

Both produced exactly the same result:

```text
0 false positives
1292 false negatives
1292 previously-correct pairs broken
```

The first counterexamples show the central failure mode.

For example:

```text
>0.0.0
>1.2.3-alpha.2
```

Semverifier returns the valid common witness:

```text
1.2.3
```

A single minimum-version candidate is not a complete intersection candidate
set. The overlap may begin at a stable release projected from a prerelease
boundary rather than at the one minimum selected by the helper.

This experiment therefore rejects `minVersion` as the foundation of an
intersection repair.

That rejection is also prudent because node-semver's `minVersion` has
separate known edge cases and active upstream work. Intersection should not
inherit unrelated uncertainty from another derived operation.

## Strategy 3: boundary witness search

The boundary-witness strategy does not ask whether comparator intervals merely
look overlapping.

Instead it builds a finite candidate pool from comparator boundaries and then
requires a concrete candidate to satisfy both original comparator sets.

The first candidate shape used:

- `0.0.0-0`;
- `0.0.0`;
- every comparator boundary;
- the stable release at the same core for prerelease boundaries;
- the discrete successor of strict lower bounds.

For a stable strict lower bound, the successor advances one patch.

For a prerelease strict lower bound, the successor appends numeric zero.

After adding the stable projection of prerelease boundaries, the result was:

```text
0 false negatives
0 false positives
0 asymmetric pairs
94 baseline errors repaired
0 new errors
```

The baseline delta is exactly:

```text
4  false -> true
90 true  -> false
```

No other corpus pair changes.

## Strategy 4: proved boundary shape

The final model mirrors the shape of Semverifier's already-proved finite
candidate pool more directly.

For every primitive comparator boundary, Semverifier's
`Range.boundaryCandidates` contributes:

For a stable bound:

```text
stable release at the bound core
next stable patch
```

For a prerelease bound:

```text
stable release at the bound core
next stable patch
prerelease floor at that core (-0)
the boundary itself, with build metadata ignored
the strict prerelease successor obtained by appending .0
```

The range pair also contributes the global minimum stable version `0.0.0`.

Semverifier then searches that finite pool and accepts only a candidate that
satisfies both ranges.

The Lean development proves the candidate pool globally complete for
Semverifier's supported range semantics.

The JavaScript experiment translates that candidate *shape* into node-semver
objects and still uses node-semver's own `Range.test()` for final acceptance.

Result:

```text
0 false negatives
0 false positives
0 asymmetric pairs
94 baseline errors repaired
0 new errors
```

on the complete 40,804-pair corpus.

## Why this result is stronger than corpus fitting

The `proved-boundary-shape` strategy was not obtained by enumerating the 94
known disagreements and hard-coding their cases.

Its candidate categories come from the Semverifier construction whose
completeness theorem was developed independently of node-semver's observed
disagreements.

The experiment therefore has two layers of evidence:

1. the candidate construction has a Lean completeness proof for Semverifier's
   semantics;
2. the translated JavaScript strategy agrees with the complete current
   Semverifier corpus while using node-semver's own `Range.test()` as the
   acceptance test.

This is not yet a proof of a node-semver patch. The bridge still depends on
the two implementations agreeing on the intended semantics for the supported
syntax.

## Important scope boundary

The current comparison is deliberately limited to the shared default semantics.

It does not yet validate a source-level repair for:

- `includePrerelease: true`;
- `loose: true`;
- parser conveniences that Semverifier intentionally does not model;
- performance or allocation behavior;
- arbitrary node-semver ranges outside the current Semverifier-supported
  syntax.

Those are required validation dimensions before an upstream repair can be
considered ready.

## Candidate direction

The experiment favors a witness-producing range-level algorithm over additional
special cases in `Comparator.intersects()`.

The key property is:

```text
Range intersection is true only when a concrete SemVer candidate satisfies
both original comparator sets.
```

This preserves set-level prerelease admission rather than attempting to infer
it from independent comparator pairs.

The `proved-boundary-shape` candidate pool is the strongest current model
because it has both zero corpus regressions and a direct correspondence to the
Lean completeness construction.

## Next step

Do not submit an upstream PR yet.

The next phase should turn the successful strategy into a temporary patch of
the pinned node-semver source and validate it as an actual implementation:

1. patch `classes/range.js` rather than only modeling the algorithm externally;
2. run node-semver's complete test suite, lint, and coverage;
3. rerun the Semverifier 40,804-pair matrix against the patched package;
4. add targeted tests for all four disagreement families;
5. separately test `includePrerelease` and `loose` behavior;
6. measure runtime impact of boundary-candidate search;
7. compare a minimal source patch with any simpler repair that preserves the
   same semantics.

Only after those checks should the project decide whether an upstream report or
PR is warranted.
