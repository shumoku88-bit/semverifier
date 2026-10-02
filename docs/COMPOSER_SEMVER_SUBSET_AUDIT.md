# Composer/semver Subset Audit

Date: 2026-10-02

## Purpose

This audit compares Composer/semver's public
`Intervals::isSubsetOf()` API with Semverifier's proved subset decision on the
same empirically discovered shared semantic surface used by the earlier
Composer intersection audit.

Target:

- repository: `composer/semver`
- commit: `4221b9ec7fdd42b5b3d939509d55d97b511c52df`

No assumption is made that Composer implements npm/node-semver range semantics.

## Shared semantic surface

The existing 202 × 384 Semverifier satisfaction corpus is first evaluated by
Composer.

Only ranges that agree on all 384 versions, including prereleases, are admitted
to the subset comparison.

The resulting set is unchanged from the intersection audit:

- 27 full-corpus-compatible ranges;
- fingerprint
  `db380f28b225a2edd0dc9d877310cb914c3d4f45a051d4b7cc65e9a922d3f3df`.

Those 27 ranges produce 729 ordered subset pairs.

## Result

| Observation | Count |
| --- | ---: |
| Complete Semverifier matrix rows | 40,804 |
| Directly comparable pairs | 729 |
| Subset disagreements | 27 |
| Semverifier subset / Composer not-subset | 27 |
| Semverifier not-subset / Composer subset | 0 |
| Witness-confirmed Composer contradictions | 0 |
| Disagreements with candidate `<0.0.0` | 27 |
| All other disagreement families | 0 |

Every disagreement has the same candidate range:

```text
<0.0.0
```

For every one of the 27 compatible containing ranges, Semverifier reports that
this candidate is a subset while Composer reports that it is not.

After removing this one candidate range, the remaining 26 × 26 = **676**
ordered pairs agree exactly.

## Minimal Composer-only reproduction

The important observation does not depend on Semverifier.

Composer parses `<0.0.0` as an ordinary
`Composer\Semver\Constraint\Constraint` rendered as:

```text
< 0.0.0.0-dev
```

The pinned probe observes:

```text
Intervals::haveIntersections(x, x) = false
Intervals::isSubsetOf(x, x)        = false
```

So Composer's interval machinery sees no version in the self-intersection, but
its subset API also says the same constraint is not a subset of itself.

The interval representation explains the boundary:

```text
Intervals::get(x)
  numeric count = 1
  start = >= 0.0.0.0-dev
  end   = <  0.0.0.0-dev
```

That is an empty numeric interval represented as one interval object.

By contrast, the existing Composer test suite includes `< dev-foo` with the
comment that the invalid range “matches nothing so is a subset of any other.”
The probe confirms that this other empty constraint has zero numeric intervals
and behaves as expected:

```text
haveIntersections(y, y) = false
isSubsetOf(y, y)        = true
isSubsetOf(y, 0.0.0)    = true
```

This rules out a simple interpretation that Composer intentionally defines all
empty constraints as non-subsets.

## Likely mechanism

`Intervals::generateSingleConstraintIntervals()` handles every numeric
`<` / `<=` primitive by directly constructing an interval from
`Interval::fromZero()` to the comparator. It does not normalize an impossible
single interval there.

For `<0.0.0`, that produces:

```text
>= 0.0.0.0-dev  ...  < 0.0.0.0-dev
```

When constraints are combined through the `MultiConstraint` path,
`generateIntervals()` explicitly filters equal-bound impossible intervals
such as `>= x ... < x`.

`isSubsetOf()` compares:

1. intervals for `candidate ∩ constraint`, which take the multi-constraint
   path and eliminate the impossible interval;
2. intervals for the candidate alone, which retain the one impossible
   single-constraint interval.

The differing interval counts cause `isSubsetOf()` to return false.

This is a source-level explanation of the observation, not yet an upstream
patch proposal.

## Existing intent and history

Composer's tests already establish that at least some constraints matching
nothing are intended to be subsets of ordinary constraints. Separately,
`MatchNoneConstraint` has explicit special-case behavior and is intentionally
not treated as a normal subset except when the right side is
`MatchAllConstraint`.

The `<0.0.0` case is not a `MatchNoneConstraint`; it is an ordinary
`Constraint` whose numeric interval is empty.

A GitHub search on 2026-10-02 found no existing Composer issue or pull request
specifically mentioning `<0.0.0` or this self-subset behavior.

## Interpretation

This audit found one narrow discrepancy family rather than a general failure of
Composer subset semantics.

The other 676 directly comparable ordered pairs agree with Semverifier's proved
subset oracle.

The `<0.0.0` result is a credible upstream bug candidate because it can be
stated entirely in Composer's own APIs as a self-subset/reflexivity problem and
is consistent with the existing test intent for another empty constraint.

No upstream issue or comment is created by this audit PR. A separate, minimal
upstream report should use the Composer-only reproduction and avoid claiming
that Semverifier defines Composer's semantics.
