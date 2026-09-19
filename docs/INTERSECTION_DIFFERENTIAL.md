# Intersection Differential Checkpoint

Date: 2026-09-18.

This checkpoint records the first witness-backed differential probe for range
intersection.

## Method

Semverifier does not yet treat failure to find a witness as proof that two
ranges are disjoint.

The probe therefore uses only the sound direction:

1. Semverifier searches for a concrete version accepted by both ranges.
2. If a witness is found, node-semver 7.8.5 must also accept that exact version
   with both ranges.
3. Only then is node-semver's `Range.intersects()` result checked.
4. The check is performed in both argument orders.

This makes every reported contradiction witness-backed and independent of
Semverifier search completeness.

## Checkpoint result

The 202 supported range expressions produce 40,804 ordered pairs.

Semverifier found concrete witnesses for 23,410 of those pairs.

All 23,410 witnesses were accepted by node-semver's own `satisfies()` for
both ranges.

Four ordered-pair contradictions were then observed in
`Range.intersects()`. They collapse to one semantic case plus syntax/order
duplicates:

```text
left:    1.2.3-alpha.2
right:   1.2.3-alpha.2 - 1.2.3
witness: 1.2.3-alpha.2

satisfies(witness, left)  = true
satisfies(witness, right) = true
left.intersects(right)    = false
right.intersects(left)    = false
```

The same result occurs when the exact left range is written explicitly as
`=1.2.3-alpha.2`.

## Root cause

The contradiction is caused by decomposing comparator sets into independent
comparator-pair intersection checks.

The hyphen range lowers to a set containing:

```text
>=1.2.3-alpha.2
<=1.2.3
```

The lower comparator admits prereleases on the `1.2.3` core for the whole
set. But when the exact prerelease is checked against `<=1.2.3` in isolation,
that sibling admission information is lost.

This is precisely why Semverifier defines range algebra extensionally over
`Range.satisfies` rather than defining intersection by pairwise comparator
convention.

## Upstream status

npm/node-semver PR #884 independently reported the same bug family and the same
root cause:

https://github.com/npm/node-semver/pull/884

That PR was closed by its author on 2026-07-11 without merge, review, or
discussion. As of this checkpoint, node-semver main still uses the affected
pairwise comparator-set intersection structure.

A separate open PR #885 addresses a different `intersects()` false-negative
around `<0.0.0-<prerelease>` comparators.

## CI policy

The four exact checkpoint contradictions are tracked as known upstream
divergences. They are reported but do not fail Semverifier CI.

Any additional witness-backed contradiction remains a CI failure.

If node-semver fixes the known case, the warning naturally disappears without
changing Semverifier semantics.


## Bounded candidate-coverage audit

Before the global completeness proof was closed, CI also falsified the finite
boundary candidate pool against the existing bounded version corpus.

For all 40,804 ordered range pairs:

- 23,410 already produce a sound concrete witness;
- the remaining 17,394 `none` results are exhaustively checked against all
  384 corpus versions;
- no bounded-universe intersection witness is missed by the boundary candidate
  search.

This audit is now historical evidence rather than the completeness argument.
Global candidate-pool completeness is proved in Lean, culminating in
`Range.intersectionCandidatesComplete`,
`Range.findIntersectionWitness?_complete_verified`, and
`Range.findIntersectionWitness?_none_iff_not_intersects_verified`.

The verified search is now exposed through the public CLI, and the differential
workflow has advanced to a complete 202 x 202 ordered range matrix against a
pinned node-semver current-main commit. See
[NODE_SEMVER_FULL_INTERSECTION_AUDIT.md](NODE_SEMVER_FULL_INTERSECTION_AUDIT.md)
and [NEXT.md](NEXT.md).
