# node-semver Full Intersection Matrix Audit

Date: 2026-09-19

## Scope

This audit compares Semverifier's proved range-intersection decision against
the current `npm/node-semver` `main` observed on 2026-09-19.

Pinned upstream target:

```text
npm/node-semver
6e05b7637396ac66522cff8731f07cfe0ef49a29
package version: 7.8.5
```

Semverifier baseline for this audit branch:

```text
shumoku88-bit/semverifier
fb8f067062daf3848e6840d04abb28d1102cd7d1
```

The upstream commit is pinned in CI. The audit does not follow a floating
branch.

## Method

The supported conformance corpus contains 202 range expressions.

Semverifier emits the complete ordered Cartesian product:

```text
202 x 202 = 40,804 ordered range pairs
```

For each pair, the Lean executable reports exactly one of:

```text
witness=<version>
disjoint
```

The result comes directly from `Range.findIntersectionWitness?`.

The relevant proved properties are:

- `Range.findIntersectionWitness?_sound`: every returned witness establishes
  semantic intersection;
- `Range.findIntersectionWitness?_complete_verified`: every semantic
  intersection yields a returned witness;
- `Range.findIntersectionWitness?_none_iff_not_intersects_verified`:
  `none` is exactly semantic disjointness.

The Node adapter then checks the same ordered pair with pinned node-semver
`Range.intersects()`.

For every Semverifier witness, node-semver's own `satisfies()` must accept
that exact version on both sides. A rejected concrete witness is a CI failure.

The matrix itself is checked to be a complete Cartesian product with no
duplicate ordered pairs.

## Checkpoint result

The complete matrix produced:

```text
40,804 ordered pairs
23,410 Semverifier intersections with concrete witnesses
17,394 Semverifier-proved disjoint pairs
```

Against pinned node-semver current main:

```text
4  ordered false-negative disagreements
90 ordered differential false-positive disagreements
62 unordered false-positive pairs
34 unordered pairs where node-semver intersects() is asymmetric
```

The complete disagreement set is checkpointed by:

```text
sha256:483d882f69ac5c2184fcec2e7873da7d5d0e6bbe5785371a53a89f03c1d90ee2
```

CI pins the counts and this fingerprint. A future semantic, corpus, or
upstream-target change must intentionally refresh the checkpoint.

## False-negative direction

The four ordered false negatives are the already-known prerelease/hyphen
case and syntax/order duplicates:

```text
1.2.3-alpha.2
=1.2.3-alpha.2
1.2.3-alpha.2 - 1.2.3
witness: 1.2.3-alpha.2
```

These are concrete contradictions: node-semver `satisfies()` accepts the
witness for both ranges while `Range.intersects()` returns `false`.

The minimized current-main reproduction and independent source trace remain in
[NODE_SEMVER_CURRENT_MAIN_AUDIT.md](NODE_SEMVER_CURRENT_MAIN_AUDIT.md).

## Differential false-positive direction

The 90 ordered rows in this direction have this shape:

```text
Semverifier: proved disjoint
node-semver Range.intersects(): true
```

They are stronger evidence than a bounded failure-to-find-a-witness test,
because Semverifier's `none` result is proved equivalent to disjointness in
its semantics.

However, this audit deliberately distinguishes two claims:

1. the cross-implementation disagreement is established;
2. calling every row a confirmed node-semver defect additionally relies on
   Semverifier and node-semver intending the same range-matching semantics for
   that syntax.

The project already has broad `satisfies()` differential conformance, and the
representative families below also align with node-semver's documented default
prerelease rule. Even so, each family should be traced before proposing an
upstream repair.

## Representative false-positive families

### 1. Null range versus wildcard / ANY forms

Examples include:

```text
<0.0.0    vs *
<0.0.0    vs x
<0.0.0    vs ""
<0.0.0    vs >=0
```

Under default prerelease handling, `<0.0.0` has no matching version.

This family overlaps historical node-semver issue #521, which was confirmed as
a bug and addressed by merged PR #538.

The current source still has an important ordering boundary in
`Comparator.intersects()`: the exact/ANY special cases at the start of the
method run before the later `<0.0.0` null-range guard. An ANY comparator can
therefore return `true` before the null guard is consulted.

The full matrix shows that residual shapes in this family remain on the pinned
current main.

### 2. Wildcard / broad stable range versus exact prerelease

Examples include:

```text
*              vs 1.2.3-alpha.2
x              vs 1.2.3-alpha.2
^*             vs 1.2.3-alpha.2
>=0.0.0        vs 1.2.3-alpha.2
```

Many of these are asymmetric in node-semver: one argument order returns
`true` and the reverse order returns `false`.

That is especially significant because node-semver's own range-intersection
fixture tests exercise both argument orders with the same expected result.

The source explains the asymmetry candidate: `Comparator.intersects()` has
different exact/ANY early-return paths depending on which comparator is
`this`. One direction can return `true` immediately for ANY, while the
reverse direction can construct a `Range` and invoke normal prerelease
filtering.

### 3. Open stable gaps

Compact examples include:

```text
>0.0.0    vs <0.0.1
>0.0.1    vs ^0.0.1
```

Comparator precedence alone suggests room between the bounds, but there is no
stable SemVer version between consecutive patch values.

Prerelease versions in that precedence gap do not automatically satisfy the
ranges: node-semver's documented default rule requires a comparator with a
prerelease tag on the same major/minor/patch tuple.

This is another place where comparator-order overlap can be a coarser relation
than actual range satisfiability.

### 4. Prerelease boundary versus stable upper bound

Examples include:

```text
<1.2.3    vs >1.2.3-alpha.2
<1.2.3    vs >=1.2.3-alpha.2
<1.2.3    vs ^1.2.3-beta.2
<1.2.3    vs 1.2.3-alpha.2 - 1.2.3
```

The only precedence-space overlap can lie among `1.2.3` prereleases.

But prerelease admission is a comparator-set property in node-semver's own
range-matching implementation. Treating comparator-pair precedence overlap as
range intersection can therefore over-approximate the true matching set.

This is the opposite-direction counterpart to the information-loss mechanism
already observed in the false-negative audit.

## Upstream context

Relevant existing upstream history includes:

- issue #223: `intersects()` prerelease false-positive behavior was confirmed
  as a bug historically;
- issue #254: prerelease inconsistency between exact and range forms;
- issue #521 / merged PR #538: `<0.0.0` intersection bugs around X-ranges;
- closed, unmerged PR #884: set-level prerelease admission lost by pairwise
  comparator intersection, producing false negatives;
- open PR #885: a separate false-negative bug caused by the
  `startsWith('<0.0.0')` guard.

This audit does not assume that those reports explain all 90 ordered
false-positive rows. They are comparison points, not substitutes for an
independent family-by-family trace.

## CI policy

The full-matrix audit now pins:

- corpus size;
- ordered pair count;
- Semverifier witness/disjoint counts;
- false-negative count;
- differential false-positive count;
- unordered false-positive count;
- node-semver asymmetry count;
- SHA-256 fingerprint of the complete disagreement set.

The pinned target is intentionally reproducible. A later node-semver commit
should be audited as a new target rather than silently replacing this
checkpoint.

## Next step

Do not implement an upstream repair yet.

The next task is to reduce the 62 unordered false-positive pairs into a small
set of semantic families and establish a minimal reproduction plus independent
source trace for each family.

For every family, check:

1. the smallest representative pair;
2. both argument orders;
3. node-semver's documented prerelease rules;
4. the exact `Range` / `Comparator` path that produces the result;
5. whether an existing upstream issue or PR already covers it.

Only after that partition is stable should repair candidates be compared.
