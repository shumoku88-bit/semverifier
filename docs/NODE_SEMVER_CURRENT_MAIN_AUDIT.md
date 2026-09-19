# node-semver Current-Main Intersection Audit

Date: 2026-09-19

## Scope

This audit validates Semverifier's proved range-intersection oracle against the
current `npm/node-semver` `main` observed on 2026-09-19.

Pinned upstream target:

```text
npm/node-semver
6e05b7637396ac66522cff8731f07cfe0ef49a29
```

Semverifier baseline:

```text
shumoku88-bit/semverifier
7922b1c33344e11cc0f54a31df4683cdbbf6de4b
```

The upstream commit is pinned in CI rather than following a floating branch, so
this observation remains reproducible if node-semver changes later.

## Result

The previously documented prerelease intersection false negative still
reproduces on the pinned current upstream `main`.

The audit also reduces it to smaller forms.

### Compact reproduction

Left range:

```text
1.0.0-0
```

Right range:

```text
1.0.0-0 - 1.0.0
```

Semverifier returns the concrete witness:

```text
1.0.0-0
```

The CI audit requires all of the following:

```text
node-semver satisfies("1.0.0-0", "1.0.0-0")                = true
node-semver satisfies("1.0.0-0", "1.0.0-0 - 1.0.0")      = true
Range("1.0.0-0").intersects(Range("1.0.0-0 - 1.0.0"))     = false
Range("1.0.0-0 - 1.0.0").intersects(Range("1.0.0-0"))     = false
```

A text-prerelease form is also required to reproduce:

```text
1.0.0-a
1.0.0-a - 1.0.0
witness: 1.0.0-a
```

The original case remains in the audit as well:

```text
1.2.3-alpha.2
1.2.3-alpha.2 - 1.2.3
witness: 1.2.3-alpha.2
```

All three cases are checked in both argument orders.

## Independent source trace

The root cause was traced directly from the pinned upstream source before
comparing the result with existing upstream proposals.

### 1. Range intersection is reduced to pairwise comparator intersection

In `classes/range.js:173-193`, `Range.intersects()` considers two comparator
sets intersecting only when every comparator on one side reports intersection
with every comparator on the other side.

The helper `isSatisfiable` in `classes/range.js:245-258` is also expressed
through pairwise `Comparator.intersects()` checks.

### 2. Prerelease admission is a comparator-set property

Actual range satisfaction uses `testSet` in
`classes/range.js:543-576`.

For a prerelease candidate, `testSet` scans the whole comparator set. A
prerelease is admitted when some comparator in that set has a prerelease with
the same major/minor/patch tuple.

That means prerelease admission is not, in general, a property of each
comparator considered independently.

### 3. Exact-comparator intersection discards sibling context

In `classes/comparator.js:84-93`, an exact comparator checks intersection with
another comparator by constructing a new one-comparator `Range` and calling
`test` on it.

For the compact reproduction, the hyphen range desugars to the conjunction:

```text
>=1.0.0-0 <=1.0.0
```

As a full comparator set, that range admits the witness `1.0.0-0`: the lower
bound carries the required prerelease tuple.

But the pairwise intersection check eventually isolates the upper bound:

```text
<=1.0.0
```

The isolated one-comparator range no longer contains the sibling
`>=1.0.0-0`, so its prerelease-admission context disappears. The exact
prerelease comparator therefore reports no intersection with that upper bound,
and the surrounding `every(...)` causes the complete range intersection to
return false.

This is a semantic information-loss problem at the comparator-set to
comparator-pair boundary.

## Relation to upstream work

After the independent trace, the result was compared with npm/node-semver
PR #884. That PR described the same broad prerelease/set-decomposition bug
family, but it was closed unmerged on 2026-07-11.

PR #885 is still open as of this audit, but concerns a separate
`<0.0.0-<prerelease>` null-set guard problem in `Comparator.intersects`.
The compact reproduction above deliberately uses the `1.0.0` tuple so that
the zero-tuple special case does not confound this audit.

## Semverifier proof boundary

The CLI used by this audit delegates directly to
`Range.findIntersectionWitness?`.

The relevant proved properties are:

- `Range.findIntersectionWitness?_sound`: any returned candidate establishes
  semantic intersection;
- `Range.findIntersectionWitness?_complete_verified`: every semantic
  intersection yields a returned witness;
- `Range.findIntersectionWitness?_none_iff_not_intersects_verified`:
  returning `none` is exactly semantic disjointness.

No node-semver behavior is encoded into the Lean kernel.

## CI evidence

PR #61 adds two current-main checks after the existing released-version
conformance checks:

1. rerun the full concrete Semverifier witness probe against the pinned
   node-semver current-main commit;
2. require the known and minimized symmetric false negatives above.

The audit was introduced without an upstream repair. The next task is to extend
the differential workflow from witness-bearing intersections to all ordered
range pairs, including Semverifier-proved disjoint pairs, so false positives can
be detected as well as false negatives.
