# Masterminds/semver Satisfaction Conformance Audit

Date: 2026-09-19

## Purpose

This audit asks a deliberately narrow question:

> Does Semverifier's existing supported range-satisfaction semantics agree with
> a second real-world SemVer implementation outside JavaScript?

The comparison target is Go's `Masterminds/semver`, pinned to current master:

- repository: `Masterminds/semver`
- commit: `dd2b995c61c39ddd668b23ac919b04d607be35ab`
- resolved Go module version:
  `v3.5.1-0.20260814205509-dd2b995c61c3`

This is an observation audit, not an assertion that either implementation is
wrong whenever the results differ.

## Method

The audit reuses Semverifier's existing deterministic satisfaction corpus:

- 202 range expressions;
- 384 candidate versions;
- 77,568 range/version judgments.

The same corpus already agrees completely with node-semver 7.8.5 for the
supported syntax milestone.

For each row, the Go adapter:

1. parses the range with `semver.NewConstraint`;
2. parses the candidate with `semver.StrictNewVersion`;
3. evaluates `Constraints.Check`;
4. compares the result with Semverifier;
5. separates stable-version and prerelease-version disagreement.

Parser incompatibility is recorded separately from semantic disagreement.

## Result

The first completed audit run produced:

| Observation | Count |
| --- | ---: |
| Corpus rows | 77,568 |
| Compared judgments | 76,800 |
| Constraint parse incompatibilities | 768 |
| Version parse errors | 0 |
| Semantic mismatches | 1,496 |
| Stable-version mismatches | 812 |
| Prerelease-version mismatches | 684 |
| Masterminds true / Semverifier false | 924 |
| Masterminds false / Semverifier true | 572 |

The 768 parser incompatibilities are exactly two surface forms, each evaluated
against all 384 candidate versions:

- `""`: 384 rows;
- `">=1.2.3 || "`: 384 rows.

These are parser-compatibility differences and are not included in the 1,496
semantic mismatches.

## Stable mismatch partition

All 812 stable-version mismatches are accounted for by seven range spellings,
with no remainder:

| Family | Range forms | Mismatches |
| --- | --- | ---: |
| caret wildcard | `^*`, `^x`, `^X` | 378 |
| zero tilde | `~0.0.0`, `~>0.0.0` | 240 |
| all-wildcard hyphen | `* - *` | 120 |
| open-ended wildcard hyphen | `1.2.3 - *` | 74 |
| **Total** | | **812** |

### Caret wildcard is especially notable

Semverifier and node-semver treat `^*`, `^x`, and `^X` as unconstrained
stable ranges.

At the pinned Masterminds commit, the source comment above
`constraintCaret` also says:

```text
^* --> (any)
```

and the public documentation says wildcard characters work with comparison
operators.

However, the differential audit observes, for example:

```text
range="^*" version="0.0.1" semverifier=true masterminds=false
```

The complete corpus gives 126 stable mismatches for each of `^*`, `^x`,
and `^X`.

This is stronger than a simple cross-library dialect difference because the
observed behavior appears inconsistent with Masterminds' own source comment.

The current implementation also exposes a concrete root-cause path:

1. parsing `^*` recognizes the wildcard major and rewrites its internal
   version to `0.0.0`;
2. that branch sets `dirty = true` but leaves both `minorDirty` and
   `patchDirty` false;
3. `constraintCaret` does not use the general `dirty` bit to implement its
   documented `^* --> (any)` case;
4. with major and minor both zero and neither narrower dirty bit set, execution
   falls through to the final patch-equality check.

That path explains the observed behavior: `^*` behaves effectively like an
exact `0.0.0` core for stable versions instead of the documented wildcard.
The same parser shape applies to `^x` and `^X`.

This is therefore a focused implementation/documentation inconsistency
candidate. It should still be reproduced with a minimal upstream-side test
before being reported as a confirmed bug.

### Zero tilde is an explicit semantic difference

The current Masterminds implementation intentionally special-cases
`~0.0.0` as equivalent to `>=0.0.0`, accepting every later stable version.

Semverifier follows node-semver-style tilde semantics, under which
`~0.0.0` is bounded below the next minor line.

The 120 mismatches for `~0.0.0` and another 120 for `~>0.0.0` therefore
represent a documented implementation-policy difference, not enough evidence
for an upstream defect by itself.

### Wildcard hyphen forms differ

The remaining 194 stable mismatches are exactly:

- `* - *`: 120;
- `1.2.3 - *`: 74.

Masterminds rewrites hyphen ranges through its own constraint parser, while
Semverifier models the node-semver whole-branch hyphen semantics used by its
supported syntax milestone.

These forms should be treated as dialect differences until Masterminds'
intended wildcard-hyphen contract is established.

## Prerelease mismatch partition

All 684 prerelease-version mismatches are accounted for by the following seven
range forms, again with no remainder:

| Range | Mismatches |
| --- | ---: |
| `>1.2.3-alpha.2` | 144 |
| `>1.2.3-alpha.2 || >=3.0.0` | 144 |
| `>=1.2.3-alpha.2` | 144 |
| `<1.2.3-alpha.2` | 108 |
| `<=1.2.3-alpha.2` | 108 |
| `>1.2.3-alpha.2 <2.0.0` | 20 |
| `^1.2.3-beta.2` | 16 |
| **Total** | **684** |

This family has a direct semantic explanation.

Masterminds records whether an AND-group contains any prerelease comparator and
passes that group-level permission into its primitive constraint checks.
Consequently a range such as:

```text
>1.2.3-alpha.2
```

can admit later prereleases such as:

```text
1.3.0-alpha
```

Semverifier follows node-semver's default prerelease admission rule, where a
prerelease candidate must be admitted by an explicit comparator on the same
major/minor/patch tuple.

Therefore these 684 rows are a real semantic difference between the libraries,
not evidence that the proved Semverifier search is inconsistent with its own
model.

## What this experiment establishes

This audit does **not** establish that Semverifier is a universal SemVer oracle.

It establishes something narrower and useful:

1. the existing oracle can be applied unchanged to a second implementation in
   another programming language;
2. disagreements can be localized to a small set of semantic families rather
   than appearing as undiagnosed noise;
3. the audit distinguishes parser surface differences, intentional semantic
   dialect differences, and candidate implementation/documentation
   inconsistencies;
4. the caret-wildcard family provides a concrete candidate for a focused
   upstream investigation.

This is exactly the role intended for Semverifier: a small semantic measuring
instrument, not a replacement package manager.

The CI adapter pins this exact checkpoint. The known disagreements themselves
do not fail CI, but any drift in corpus size, parser-incompatibility families,
mismatch counts, mismatch directions, or the complete per-range mismatch
partition does. This turns the audit into a reproducible historical baseline
rather than a log-only experiment.

## Upstream context

Masterminds has received repeated requests for range-to-range operations:

- PR #169, opened in 2022, proposes `Constraints.Intersects` and remains open;
- issue #256 asks for constraint subset comparison;
- PR #274 proposed `Intersection` and `IsSubset`, but was closed unmerged on
  2026-09-13.

That history makes Masterminds a relevant validation target, but none of those
artifacts should be treated as evidence that Semverifier's semantics are the
intended Masterminds semantics.

## Next narrow step

Do not report the 1,496 disagreements upstream as one issue.

The next useful step is to isolate the `^*` / `^x` / `^X` family because
it is the only observed stable family that already has an apparent
implementation-versus-own-documentation contradiction.

A good next checkpoint would:

1. reproduce `^*` with a tiny direct Masterminds test independent of the
   Semverifier corpus;
2. trace how wildcard parsing sets `dirty`, `minorDirty`, and
   `patchDirty`;
3. check existing tests and historical issues for intended behavior;
4. only then decide whether an upstream issue or PR comment would be useful.

Do not mix the prerelease-policy or wildcard-hyphen dialect differences into
that report.
