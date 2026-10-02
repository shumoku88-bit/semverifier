# Verified Subset Counterexample Search

Date: 2026-10-02

## Purpose

Semverifier already defined semantic range subset extensionally:

```text
SubsetOf sub dom :=
  every version accepted by sub is accepted by dom
```

This checkpoint turns that specification into an executable decision procedure
without defining subset by implementation convention.

The practical motivation is external: mature SemVer libraries such as
Composer/semver expose subset APIs (`Intervals::isSubsetOf()`). A verified
counterexample-producing oracle gives those APIs a small independent semantic
reference.

## Executable result

The new search is:

```text
Range.findSubsetCounterexample? sub dom
```

If it returns a version `v`, Lean proves:

- `sub` accepts `v`;
- `dom` rejects `v`;
- therefore `SubsetOf sub dom` is false.

If it returns `none`, Lean proves:

```text
findSubsetCounterexample? sub dom = none
  ↔
SubsetOf sub dom
```

The Boolean wrapper `Range.isSubsetOf` is therefore proved equivalent to the
extensional subset proposition.

## Candidate reuse

No second finite search universe was invented.

Subset search reuses the existing intersection critical-boundary pool:

```text
minimum stable
+ boundaries from the left range
+ boundaries from the right range
```

The key proof question was whether a semantic subset failure could always be
moved onto one of those existing boundaries.

## Proof shape

Suppose a semantic witness `w` is accepted by `sub` and rejected by
`dom`.

For each primitive comparator in a rejecting domain branch, the proof can
construct a primitive condition describing the side of the same boundary on
which `w` lies. The synthetic condition keeps the original comparator bound,
so it contributes no new boundary versions.

The proof then reuses the intersection boundary machinery.

For stable witnesses, the strengthened boundary lemma keeps the reduced witness
stable. This prevents prerelease admission from entering the argument.

For prerelease witnesses, the strengthened boundary lemma keeps the reduced
witness prerelease and on the same major/minor/patch core. That preserves the
set-local prerelease admission facts needed by both the accepting and rejecting
branches.

Thus any semantic subset counterexample can be reduced to a concrete
counterexample already present in the original finite boundary pool.

## Main theorems

The checkpoint includes:

- `Range.findSubsetCounterexample?_counterexample`
- `Range.findSubsetCounterexample?_sound`
- `Range.subsetCounterexampleCandidatesComplete`
- `Range.findSubsetCounterexample?_complete_verified`
- `Range.findSubsetCounterexample?_none_iff_subset_verified`
- `Range.isSubsetOf_eq_true_iff`

## Corpus audit

Before completing the proof, the candidate hypothesis was checked against the
existing deterministic corpus.

Across all 202 × 202 = 40,804 ordered range pairs:

| Observation | Count |
| --- | ---: |
| Bounded-corpus non-subset pairs | 29,114 |
| Boundary-search witnesses | 30,692 |
| Bounded counterexamples missed by boundary search | 0 |
| Soundness failures | 0 |
| Boundary witnesses outside the 384-version corpus | 1,578 |

These numbers are an empirical regression check, not the completeness proof.
The infinite semantic claim is discharged by Lean; the corpus audit was used to
test the candidate design before investing in that proof.

## CLI

A thin CLI adapter exposes the proved search:

```sh
lake exe semverifier subset ">=1.2.0 <2.0.0" ">=1.0.0 <3.0.0"
```

prints:

```text
subset
```

Reversing the ranges prints a concrete version:

```text
counterexample    <version>
```

The CLI contains no independent subset logic.

## Scope

This checkpoint does not claim anything about Composer/semver's subset
implementation.

The natural follow-up is a differential audit against
`Composer\\Semver\\Intervals::isSubsetOf()`, using the same shared-semantic
surface discipline already used for the Composer intersection audit.

No upstream report is warranted until such an audit produces a concrete,
intent-checked discrepancy.
