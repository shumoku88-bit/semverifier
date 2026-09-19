# node-semver PR #901 independent intersection audit

Date: 2026-09-19

## Scope

This checkpoint evaluates the open upstream pull request:

- npm/node-semver PR #901: `fix: exclude unshared prereleases from range intersections`
- audited head: `7a597a93b2feb62696f94e4df9533363eaf8f98a`
- upstream baseline: node-semver 7.8.5 / main `6e05b7637396ac66522cff8731f07cfe0ef49a29`

The purpose is freshness checking before any Semverifier-originated upstream
submission. It is not an endorsement of PR #901 and does not modify
Semverifier's semantic kernel.

## Method

The existing proved Semverifier intersection oracle generated the same complete
202 x 202 corpus used by the pinned-main audit:

```text
40,804 ordered range pairs
23,410 intersecting pairs with concrete Semverifier witnesses
17,394 Semverifier-disjoint pairs
```

The workflow first reran the pinned node-semver baseline unchanged, then
installed the exact PR #901 head and reran the complete matrix.

For every Semverifier witness, node-semver's own `satisfies()` was also
required to accept that witness on both input ranges.

## Baseline

Pinned current main / 7.8.5:

```text
false negatives: 4
false positives: 90
asymmetric unordered pairs: 34
```

The 90 ordered false positives are the previously recorded four-family set.

## PR #901 result

Against PR #901 head `7a597a93b2feb62696f94e4df9533363eaf8f98a`:

```text
false negatives: 4
false positives: 0
asymmetric unordered pairs: 0
```

So, over this fixed corpus, PR #901:

1. removes all 90 baseline false-positive rows;
2. removes all 34 baseline asymmetric unordered pairs;
3. introduces no observed false positive;
4. leaves the same four known prerelease/hyphen false negatives unchanged.

The four remaining false negatives are:

```text
1.2.3-alpha.2              vs 1.2.3-alpha.2 - 1.2.3
=1.2.3-alpha.2             vs 1.2.3-alpha.2 - 1.2.3
1.2.3-alpha.2 - 1.2.3      vs 1.2.3-alpha.2
1.2.3-alpha.2 - 1.2.3      vs =1.2.3-alpha.2
```

Each has concrete witness `1.2.3-alpha.2`.

## Interpretation

The broad upstream issue draft prepared before this freshness check is now
stale as a submission artifact.

Its false-positive and asymmetry portion substantially overlaps an already-open
upstream repair. Posting the draft unchanged would therefore obscure the
current upstream state.

The remaining independently reproduced disagreement is narrower: the four
witness-backed false negatives in the same semantic family as closed,
unmerged PR #884.

PR #885 remains open and addresses a separate near-zero comparator
false-negative.

## Evidence boundary

This audit establishes behavior only over Semverifier's deterministic
40,804-pair corpus and the exact PR #901 head above.

It does not prove PR #901 correct for every node-semver input, syntax mode, or
future commit, and it does not replace upstream review.

## Upstream submission consequence

Do not post the previous broad issue body unchanged.

Before any upstream action:

1. recheck whether PR #901 has moved or received maintainer feedback;
2. decide whether independent validation belongs as a concise comment on #901;
3. treat the remaining four false negatives separately from the repaired
   false-positive families;
4. review any proposed public text field-by-field before posting.
