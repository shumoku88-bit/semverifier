# Composer/semver Intersection Audit

Date: 2026-10-02

## Purpose

This audit asks whether Semverifier's proved range-intersection oracle agrees
with Composer/semver in the part of the range language where the two
implementations first demonstrate compatible satisfaction behavior.

The target is Composer/semver current main pinned at:

- repository: `composer/semver`
- commit: `4221b9ec7fdd42b5b3d939509d55d97b511c52df`

This is deliberately not a claim that Composer implements npm/node-semver
semantics. Composer documents its own compatibility constraints, supports
four-component normalized versions and `dev-*` branches, and has prerelease /
stability behavior outside Semverifier's model.

## Method

The audit has two stages.

### Stage 1: discover the shared semantic surface

The existing Semverifier conformance corpus contains:

- 202 range expressions;
- 384 candidate versions;
- 77,568 range/version judgments.

Of those candidate judgments, 25,856 are against stable versions (including
build-metadata variants).

Every corpus row is evaluated by both Semverifier and Composer's parsed
constraint machinery.

Two compatibility sets are then derived:

1. **stable-compatible**: no disagreement on any stable corpus version;
2. **full-corpus-compatible**: no disagreement on any of the 384 corpus
   versions, including prereleases.

The stable-compatible set is useful for understanding how much ordinary stable
range behavior overlaps. It is not used directly for intersection claims,
because Composer's prerelease and dev semantics can still differ.

Only the full-corpus-compatible set proceeds to stage 2.

### Stage 2: compare range intersection

For every ordered pair of full-corpus-compatible ranges:

1. Semverifier classifies the pair using the proved
   `Range.findIntersectionWitness?` search;
2. Composer parses both constraints and evaluates
   `Intervals::haveIntersections()`;
3. the boolean judgments are compared;
4. if Semverifier reports an intersection while Composer does not, the concrete
   Semverifier witness is also tested against both Composer constraints.

This keeps Composer-specific syntax or known dialect differences out of the
direct intersection comparison.

## Stage 1 result

The pinned run produced:

| Observation | Count |
| --- | ---: |
| Corpus rows | 77,568 |
| Stable corpus rows | 25,856 |
| Range expressions | 202 |
| Parse-incompatible ranges | 60 |
| Semantic mismatch rows | 10,747 |
| Stable semantic mismatch rows | 280 |
| Ranges with any semantic mismatch | 115 |
| Ranges with stable semantic mismatch | 14 |
| Stable-compatible ranges | 128 |
| Full-corpus-compatible ranges | 27 |

The large difference between 128 stable-compatible ranges and 27
full-corpus-compatible ranges is important. It confirms that a stable-only
agreement filter would be too weak for a direct comparison of
`haveIntersections()`, because prerelease behavior remains a substantial
semantic boundary.

The 60 parse-incompatible ranges are treated as syntax/dialect differences, not
bugs. They include forms such as npm-style `~>` aliases, wildcard operands in
some comparator/caret/tilde positions, open-ended unions, and wildcard hyphen
forms that Composer does not parse in the same surface language.

Likewise, the 10,747 semantic mismatch rows are not reported upstream. They
contain real dialect differences, particularly around prerelease/stability
handling, and require separate intent analysis before any individual mismatch
could be called a defect.

## Full-corpus-compatible range set

The 27 ranges admitted to the direct intersection audit are:

```text
0.0.0
0.0.1
0.1.0
0.2.3
1.0.0
1.2.3
1.2.3-alpha.2
1.2.3-alpha.2 - 1.2.3
1.9.9
2.0.0
2.5.1
3.0.0
<0.0.0
=0.0.0
=0.0.1
=0.1.0
=0.2.3
=1.0.0
=1.2.3
=1.2.3-alpha.2
=1.9.9
=2.0.0
=2.5.1
=3.0.0
^2.5.1
~1.2.3-beta.2
~2.5.1
```

This set is an empirical compatibility boundary for the pinned corpus, not a
proof that the two libraries have identical semantics for every possible
version outside the corpus.

## Stage 2 result

The 27 compatible ranges produce 729 ordered range pairs.

| Intersection observation | Count |
| --- | ---: |
| Directly comparable pairs | 729 |
| Total disagreements | 0 |
| Semverifier true / Composer false | 0 |
| Composer true / Semverifier false | 0 |
| Witness-confirmed Composer contradictions | 0 |

So on this independently selected shared semantic surface,
Composer/semver's `Intervals::haveIntersections()` agrees with
Semverifier's proved intersection search on all 729 ordered pairs.

This is a useful negative result: the experiment found no intersection defect
to report to Composer.

## Reproducibility checkpoint

CI pins:

- all corpus and partition counts above;
- SHA-256 fingerprints for the parse-incompatible, mismatch and compatible
  range partitions;
- the 729-pair intersection comparison;
- zero intersection disagreements.

A change to Semverifier's corpus, Composer's pinned source, or the adapter that
alters any of those observations fails CI and requires explicit review.

## Interpretation

This audit gives two useful results.

First, Semverifier can be used against an implementation whose semantics are not
simply node-semver's semantics, provided the shared surface is discovered
empirically instead of assumed.

Second, Composer's interval implementation survives the resulting direct
intersection check. The correct outcome here is therefore not an upstream bug
report but a reproducible compatibility checkpoint.

## Next step

Do not broaden this into all Composer syntax merely to obtain more pairs.

A future Composer audit is justified only if there is a concrete question, for
example:

- a newly reported Composer intersection/subset bug;
- a change to Composer's interval implementation;
- a need to study one of the excluded semantic families separately.

No upstream Composer issue or comment is warranted by this checkpoint.
