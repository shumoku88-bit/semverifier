# Next Work Checkpoint

Date: 2026-09-19

## Current state

Latest completed checkpoint:

- main checkpoint: `7a33f6f65dc77d8d3c27c373591d9cebf18d47ed`
- intersection completeness landed at `6dffc7f53c993bded6e40670711bf11c51da34f3`
- main CI #152: success
- open PRs at checkpoint: 0
- range-syntax semantics milestone: complete
- finite range-intersection witness search: proved sound and complete

The important completed theorems are:

- `Range.comparatorSetPairCandidatesComplete`
- `Range.intersectionCandidatesComplete`
- `Range.findIntersectionWitness?_complete_verified`
- `Range.findIntersectionWitness?_none_iff_not_intersects_verified`

The bounded intersection audit and the witness-backed node-semver
`Range.intersects()` discrepancy remain documented in
[INTERSECTION_DIFFERENTIAL.md](INTERSECTION_DIFFERENTIAL.md).

## CLI checkpoint complete

The first public oracle slice is implemented in PR #60.

The CLI now:

1. accepts `semverifier intersect "<left range>" "<right range>"`;
2. parses both operands with the existing `Range.parse?` frontend;
3. calls the proved `Range.findIntersectionWitness?` search directly;
4. prints a concrete witness or `disjoint`;
5. distinguishes parse failures with a non-zero exit status;
6. is exercised in CI against an intersecting case, a disjoint case, and an
   invalid range.

The CI witness case is the known prerelease/hyphen-range discrepancy already
recorded in [INTERSECTION_DIFFERENTIAL.md](INTERSECTION_DIFFERENTIAL.md), so the
external interface is checked against a semantically meaningful example rather
than only a trivial smoke test.

No new range semantics were added to support the CLI.

## Next phase

Do not reopen the completeness proof unless a concrete semantic gap is found.

The next task is real-world validation against the current node-semver `main`.
Use the CLI as the human-facing oracle while keeping automated differential
adapters outside the semantic kernel.

Current-main validation checkpoint (PR #61):

1. reproduced the known `Range.intersects()` false negative against pinned
   current node-semver `main`
   `6e05b7637396ac66522cff8731f07cfe0ef49a29`;
2. reduced the reproduction to compact witness-backed forms including
   `1.0.0-0` vs. `1.0.0-0 - 1.0.0`;
3. checked both argument orders and required node-semver `satisfies()` to
   accept the Semverifier witness on both sides;
4. independently traced the information loss from comparator-set prerelease
   admission to pairwise `Comparator.intersects()` checks;
5. reran the existing concrete-witness probe against the pinned current-main
   commit.

The detailed evidence is in
[NODE_SEMVER_CURRENT_MAIN_AUDIT.md](NODE_SEMVER_CURRENT_MAIN_AUDIT.md).

Full-matrix validation checkpoint (PR #62):

1. extended the differential workflow to all 40,804 ordered corpus range pairs;
2. classified every pair with the proved search as a concrete witness or
   semantic disjointness;
3. compared the complete matrix against pinned node-semver current main
   `6e05b7637396ac66522cff8731f07cfe0ef49a29`;
4. observed 4 witness-backed false-negative disagreements and 90 ordered
   differential false-positive disagreements;
5. reduced those 90 rows to 62 unordered pairs and detected 34 unordered pairs
   where node-semver `intersects()` is asymmetric;
6. pinned the complete disagreement set by SHA-256 fingerprint so future
   semantic or corpus changes cannot silently alter the checkpoint.

The detailed evidence is in
[NODE_SEMVER_FULL_INTERSECTION_AUDIT.md](NODE_SEMVER_FULL_INTERSECTION_AUDIT.md).

False-positive family checkpoint (PR #63):

1. partitioned all 62 unordered differential false-positive pairs with no
   remainder;
2. reduced them to four semantic families:
   - `null-below-zero`: 17 pairs;
   - `exact-prerelease-asymmetry`: 34 pairs;
   - `stable-open-gap`: 3 pairs;
   - `prerelease-boundary-overlap`: 8 pairs;
3. traced each family against the pinned current node-semver source;
4. connected the null-range family to historical issue #521 / merged PR #538,
   and compared the prerelease families with issues #223 / #254 and closed
   unmerged PR #884 without treating those as substitutes for the current
   source trace;
5. confirmed that all 34 asymmetric pairs belong to the exact-prerelease/ANY
   family and that node-semver's own range-intersection tests expect operand
   symmetry;
6. made an unclassified false-positive pair a CI failure.

The detailed evidence is in
[NODE_SEMVER_FALSE_POSITIVE_FAMILIES.md](NODE_SEMVER_FALSE_POSITIVE_FAMILIES.md).

Repair-strategy experiment checkpoint (PR #64):

1. compared staged repair models against all 40,804 ordered range pairs;
2. found that symmetric pairwise checking removes all 34 asymmetric errors with
   zero new corpus errors;
3. adding semantic non-emptiness removes 68 of the 94 baseline disagreements
   with zero new corpus errors, leaving only the stable-gap and prerelease-
   boundary families;
4. rejected two `minVersion`-based intersection strategies after each created
   1,292 new false negatives;
5. developed a finite boundary-witness strategy that repairs all 94 baseline
   disagreements with zero new corpus errors;
6. mirrored Semverifier's proved boundary-candidate shape in JavaScript and
   again obtained 0 false negatives, 0 false positives, 0 asymmetric pairs, and
   0 introduced errors over the complete corpus;
7. pinned the complete strategy comparison in CI.

The detailed evidence is in
[NODE_SEMVER_REPAIR_STRATEGY_EXPERIMENT.md](NODE_SEMVER_REPAIR_STRATEGY_EXPERIMENT.md).

The next immediate task is to validate the successful proved-boundary-shape
strategy as an actual temporary patch of pinned node-semver source. Run the
upstream full tests, lint, and coverage; rerun the complete Semverifier matrix;
exercise `includePrerelease` and `loose` separately; and measure runtime
impact before considering any upstream submission.

## Before any upstream node-semver PR

Do not rush into an upstream pull request after the CLI is working.

Treat node-semver as the first real-world validation target for Semverifier.
Before proposing any fix upstream, perform a careful adversarial audit and
record the evidence in this repository.

The validation sequence should be:

1. Reproduce the known `Range.intersects()` false negative against the current
   node-semver `main`, not only the published 7.8.5 release.
2. Minimize the contradiction to the smallest useful range pair and concrete
   witness. Check both argument orders.
3. Reconfirm on the Semverifier side that the same case is accepted by the
   proved search and that the relevant soundness/completeness theorems apply.
4. Trace the current node-semver implementation to identify the root cause
   independently. Existing upstream PR #884 is evidence to compare against,
   not a substitute for our own analysis.
5. Develop more than one plausible repair when useful, and compare their
   semantic scope. Avoid a narrow special case unless evidence shows that is
   the right boundary.
6. Run a broad differential matrix across current node-semver, any proposed
   repair, and Semverifier. Enumerate every changed range pair.
7. For every new `intersects() === true` result caused by a repair, require a
   concrete common witness. Check especially prerelease-admission cases.
8. Check the opposite risk as well: no repair should create false positives or
   silently alter unrelated stable-range behavior.
9. Run node-semver's own full tests, lint, and coverage requirements on the
   proposed repair.
10. Re-read node-semver's current CONTRIBUTING / PR policy immediately before
    submission, because contribution rules may change.

Only after this validation is complete should we decide whether to open an
upstream PR.

The desired upstream artifact is deliberately small: a minimal reproduction,
failing regression test, root-cause explanation, minimal justified repair, and
a short note that an independent Lean semantic oracle also validates the case.
Semverifier should support the claim, not overwhelm the PR.

## Explicitly not next

Do not expand into a package manager.

Do not prioritize parser-compatibility extras such as `loose`,
`includePrerelease`, leading-`v`, or every whitespace convenience unless a
real consumer requires them.

Do not add richer range algebra merely to grow the API. The immediate goal is
to make the proved intersection result easy for another program or person to
use.
