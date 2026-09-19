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

The immediate sequence is:

1. reproduce the known `Range.intersects()` false negative against current
   node-semver `main`;
2. minimize and record the smallest useful witness-backed contradiction;
3. trace the current upstream implementation independently;
4. build a differential workflow that compares current upstream behavior with
   Semverifier and enumerates every disagreement;
5. only then investigate and validate candidate repairs.

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
