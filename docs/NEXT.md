# Next Work Checkpoint

Date: 2026-09-19

## Current state

Latest completed intersection-completeness milestone:

- main checkpoint: `6dffc7f53c993bded6e40670711bf11c51da34f3`
- main CI #150: success
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

## Next phase

Do not reopen the completeness proof unless a concrete semantic gap is found.

The next phase is to make the verified kernel useful as a small semantic oracle.
The first task should be a minimal public CLI around the existing parser and
verified intersection search.

A reasonable first interface is conceptually:

```text
semverifier intersect "<left range>" "<right range>"
```

For the currently supported syntax, it should:

1. parse both ranges with the existing Semverifier range parser;
2. run the verified `Range.findIntersectionWitness?` search;
3. print a concrete witness when the ranges intersect;
4. report disjointness when the verified search returns `none`;
5. distinguish parse failure from semantic disjointness.

Keep this layer thin. The CLI should call the proved kernel rather than
reimplement range logic.

## Definition of done for the first CLI slice

- add a user-facing `lean_exe semverifier` or equivalently small executable;
- accept two supported range expressions for intersection checking;
- expose witness vs. disjoint vs. parse-error outcomes clearly;
- add focused executable tests or CI examples;
- keep node-semver outside the semantic kernel.

After that, the next useful layer is a differential-oracle workflow that makes
it easy to compare existing implementations against Semverifier and emit
witness-backed counterexamples.

## Explicitly not next

Do not expand into a package manager.

Do not prioritize parser-compatibility extras such as `loose`,
`includePrerelease`, leading-`v`, or every whitespace convenience unless a
real consumer requires them.

Do not add richer range algebra merely to grow the API. The immediate goal is
to make the proved intersection result easy for another program or person to
use.
