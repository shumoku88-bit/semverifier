import Semverifier.RangeIntersection

/-!
# Semverifier

The public semantic kernel covers validated SemVer versions, precedence,
primitive comparators, comparator sets, default prerelease admission, and range
union.

Surface range syntax is kept outside that kernel and desugared into it.
Canonical strict forms for partial/X-ranges, operator-prefixed partials, tilde
(including `~>`), caret, and whole-branch hyphen ranges all reuse the same
Comparator / ComparatorSet semantics.

Range algebra is specified extensionally over satisfaction sets:
intersection means a common accepted version exists, subset means every
accepted version on the left is accepted on the right, and equivalence means
both ranges accept exactly the same versions. Executable search is layered on top of these meanings. The first intersection
search returns concrete witnesses and proves returned witnesses sound; a
completeness proof is still required before absence of a witness may be treated
as a disjointness decision.
-/
