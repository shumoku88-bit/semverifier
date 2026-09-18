import Semverifier.Range

/-!
# Semverifier

The public semantic kernel covers validated SemVer versions, precedence,
primitive comparators, comparator sets, default prerelease admission, and range
union.

Surface range syntax is kept outside that kernel and desugared into it.
Canonical strict forms for partial/X-ranges, operator-prefixed partials, tilde
(including `~>`), caret, and whole-branch hyphen ranges all reuse the same
Comparator / ComparatorSet semantics.

Parser compatibility conveniences and richer range algebra are deliberately
separate from this syntax semantics boundary.
-/
