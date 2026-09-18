import Semverifier.ComparatorSet

namespace Semverifier

/--
A semantic-version range is a union of comparator sets.

Each comparator set is a conjunction. The range is satisfied when at least one
set is satisfied.
-/
structure Range where
  sets : List ComparatorSet
deriving Repr, BEq, DecidableEq

namespace Range

/--
Parse a range as `||`-separated comparator sets.

This parser intentionally supports only union at this layer. Each branch is
delegated to `ComparatorSet.parse?`, so advanced range sugar remains outside
the current boundary.

Empty branches are admitted because node-semver's empty range branch behaves as
"any stable version" under default prerelease semantics.
-/
def parse? (raw : String) : Option Range := do
  let sets ← (raw.split "||" |>.toStringList).mapM ComparatorSet.parse?
  some { sets }

/-- Decide whether a version satisfies at least one comparator set. -/
def satisfies (range : Range) (candidate : Version) : Bool :=
  range.sets.any (fun set => set.satisfies candidate)

end Range
end Semverifier
