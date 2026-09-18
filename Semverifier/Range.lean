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

/--
Executable union semantics, exposed propositionally.

A range satisfies a candidate exactly when some comparator set in the range
satisfies it.
-/
theorem satisfies_eq_true_iff
    (range : Range)
    (candidate : Version) :
    range.satisfies candidate = true ↔
      ∃ set, set ∈ range.sets ∧ set.satisfies candidate = true := by
  simp [satisfies]

/-- Union two already-parsed semantic ranges. -/
def union (left right : Range) : Range :=
  { sets := left.sets ++ right.sets }

/-- Range union corresponds exactly to boolean disjunction of satisfaction. -/
theorem satisfies_union
    (left right : Range)
    (candidate : Version) :
    (union left right).satisfies candidate =
      (left.satisfies candidate || right.satisfies candidate) := by
  simp [union, satisfies]

end Range
end Semverifier
