import Semverifier.Caret
import Semverifier.HyphenRange
import Semverifier.Tilde
import Semverifier.XRange

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

private def branchTokens (raw : String) : List String :=
  raw.split Char.isWhitespace
    |>.toStringList
    |>.filter (fun token => !token.isEmpty)

private def parseTerm? (raw : String) : Option (List Comparator) :=
  if raw.startsWith "^" then
    (Caret.parse? raw).map (fun set => set.comparators)
  else if raw.startsWith "~" then
    (Tilde.parse? raw).map (fun set => set.comparators)
  else
    match Comparator.parse? raw with
    | some comparator => some [comparator]
    | none => (XRange.parse? raw).map (fun set => set.comparators)

private def parseOrdinaryBranch? (raw : String) : Option ComparatorSet := do
  let chunks ← (branchTokens raw).mapM parseTerm?
  some { comparators := chunks.foldr (· ++ ·) [] }

private def parseBranch? (raw : String) : Option ComparatorSet :=
  match HyphenRange.parse? raw with
  | some set => some set
  | none => parseOrdinaryBranch? raw

/--
Parse a range as `||`-separated comparator sets.

Each branch accepts primitive comparators plus the frontends that have already
been defined. Caret, tilde, partial/X-range, and whole-branch strict hyphen
syntax are desugared into comparator sets before satisfaction.

Empty branches are admitted because node-semver's empty range branch behaves as
"any stable version" under default prerelease semantics.
-/
def parse? (raw : String) : Option Range := do
  let sets ← (raw.split "||" |>.toStringList).mapM parseBranch?
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
