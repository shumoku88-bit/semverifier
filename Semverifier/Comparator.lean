import Semverifier.Parser

namespace Semverifier

/-- Primitive comparator operators used by semantic-version ranges. -/
inductive ComparatorOperator where
  | lt
  | lte
  | gt
  | gte
  | eq
deriving Repr, BEq, DecidableEq

/--
One primitive version constraint.

The bound retains its full version identity, but satisfaction is defined only
through SemVer precedence. Build metadata therefore cannot affect the answer.
-/
structure Comparator where
  operator : ComparatorOperator
  bound : Version
deriving Repr, BEq, DecidableEq

namespace Comparator

/-- Decide whether a version satisfies one primitive comparator. -/
def satisfies (comparator : Comparator) (candidate : Version) : Bool :=
  match comparator.operator, Version.precedence candidate comparator.bound with
  | .lt, .lt => true
  | .lt, _ => false
  | .lte, .gt => false
  | .lte, _ => true
  | .gt, .gt => true
  | .gt, _ => false
  | .gte, .lt => false
  | .gte, _ => true
  | .eq, .eq => true
  | .eq, _ => false

/--
Changing build metadata on either side cannot affect primitive-comparator
satisfaction.
-/
theorem satisfies_ignores_build
    (comparator : Comparator)
    (candidate : Version)
    (boundBuild candidateBuild : List String) :
    satisfies
        { comparator with bound := { comparator.bound with build := boundBuild } }
        { candidate with build := candidateBuild } =
      satisfies comparator candidate := by
  cases comparator with
  | mk operator bound =>
      cases operator <;> rfl

end Comparator
end Semverifier
