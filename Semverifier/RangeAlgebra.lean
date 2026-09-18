import Semverifier.Range

namespace Semverifier

namespace Range

/-- A range contains a candidate exactly when its executable semantics accepts it. -/
def Contains (range : Range) (candidate : Version) : Prop :=
  range.satisfies candidate = true

/--
Executable witness check for semantic range intersection.

This checks one candidate only. Deciding whether some candidate exists is a
separate problem.
-/
def overlapsAt (left right : Range) (candidate : Version) : Bool :=
  left.satisfies candidate && right.satisfies candidate

/--
Two ranges semantically intersect when there exists at least one version
accepted by both ranges.

This is intentionally a proposition first. A future executable decision
procedure must be proved against this specification rather than defining the
meaning of intersection by implementation convention.
-/
def Intersects (left right : Range) : Prop :=
  ∃ candidate, Contains left candidate ∧ Contains right candidate

/-- Every version accepted by `sub` is also accepted by `dom`. -/
def SubsetOf (sub dom : Range) : Prop :=
  ∀ candidate, Contains sub candidate → Contains dom candidate

/-- Two ranges accept exactly the same versions. -/
def Equivalent (left right : Range) : Prop :=
  ∀ candidate, Contains left candidate ↔ Contains right candidate

theorem overlapsAt_eq_true_iff
    (left right : Range)
    (candidate : Version) :
    overlapsAt left right candidate = true ↔
      Contains left candidate ∧ Contains right candidate := by
  simp [overlapsAt, Contains]

theorem intersects_iff_exists_overlapsAt
    (left right : Range) :
    Intersects left right ↔
      ∃ candidate, overlapsAt left right candidate = true := by
  simp [Intersects, overlapsAt_eq_true_iff]

theorem intersects_comm
    (left right : Range) :
    Intersects left right ↔ Intersects right left := by
  constructor
  · rintro ⟨candidate, hLeft, hRight⟩
    exact ⟨candidate, hRight, hLeft⟩
  · rintro ⟨candidate, hRight, hLeft⟩
    exact ⟨candidate, hLeft, hRight⟩

theorem subset_refl (range : Range) :
    SubsetOf range range := by
  intro candidate h
  exact h

theorem subset_trans
    (first second third : Range)
    (hFirstSecond : SubsetOf first second)
    (hSecondThird : SubsetOf second third) :
    SubsetOf first third := by
  intro candidate hFirst
  exact hSecondThird candidate (hFirstSecond candidate hFirst)

theorem equivalent_refl (range : Range) :
    Equivalent range range := by
  intro candidate
  exact Iff.rfl

theorem equivalent_symm
    (left right : Range)
    (h : Equivalent left right) :
    Equivalent right left := by
  intro candidate
  exact (h candidate).symm

theorem equivalent_trans
    (first second third : Range)
    (hFirstSecond : Equivalent first second)
    (hSecondThird : Equivalent second third) :
    Equivalent first third := by
  intro candidate
  exact (hFirstSecond candidate).trans (hSecondThird candidate)

theorem equivalent_iff_mutual_subset
    (left right : Range) :
    Equivalent left right ↔
      SubsetOf left right ∧ SubsetOf right left := by
  constructor
  · intro h
    constructor
    · intro candidate hLeft
      exact (h candidate).mp hLeft
    · intro candidate hRight
      exact (h candidate).mpr hRight
  · rintro ⟨hLeftRight, hRightLeft⟩
    intro candidate
    constructor
    · exact hLeftRight candidate
    · exact hRightLeft candidate

theorem subset_union_left
    (left right : Range) :
    SubsetOf left (union left right) := by
  intro candidate hLeft
  unfold Contains at hLeft ⊢
  simp [satisfies_union, hLeft]

theorem subset_union_right
    (left right : Range) :
    SubsetOf right (union left right) := by
  intro candidate hRight
  unfold Contains at hRight ⊢
  simp [satisfies_union, hRight]

end Range
end Semverifier
