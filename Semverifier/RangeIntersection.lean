import Lean.Elab.Tactic.Omega
import Semverifier.RangeAlgebra

namespace Semverifier

namespace Range

private def minimumStable : Version :=
  { major := 0, minor := 0, patch := 0 }

private def stableAtCore (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch
  }

private def nextStablePatch (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch + 1
  }

/--
Lexicographic order on the stable major/minor/patch core.

Prerelease and build metadata are deliberately absent. This is the order used
by the stable half of comparator-set intersection completeness.
-/
private def stableCoreLE (left right : Version) : Prop :=
  left.major < right.major ∨
    (left.major = right.major ∧
      (left.minor < right.minor ∨
        (left.minor = right.minor ∧ left.patch ≤ right.patch)))

private instance stableCoreLE_decidable
    (left right : Version) :
    Decidable (stableCoreLE left right) := by
  unfold stableCoreLE
  infer_instance

private theorem stableCoreLE_refl (version : Version) :
    stableCoreLE version version := by
  simp [stableCoreLE]

private theorem stableCoreLE_trans
    (first second third : Version)
    (hFirstSecond : stableCoreLE first second)
    (hSecondThird : stableCoreLE second third) :
    stableCoreLE first third := by
  unfold stableCoreLE at *
  omega

private theorem stableCoreLE_total (left right : Version) :
    stableCoreLE left right ∨ stableCoreLE right left := by
  unfold stableCoreLE
  omega

private def stableCoreLT (left right : Version) : Prop :=
  left.major < right.major ∨
    (left.major = right.major ∧
      (left.minor < right.minor ∨
        (left.minor = right.minor ∧ left.patch < right.patch)))

private theorem stableCoreLT_of_le_of_lt
    (first second third : Version)
    (hFirstSecond : stableCoreLE first second)
    (hSecondThird : stableCoreLT second third) :
    stableCoreLT first third := by
  unfold stableCoreLE at hFirstSecond
  unfold stableCoreLT at hSecondThird ⊢
  omega

private theorem precedence_lt_of_stableCoreLT
    (left right : Version)
    (hCore : stableCoreLT left right) :
    Version.precedence left right = .lt := by
  unfold stableCoreLT at hCore
  rcases hCore with hMajor | ⟨hMajorEq, hMinor⟩
  · have hMajorCompare :
        compare left.major right.major = .lt :=
      Nat.compare_eq_lt.mpr hMajor
    simp [
      Version.precedence,
      Version.precedenceKey,
      PrecedenceKey.ordering,
      hMajorCompare
    ]
  · rcases hMinor with hMinorLt | ⟨hMinorEq, hPatchLt⟩
    · have hMajorCompare :
          compare left.major right.major = .eq :=
        Nat.compare_eq_eq.mpr hMajorEq
      have hMinorCompare :
          compare left.minor right.minor = .lt :=
        Nat.compare_eq_lt.mpr hMinorLt
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajorCompare,
        hMinorCompare
      ]
    · have hMajorCompare :
          compare left.major right.major = .eq :=
        Nat.compare_eq_eq.mpr hMajorEq
      have hMinorCompare :
          compare left.minor right.minor = .eq :=
        Nat.compare_eq_eq.mpr hMinorEq
      have hPatchCompare :
          compare left.patch right.patch = .lt :=
        Nat.compare_eq_lt.mpr hPatchLt
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajorCompare,
        hMinorCompare,
        hPatchCompare
      ]

private theorem precedence_gt_of_stableCoreLT
    (left right : Version)
    (hCore : stableCoreLT left right) :
    Version.precedence right left = .gt := by
  unfold stableCoreLT at hCore
  rcases hCore with hMajor | ⟨hMajorEq, hMinor⟩
  · have hMajorCompare :
        compare right.major left.major = .gt :=
      Nat.compare_eq_gt.mpr hMajor
    simp [
      Version.precedence,
      Version.precedenceKey,
      PrecedenceKey.ordering,
      hMajorCompare
    ]
  · rcases hMinor with hMinorLt | ⟨hMinorEq, hPatchLt⟩
    · have hMajorCompare :
          compare right.major left.major = .eq :=
        Nat.compare_eq_eq.mpr hMajorEq.symm
      have hMinorCompare :
          compare right.minor left.minor = .gt :=
        Nat.compare_eq_gt.mpr hMinorLt
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajorCompare,
        hMinorCompare
      ]
    · have hMajorCompare :
          compare right.major left.major = .eq :=
        Nat.compare_eq_eq.mpr hMajorEq.symm
      have hMinorCompare :
          compare right.minor left.minor = .eq :=
        Nat.compare_eq_eq.mpr hMinorEq.symm
      have hPatchCompare :
          compare right.patch left.patch = .gt :=
        Nat.compare_eq_gt.mpr hPatchLt
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajorCompare,
        hMinorCompare,
        hPatchCompare
      ]

private theorem prerelease_eq_nil_of_stable
    (version : Version)
    (hStable : version.prerelease.isEmpty = true) :
    version.prerelease = [] := by
  cases hPrerelease : version.prerelease with
  | nil =>
      rfl
  | cons head tail =>
      simp [hPrerelease] at hStable

private theorem stableCoreLT_of_precedence_lt_of_stable
    (left right : Version)
    (hStable : left.prerelease.isEmpty = true)
    (hPrecedence : Version.precedence left right = .lt) :
    stableCoreLT left right := by
  have hLeftPrerelease :=
    prerelease_eq_nil_of_stable left hStable
  cases hMajor : compare left.major right.major with
  | lt =>
      have hMajorLt : left.major < right.major :=
        Nat.compare_eq_lt.mp hMajor
      exact Or.inl hMajorLt
  | gt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hPrecedence
  | eq =>
      have hMajorEq : left.major = right.major :=
        Nat.compare_eq_eq.mp hMajor
      cases hMinor : compare left.minor right.minor with
      | lt =>
          have hMinorLt : left.minor < right.minor :=
            Nat.compare_eq_lt.mp hMinor
          exact Or.inr ⟨hMajorEq, Or.inl hMinorLt⟩
      | gt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hPrecedence
      | eq =>
          have hMinorEq : left.minor = right.minor :=
            Nat.compare_eq_eq.mp hMinor
          cases hPatch : compare left.patch right.patch with
          | lt =>
              have hPatchLt : left.patch < right.patch :=
                Nat.compare_eq_lt.mp hPatch
              exact
                Or.inr
                  ⟨hMajorEq, Or.inr ⟨hMinorEq, hPatchLt⟩⟩
          | gt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hPrecedence
          | eq =>
              cases hRightPrerelease : right.prerelease with
              | nil =>
                  have hExpected :
                      Version.precedence left right = .eq := by
                    simp only [
                      Version.precedence,
                      Version.precedenceKey,
                      PrecedenceKey.ordering
                    ]
                    rw [hMajor, hMinor, hPatch]
                    rw [hLeftPrerelease, hRightPrerelease]
                    rfl
                  rw [hExpected] at hPrecedence
                  contradiction
              | cons head tail =>
                  have hExpected :
                      Version.precedence left right = .gt := by
                    simp only [
                      Version.precedence,
                      Version.precedenceKey,
                      PrecedenceKey.ordering
                    ]
                    rw [hMajor, hMinor, hPatch]
                    rw [hLeftPrerelease, hRightPrerelease]
                    rfl
                  rw [hExpected] at hPrecedence
                  contradiction

private theorem stable_bound_and_same_core_of_precedence_eq
    (candidate bound : Version)
    (hCandidateStable : candidate.prerelease.isEmpty = true)
    (hPrecedence : Version.precedence candidate bound = .eq) :
    bound.prerelease.isEmpty = true ∧
      candidate.major = bound.major ∧
      candidate.minor = bound.minor ∧
      candidate.patch = bound.patch := by
  have hCandidatePrerelease :=
    prerelease_eq_nil_of_stable candidate hCandidateStable
  cases hMajor : compare candidate.major bound.major with
  | lt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hPrecedence
  | gt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hPrecedence
  | eq =>
      have hMajorEq : candidate.major = bound.major :=
        Nat.compare_eq_eq.mp hMajor
      cases hMinor : compare candidate.minor bound.minor with
      | lt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hPrecedence
      | gt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hPrecedence
      | eq =>
          have hMinorEq : candidate.minor = bound.minor :=
            Nat.compare_eq_eq.mp hMinor
          cases hPatch : compare candidate.patch bound.patch with
          | lt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hPrecedence
          | gt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hPrecedence
          | eq =>
              have hPatchEq : candidate.patch = bound.patch :=
                Nat.compare_eq_eq.mp hPatch
              cases hBoundPrerelease : bound.prerelease with
              | nil =>
                  exact
                    ⟨by simp [hBoundPrerelease],
                      hMajorEq,
                      hMinorEq,
                      hPatchEq⟩
              | cons head tail =>
                  have hExpected :
                      Version.precedence candidate bound = .gt := by
                    simp only [
                      Version.precedence,
                      Version.precedenceKey,
                      PrecedenceKey.ordering
                    ]
                    rw [hMajor, hMinor, hPatch]
                    rw [hCandidatePrerelease, hBoundPrerelease]
                    rfl
                  rw [hExpected] at hPrecedence
                  contradiction

private theorem precedence_eq_of_stable_same_core
    (left right : Version)
    (hLeftStable : left.prerelease.isEmpty = true)
    (hRightStable : right.prerelease.isEmpty = true)
    (hMajor : left.major = right.major)
    (hMinor : left.minor = right.minor)
    (hPatch : left.patch = right.patch) :
    Version.precedence left right = .eq := by
  have hLeftPrerelease :=
    prerelease_eq_nil_of_stable left hLeftStable
  have hRightPrerelease :=
    prerelease_eq_nil_of_stable right hRightStable
  have hMajorCompare :
      compare left.major right.major = .eq :=
    Nat.compare_eq_eq.mpr hMajor
  have hMinorCompare :
      compare left.minor right.minor = .eq :=
    Nat.compare_eq_eq.mpr hMinor
  have hPatchCompare :
      compare left.patch right.patch = .eq :=
    Nat.compare_eq_eq.mpr hPatch
  simp only [
    Version.precedence,
    Version.precedenceKey,
    PrecedenceKey.ordering
  ]
  rw [hMajorCompare, hMinorCompare, hPatchCompare]
  rw [hLeftPrerelease, hRightPrerelease]
  rfl

private theorem minimumStable_core_le (version : Version) :
    stableCoreLE minimumStable version := by
  simp [stableCoreLE, minimumStable] <;> omega

/--
Binary maximum for the stable core order.
-/
private def stableCoreMax (left right : Version) : Version :=
  if stableCoreLE left right then right else left

private theorem stableCoreLE_left_max (left right : Version) :
    stableCoreLE left (stableCoreMax left right) := by
  by_cases h : stableCoreLE left right
  · simp [stableCoreMax, h]
  · simp [stableCoreMax, h, stableCoreLE_refl]

private theorem stableCoreLE_right_max (left right : Version) :
    stableCoreLE right (stableCoreMax left right) := by
  by_cases h : stableCoreLE left right
  · simp [stableCoreMax, h, stableCoreLE_refl]
  · have hRightLeft : stableCoreLE right left := by
      rcases stableCoreLE_total left right with hLeftRight | hRightLeft
      · exact (h hLeftRight).elim
      · exact hRightLeft
    simpa [stableCoreMax, h] using hRightLeft

private theorem stableCoreMax_core_le
    (left right upper : Version)
    (hLeft : stableCoreLE left upper)
    (hRight : stableCoreLE right upper) :
    stableCoreLE (stableCoreMax left right) upper := by
  by_cases h : stableCoreLE left right
  · simpa [stableCoreMax, h] using hRight
  · simpa [stableCoreMax, h] using hLeft

private theorem stableCoreMax_eq_left_or_right
    (left right : Version) :
    stableCoreMax left right = left ∨ stableCoreMax left right = right := by
  by_cases h : stableCoreLE left right
  · exact Or.inr (by simp [stableCoreMax, h])
  · exact Or.inl (by simp [stableCoreMax, h])

private theorem stableCoreMax_is_stable
    (left right : Version)
    (hLeft : left.prerelease.isEmpty = true)
    (hRight : right.prerelease.isEmpty = true) :
    (stableCoreMax left right).prerelease.isEmpty = true := by
  rcases stableCoreMax_eq_left_or_right left right with hMax | hMax
  · simpa [hMax] using hLeft
  · simpa [hMax] using hRight

private def prereleaseFloorAtCore (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch
    prerelease := [.numeric 0]
  }

private def strippedBound (version : Version) : Version :=
  { version with build := [] }

private def prereleaseSuccessor (version : Version) : Version :=
  {
    strippedBound version with
    prerelease := version.prerelease ++ [.numeric 0]
  }

/--
A prerelease version lies on the same major/minor/patch core as a reference.
-/
private def samePrereleaseCoreAs
    (candidate reference : Version) : Prop :=
  candidate.prerelease.isEmpty = false ∧
    candidate.major = reference.major ∧
    candidate.minor = reference.minor ∧
    candidate.patch = reference.patch

private instance samePrereleaseCoreAs_decidable
    (candidate reference : Version) :
    Decidable (samePrereleaseCoreAs candidate reference) := by
  unfold samePrereleaseCoreAs
  infer_instance

/--
Maximum of two prerelease versions intended to lie on one fixed core.

The function deliberately returns one of its inputs so finite folds remain
inside the existing generated candidate pool.
-/
private def prereleaseCoreMax (left right : Version) : Version :=
  match Version.precedence left right with
  | .gt => left
  | .lt | .eq => right

private theorem prereleaseCoreMax_eq_left_or_right
    (left right : Version) :
    prereleaseCoreMax left right = left ∨
      prereleaseCoreMax left right = right := by
  cases hPrecedence : Version.precedence left right <;>
    simp [prereleaseCoreMax, hPrecedence]

private theorem prereleaseCoreMax_same_core_as
    (left right reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference) :
    samePrereleaseCoreAs
      (prereleaseCoreMax left right)
      reference := by
  rcases prereleaseCoreMax_eq_left_or_right left right with hMax | hMax
  · simpa [hMax] using hLeft
  · simpa [hMax] using hRight

private theorem prereleaseCoreMax_left_isLE
    (left right reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference) :
    (Version.precedence left (prereleaseCoreMax left right)).isLE := by
  rcases hLeft with
    ⟨hLeftPrerelease, hLeftMajor, hLeftMinor, hLeftPatch⟩
  rcases hRight with
    ⟨hRightPrerelease, hRightMajor, hRightMinor, hRightPatch⟩
  cases hPrecedence : Version.precedence left right with
  | lt =>
      simp [prereleaseCoreMax, hPrecedence]
  | eq =>
      simp [prereleaseCoreMax, hPrecedence]
  | gt =>
      have hSelf :=
        Version.precedence_prerelease_self_eq
          left hLeftPrerelease
      simp [prereleaseCoreMax, hPrecedence, hSelf]

private theorem prereleaseCoreMax_right_isLE
    (left right reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference) :
    (Version.precedence right (prereleaseCoreMax left right)).isLE := by
  rcases hLeft with
    ⟨hLeftPrerelease, hLeftMajor, hLeftMinor, hLeftPatch⟩
  rcases hRight with
    ⟨hRightPrerelease, hRightMajor, hRightMinor, hRightPatch⟩
  have hMajor : left.major = right.major :=
    hLeftMajor.trans hRightMajor.symm
  have hMinor : left.minor = right.minor :=
    hLeftMinor.trans hRightMinor.symm
  have hPatch : left.patch = right.patch :=
    hLeftPatch.trans hRightPatch.symm
  have hSwap :=
    Version.precedence_prerelease_swap_of_same_core
      left right
      hLeftPrerelease hRightPrerelease
      hMajor hMinor hPatch
  cases hPrecedence : Version.precedence left right with
  | lt =>
      have hSelf :=
        Version.precedence_prerelease_self_eq
          right hRightPrerelease
      simp [prereleaseCoreMax, hPrecedence, hSelf]
  | eq =>
      have hSelf :=
        Version.precedence_prerelease_self_eq
          right hRightPrerelease
      simp [prereleaseCoreMax, hPrecedence, hSelf]
  | gt =>
      have hReverse : Version.precedence right left = .lt := by
        cases hReverse : Version.precedence right left <;>
          simp [hPrecedence, hReverse] at hSwap ⊢
      have hMax :
          prereleaseCoreMax left right = left := by
        simp [prereleaseCoreMax, hPrecedence]
      rw [hMax]
      simp [hReverse]

private theorem prereleaseCoreMax_isLE
    (left right upper reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference)
    (hUpper : samePrereleaseCoreAs upper reference)
    (hLeftUpper : (Version.precedence left upper).isLE)
    (hRightUpper : (Version.precedence right upper).isLE) :
    (Version.precedence
      (prereleaseCoreMax left right)
      upper).isLE := by
  rcases prereleaseCoreMax_eq_left_or_right left right with hMax | hMax
  · simpa [hMax] using hLeftUpper
  · simpa [hMax] using hRightUpper

private theorem prereleaseCore_isLE_trans
    (first second third reference : Version)
    (hFirst : samePrereleaseCoreAs first reference)
    (hSecond : samePrereleaseCoreAs second reference)
    (hThird : samePrereleaseCoreAs third reference)
    (hFirstSecond : (Version.precedence first second).isLE)
    (hSecondThird : (Version.precedence second third).isLE) :
    (Version.precedence first third).isLE := by
  rcases hFirst with
    ⟨hFirstPrerelease, hFirstMajor, hFirstMinor, hFirstPatch⟩
  rcases hSecond with
    ⟨hSecondPrerelease, hSecondMajor, hSecondMinor, hSecondPatch⟩
  rcases hThird with
    ⟨hThirdPrerelease, hThirdMajor, hThirdMinor, hThirdPatch⟩
  exact
    Version.precedence_prerelease_isLE_trans_of_same_core
      first second third
      hFirstPrerelease
      hSecondPrerelease
      hThirdPrerelease
      (hFirstMajor.trans hSecondMajor.symm)
      (hFirstMinor.trans hSecondMinor.symm)
      (hFirstPatch.trans hSecondPatch.symm)
      (hSecondMajor.trans hThirdMajor.symm)
      (hSecondMinor.trans hThirdMinor.symm)
      (hSecondPatch.trans hThirdPatch.symm)
      hFirstSecond
      hSecondThird

private theorem prereleaseCore_swap
    (left right reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference) :
    Version.precedence left right =
      (Version.precedence right left).swap := by
  rcases hLeft with
    ⟨hLeftPrerelease, hLeftMajor, hLeftMinor, hLeftPatch⟩
  rcases hRight with
    ⟨hRightPrerelease, hRightMajor, hRightMinor, hRightPatch⟩
  exact
    Version.precedence_prerelease_swap_of_same_core
      left right
      hLeftPrerelease hRightPrerelease
      (hLeftMajor.trans hRightMajor.symm)
      (hLeftMinor.trans hRightMinor.symm)
      (hLeftPatch.trans hRightPatch.symm)

private theorem prereleaseCore_eq_of_isLE_of_reverse_isLE
    (left right reference : Version)
    (hLeft : samePrereleaseCoreAs left reference)
    (hRight : samePrereleaseCoreAs right reference)
    (hLeftRight : (Version.precedence left right).isLE)
    (hRightLeft : (Version.precedence right left).isLE) :
    Version.precedence left right = .eq := by
  have hSwap :=
    prereleaseCore_swap left right reference hLeft hRight
  cases hOrder : Version.precedence left right with
  | lt =>
      have hReverse : Version.precedence right left = .gt := by
        cases hReverse : Version.precedence right left <;>
          simp [hOrder, hReverse] at hSwap ⊢
      simp [hReverse] at hRightLeft
  | eq =>
      rfl
  | gt =>
      simp [hOrder] at hLeftRight

private theorem prereleaseCore_lt_of_isLE_of_lt
    (first second third reference : Version)
    (hFirst : samePrereleaseCoreAs first reference)
    (hSecond : samePrereleaseCoreAs second reference)
    (hThird : samePrereleaseCoreAs third reference)
    (hFirstSecond : (Version.precedence first second).isLE)
    (hSecondThird : Version.precedence second third = .lt) :
    Version.precedence first third = .lt := by
  have hSecondThirdLE :
      (Version.precedence second third).isLE := by
    simp [hSecondThird]
  have hFirstThirdLE :=
    prereleaseCore_isLE_trans
      first second third reference
      hFirst hSecond hThird
      hFirstSecond hSecondThirdLE
  cases hFirstThird : Version.precedence first third with
  | lt =>
      rfl
  | gt =>
      simp [hFirstThird] at hFirstThirdLE
  | eq =>
      have hSwapFirstThird :=
        prereleaseCore_swap first third reference hFirst hThird
      have hThirdFirst :
          Version.precedence third first = .eq := by
        cases hReverse : Version.precedence third first <;>
          simp [hFirstThird, hReverse] at hSwapFirstThird ⊢
      have hThirdFirstLE :
          (Version.precedence third first).isLE := by
        simp [hThirdFirst]
      have hThirdSecondLE :=
        prereleaseCore_isLE_trans
          third first second reference
          hThird hFirst hSecond
          hThirdFirstLE hFirstSecond
      have hSwapSecondThird :=
        prereleaseCore_swap second third reference hSecond hThird
      have hThirdSecond :
          Version.precedence third second = .gt := by
        cases hReverse : Version.precedence third second <;>
          simp [hSecondThird, hReverse] at hSwapSecondThird ⊢
      simp [hThirdSecond] at hThirdSecondLE

private theorem prereleaseCore_lt_of_lt_of_isLE
    (first second third reference : Version)
    (hFirst : samePrereleaseCoreAs first reference)
    (hSecond : samePrereleaseCoreAs second reference)
    (hThird : samePrereleaseCoreAs third reference)
    (hFirstSecond : Version.precedence first second = .lt)
    (hSecondThird : (Version.precedence second third).isLE) :
    Version.precedence first third = .lt := by
  have hFirstSecondLE :
      (Version.precedence first second).isLE := by
    simp [hFirstSecond]
  have hFirstThirdLE :=
    prereleaseCore_isLE_trans
      first second third reference
      hFirst hSecond hThird
      hFirstSecondLE hSecondThird
  cases hFirstThird : Version.precedence first third with
  | lt =>
      rfl
  | gt =>
      simp [hFirstThird] at hFirstThirdLE
  | eq =>
      have hSwapFirstThird :=
        prereleaseCore_swap first third reference hFirst hThird
      have hThirdFirst :
          Version.precedence third first = .eq := by
        cases hReverse : Version.precedence third first <;>
          simp [hFirstThird, hReverse] at hSwapFirstThird ⊢
      have hSecondThirdFirst :=
        prereleaseCore_isLE_trans
          second third first reference
          hSecond hThird hFirst
          hSecondThird
          (by simp [hThirdFirst])
      have hSwapFirstSecond :=
        prereleaseCore_swap first second reference hFirst hSecond
      have hSecondFirst :
          Version.precedence second first = .gt := by
        cases hReverse : Version.precedence second first <;>
          simp [hFirstSecond, hReverse] at hSwapFirstSecond ⊢
      simp [hSecondFirst] at hSecondThirdFirst

private theorem samePrereleaseCoreAs_of_precedence_eq
    (left right : Version)
    (hLeftPrerelease : left.prerelease.isEmpty = false)
    (hEq : Version.precedence left right = .eq) :
    samePrereleaseCoreAs right left := by
  cases hMajor : compare left.major right.major with
  | lt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hEq
  | gt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hEq
  | eq =>
      have hMajorEq : left.major = right.major :=
        Nat.compare_eq_eq.mp hMajor
      cases hMinor : compare left.minor right.minor with
      | lt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hEq
      | gt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hEq
      | eq =>
          have hMinorEq : left.minor = right.minor :=
            Nat.compare_eq_eq.mp hMinor
          cases hPatch : compare left.patch right.patch with
          | lt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hEq
          | gt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hEq
          | eq =>
              have hPatchEq : left.patch = right.patch :=
                Nat.compare_eq_eq.mp hPatch
              cases hLeftList : left.prerelease with
              | nil =>
                  simp [hLeftList] at hLeftPrerelease
              | cons leftHead leftTail =>
                  cases hRightList : right.prerelease with
                  | nil =>
                      have hLt :=
                        Version.precedence_prerelease_lt_stable_of_same_core
                          left right
                          hLeftPrerelease
                          (by simp [hRightList])
                          hMajorEq hMinorEq hPatchEq
                      rw [hEq] at hLt
                      contradiction
                  | cons rightHead rightTail =>
                      exact
                        ⟨by simp [hRightList],
                          hMajorEq.symm,
                          hMinorEq.symm,
                          hPatchEq.symm⟩

private theorem stableCoreLT_of_prerelease_gt_of_not_same_core
    (witness bound : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hGt : Version.precedence witness bound = .gt)
    (hNotCore : ¬ samePrereleaseCoreAs bound witness) :
    stableCoreLT bound witness := by
  by_cases hBoundWitness : stableCoreLT bound witness
  · exact hBoundWitness
  · by_cases hWitnessBound : stableCoreLT witness bound
    · have hLt :=
        precedence_lt_of_stableCoreLT witness bound hWitnessBound
      rw [hGt] at hLt
      contradiction
    · have hMajor : bound.major = witness.major := by
        unfold stableCoreLT at hBoundWitness hWitnessBound
        omega
      have hMinor : bound.minor = witness.minor := by
        unfold stableCoreLT at hBoundWitness hWitnessBound
        omega
      have hPatch : bound.patch = witness.patch := by
        unfold stableCoreLT at hBoundWitness hWitnessBound
        omega
      cases hBoundList : bound.prerelease with
      | nil =>
          cases hWitnessList : witness.prerelease with
          | nil =>
              simp [hWitnessList] at hWitnessPrerelease
          | cons witnessHead witnessTail =>
              have hMajorCompare :
                  compare witness.major bound.major = .eq :=
                Nat.compare_eq_eq.mpr hMajor.symm
              have hMinorCompare :
                  compare witness.minor bound.minor = .eq :=
                Nat.compare_eq_eq.mpr hMinor.symm
              have hPatchCompare :
                  compare witness.patch bound.patch = .eq :=
                Nat.compare_eq_eq.mpr hPatch.symm
              have hLt :=
                Version.precedence_prerelease_lt_stable_of_same_core
                  witness bound
                  hWitnessPrerelease
                  (by simp [hBoundList])
                  hMajor.symm hMinor.symm hPatch.symm
              rw [hGt] at hLt
              contradiction
      | cons boundHead boundTail =>
          have hCore : samePrereleaseCoreAs bound witness :=
            ⟨by simp [hBoundList], hMajor, hMinor, hPatch⟩
          exact (hNotCore hCore).elim

private theorem precedence_lt_of_prerelease_le_witness_lt_bound
    (candidate witness bound : Version)
    (hCandidate : samePrereleaseCoreAs candidate witness)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hCandidateWitness : (Version.precedence candidate witness).isLE)
    (hWitnessBound : Version.precedence witness bound = .lt) :
    Version.precedence candidate bound = .lt := by
  by_cases hWitnessBoundCore : stableCoreLT witness bound
  · rcases hCandidate with
      ⟨hCandidatePrerelease, hMajor, hMinor, hPatch⟩
    have hCandidateBoundCore : stableCoreLT candidate bound := by
      unfold stableCoreLT at hWitnessBoundCore ⊢
      omega
    exact
      precedence_lt_of_stableCoreLT
        candidate bound hCandidateBoundCore
  · by_cases hBoundWitnessCore : stableCoreLT bound witness
    · have hGt :=
        precedence_gt_of_stableCoreLT bound witness hBoundWitnessCore
      rw [hWitnessBound] at hGt
      contradiction
    · have hMajor : bound.major = witness.major := by
        unfold stableCoreLT at hWitnessBoundCore hBoundWitnessCore
        omega
      have hMinor : bound.minor = witness.minor := by
        unfold stableCoreLT at hWitnessBoundCore hBoundWitnessCore
        omega
      have hPatch : bound.patch = witness.patch := by
        unfold stableCoreLT at hWitnessBoundCore hBoundWitnessCore
        omega
      cases hBoundList : bound.prerelease with
      | nil =>
          rcases hCandidate with
            ⟨hCandidatePrerelease, hCandidateMajor, hCandidateMinor, hCandidatePatch⟩
          cases hCandidateList : candidate.prerelease with
          | nil =>
              simp [hCandidateList] at hCandidatePrerelease
          | cons candidateHead candidateTail =>
              have hMajorCompare :
                  compare candidate.major bound.major = .eq :=
                Nat.compare_eq_eq.mpr
                  (hCandidateMajor.trans hMajor.symm)
              have hMinorCompare :
                  compare candidate.minor bound.minor = .eq :=
                Nat.compare_eq_eq.mpr
                  (hCandidateMinor.trans hMinor.symm)
              have hPatchCompare :
                  compare candidate.patch bound.patch = .eq :=
                Nat.compare_eq_eq.mpr
                  (hCandidatePatch.trans hPatch.symm)
              exact
                Version.precedence_prerelease_lt_stable_of_same_core
                  candidate bound
                  hCandidatePrerelease
                  (by simp [hBoundList])
                  (hCandidateMajor.trans hMajor.symm)
                  (hCandidateMinor.trans hMinor.symm)
                  (hCandidatePatch.trans hPatch.symm)
      | cons boundHead boundTail =>
          have hBoundCore : samePrereleaseCoreAs bound witness :=
            ⟨by simp [hBoundList], hMajor, hMinor, hPatch⟩
          exact
            prereleaseCore_lt_of_isLE_of_lt
              candidate witness bound witness
              hCandidate
              ⟨hWitnessPrerelease, rfl, rfl, rfl⟩
              hBoundCore
              hCandidateWitness
              hWitnessBound

/--
Appending numeric zero preserves prerelease status for a prerelease bound.
-/
private theorem prereleaseSuccessor_is_prerelease
    (version : Version)
    (hPrerelease : version.prerelease.isEmpty = false) :
    (prereleaseSuccessor version).prerelease.isEmpty = false := by
  simp [prereleaseSuccessor, strippedBound, hPrerelease]

/--
The generated prerelease successor is strictly above its prerelease bound in
SemVer precedence.
-/
private theorem prereleaseSuccessor_precedence_gt
    (version : Version)
    (hPrerelease : version.prerelease.isEmpty = false) :
    Version.precedence (prereleaseSuccessor version) version = .gt := by
  simpa [
    Version.precedence,
    Version.precedenceKey,
    prereleaseSuccessor,
    strippedBound
  ] using
    PrecedenceKey.ordering_prerelease_append_zero_gt
      version.major
      version.minor
      version.patch
      version.prerelease
      hPrerelease

/--
Finite boundary candidates contributed by one primitive comparator.

Stable candidates include the release at the bound's core and the next patch
release. A prerelease bound additionally contributes the lowest prerelease at
that core, the bound itself, and the immediate prefix extension obtained by
appending numeric zero.

The list may contain duplicates. Keeping generation simple is more important
than deduplication at this stage.
-/
private def boundaryCandidates (comparator : Comparator) : List Version :=
  let bound := comparator.bound
  let stable := stableAtCore bound
  let nextStable := nextStablePatch bound
  if bound.prerelease.isEmpty then
    [stable, nextStable]
  else
    [
      stable,
      nextStable,
      prereleaseFloorAtCore bound,
      strippedBound bound,
      prereleaseSuccessor bound
    ]

/--
The canonical prerelease floor is itself a prerelease.
-/
private theorem prereleaseFloorAtCore_is_prerelease
    (version : Version) :
    (prereleaseFloorAtCore version).prerelease.isEmpty = false := by
  simp [prereleaseFloorAtCore]

/--
The canonical `-0` prerelease floor never lies above a prerelease version on
the same core.
-/
private theorem prereleaseFloorAtCore_precedence_ne_gt
    (version : Version)
    (hPrerelease : version.prerelease.isEmpty = false) :
    Version.precedence (prereleaseFloorAtCore version) version ≠ .gt := by
  simpa [
    Version.precedence,
    Version.precedenceKey,
    prereleaseFloorAtCore
  ] using
    PrecedenceKey.ordering_prerelease_zero_ne_gt
      version.major
      version.minor
      version.patch
      version.prerelease
      hPrerelease

/--
A prerelease comparator bound contributes the prerelease floor at its core to
the existing critical-boundary pool.
-/
private theorem prereleaseFloorAtCore_mem_boundary
    (comparator : Comparator)
    (hPrerelease : comparator.bound.prerelease.isEmpty = false) :
    prereleaseFloorAtCore comparator.bound ∈ boundaryCandidates comparator := by
  simp [boundaryCandidates, hPrerelease]

/--
A prerelease comparator bound contributes both its build-stripped boundary and
its strict prerelease successor to the finite candidate pool.
-/
private theorem prerelease_boundaries_mem_boundary
    (comparator : Comparator)
    (hPrerelease : comparator.bound.prerelease.isEmpty = false) :
    strippedBound comparator.bound ∈ boundaryCandidates comparator ∧
      prereleaseSuccessor comparator.bound ∈ boundaryCandidates comparator := by
  simp [boundaryCandidates, hPrerelease]

/--
One canonical prerelease lower-bound candidate contributed by a comparator
relative to a prerelease witness core.

Only prerelease bounds on the witness core can tighten the prerelease floor.
Strict lower bounds contribute the discrete successor `bound.0`; inclusive
lower bounds and equality contribute the build-stripped bound itself. All
other cases fall back to the canonical `-0` floor on the witness core.
-/
private def prereleaseLowerCandidate
    (comparator : Comparator)
    (witness : Version) : Version :=
  match comparator.operator with
  | .gt =>
      if samePrereleaseCoreAs comparator.bound witness then
        prereleaseSuccessor comparator.bound
      else
        prereleaseFloorAtCore witness
  | .gte | .eq =>
      if samePrereleaseCoreAs comparator.bound witness then
        strippedBound comparator.bound
      else
        prereleaseFloorAtCore witness
  | .lt | .lte =>
      prereleaseFloorAtCore witness

private theorem prereleaseFloorAtCore_same_core_as
    (reference : Version) :
    samePrereleaseCoreAs
      (prereleaseFloorAtCore reference)
      reference := by
  simp [samePrereleaseCoreAs, prereleaseFloorAtCore]

private theorem strippedBound_same_core_as
    (bound reference : Version)
    (hCore : samePrereleaseCoreAs bound reference) :
    samePrereleaseCoreAs (strippedBound bound) reference := by
  simpa [samePrereleaseCoreAs, strippedBound] using hCore

private theorem prereleaseSuccessor_same_core_as
    (bound reference : Version)
    (hCore : samePrereleaseCoreAs bound reference) :
    samePrereleaseCoreAs
      (prereleaseSuccessor bound)
      reference := by
  rcases hCore with
    ⟨hPrerelease, hMajor, hMinor, hPatch⟩
  exact
    ⟨prereleaseSuccessor_is_prerelease bound hPrerelease,
      by simpa [prereleaseSuccessor, strippedBound] using hMajor,
      by simpa [prereleaseSuccessor, strippedBound] using hMinor,
      by simpa [prereleaseSuccessor, strippedBound] using hPatch⟩

/--
Every prerelease lower candidate remains on the witness core.
-/
private theorem prereleaseLowerCandidate_same_core_as
    (comparator : Comparator)
    (witness : Version) :
    samePrereleaseCoreAs
      (prereleaseLowerCandidate comparator witness)
      witness := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          exact prereleaseFloorAtCore_same_core_as witness
      | lte =>
          exact prereleaseFloorAtCore_same_core_as witness
      | gt =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · simpa [prereleaseLowerCandidate, hCore] using
              prereleaseSuccessor_same_core_as bound witness hCore
          · simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_same_core_as witness
      | gte =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · simpa [prereleaseLowerCandidate, hCore] using
              strippedBound_same_core_as bound witness hCore
          · simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_same_core_as witness
      | eq =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · simpa [prereleaseLowerCandidate, hCore] using
              strippedBound_same_core_as bound witness hCore
          · simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_same_core_as witness

/--
Each prerelease lower candidate is either the shared witness-core floor or an
existing boundary candidate contributed by its comparator.
-/
private theorem prereleaseLowerCandidate_eq_floor_or_mem_boundary
    (comparator : Comparator)
    (witness : Version) :
    prereleaseLowerCandidate comparator witness =
        prereleaseFloorAtCore witness ∨
      prereleaseLowerCandidate comparator witness ∈
        boundaryCandidates comparator := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          exact Or.inl (by simp [prereleaseLowerCandidate])
      | lte =>
          exact Or.inl (by simp [prereleaseLowerCandidate])
      | gt =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · have hPrerelease :
                bound.prerelease.isEmpty = false := hCore.1
            have hMem :=
              (prerelease_boundaries_mem_boundary
                { operator := .gt, bound := bound }
                hPrerelease).2
            exact Or.inr (by
              simpa [prereleaseLowerCandidate, hCore] using hMem)
          · exact Or.inl (by
              simp [prereleaseLowerCandidate, hCore])
      | gte =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · have hPrerelease :
                bound.prerelease.isEmpty = false := hCore.1
            have hMem :=
              (prerelease_boundaries_mem_boundary
                { operator := .gte, bound := bound }
                hPrerelease).1
            exact Or.inr (by
              simpa [prereleaseLowerCandidate, hCore] using hMem)
          · exact Or.inl (by
              simp [prereleaseLowerCandidate, hCore])
      | eq =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · have hPrerelease :
                bound.prerelease.isEmpty = false := hCore.1
            have hMem :=
              (prerelease_boundaries_mem_boundary
                { operator := .eq, bound := bound }
                hPrerelease).1
            exact Or.inr (by
              simpa [prereleaseLowerCandidate, hCore] using hMem)
          · exact Or.inl (by
              simp [prereleaseLowerCandidate, hCore])

private theorem ordering_isLE_of_ne_gt
    (order : Ordering)
    (hOrder : order ≠ .gt) :
    order.isLE := by
  cases h : order <;> simp_all

/--
A prerelease lower candidate never lies above a prerelease witness that
satisfies its source comparator.
-/
private theorem prereleaseLowerCandidate_isLE_of_satisfies
    (comparator : Comparator)
    (witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hSatisfies : comparator.satisfies witness = true) :
    (Version.precedence
      (prereleaseLowerCandidate comparator witness)
      witness).isLE := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          apply ordering_isLE_of_ne_gt
          simpa [prereleaseLowerCandidate] using
            prereleaseFloorAtCore_precedence_ne_gt
              witness hWitnessPrerelease
      | lte =>
          apply ordering_isLE_of_ne_gt
          simpa [prereleaseLowerCandidate] using
            prereleaseFloorAtCore_precedence_ne_gt
              witness hWitnessPrerelease
      | gt =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · rcases hCore with
              ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
            have hGt :
                Version.precedence witness bound = .gt := by
              cases hPrecedence :
                  Version.precedence witness bound with
              | lt =>
                  simp [Comparator.satisfies, hPrecedence] at hSatisfies
              | eq =>
                  simp [Comparator.satisfies, hPrecedence] at hSatisfies
              | gt =>
                  rfl
            have hGtKey :
                PrecedenceKey.ordering
                    {
                      major := bound.major
                      minor := bound.minor
                      patch := bound.patch
                      prerelease := witness.prerelease
                    }
                    {
                      major := bound.major
                      minor := bound.minor
                      patch := bound.patch
                      prerelease := bound.prerelease
                    } = .gt := by
              simpa [
                Version.precedence,
                Version.precedenceKey,
                hMajor.symm,
                hMinor.symm,
                hPatch.symm
              ] using hGt
            have hNotGtKey :=
              PrecedenceKey.ordering_prerelease_append_zero_ne_gt_of_gt
                bound.major
                bound.minor
                bound.patch
                bound.prerelease
                witness.prerelease
                hBoundPrerelease
                hWitnessPrerelease
                hGtKey
            have hNotGt :
                Version.precedence
                    (prereleaseSuccessor bound)
                    witness ≠ .gt := by
              simpa [
                Version.precedence,
                Version.precedenceKey,
                prereleaseSuccessor,
                strippedBound,
                hMajor.symm,
                hMinor.symm,
                hPatch.symm
              ] using hNotGtKey
            have hCore' :
                samePrereleaseCoreAs bound witness :=
              ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
            apply ordering_isLE_of_ne_gt
            simpa [prereleaseLowerCandidate, hCore'] using hNotGt
          · apply ordering_isLE_of_ne_gt
            simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_precedence_ne_gt
                witness hWitnessPrerelease
      | gte =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · rcases hCore with
              ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
            have hSwap :=
              Version.precedence_prerelease_swap_of_same_core
                witness bound
                hWitnessPrerelease hBoundPrerelease
                hMajor.symm hMinor.symm hPatch.symm
            cases hPrecedence :
                Version.precedence witness bound with
            | lt =>
                simp [Comparator.satisfies, hPrecedence] at hSatisfies
            | eq =>
                have hReverse :
                    Version.precedence bound witness = .eq := by
                  cases hReverse :
                      Version.precedence bound witness <;>
                    simp [hPrecedence, hReverse] at hSwap ⊢
                have hCore' :
                    samePrereleaseCoreAs bound witness :=
                  ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
                have hCandidate :
                    prereleaseLowerCandidate
                        { operator := .gte, bound := bound }
                        witness =
                      strippedBound bound := by
                  simp [prereleaseLowerCandidate, hCore']
                have hStripped :
                    Version.precedence (strippedBound bound) witness =
                      Version.precedence bound witness := by
                  rfl
                rw [hCandidate, hStripped, hReverse]
                rfl
            | gt =>
                have hReverse :
                    Version.precedence bound witness = .lt := by
                  cases hReverse :
                      Version.precedence bound witness <;>
                    simp [hPrecedence, hReverse] at hSwap ⊢
                have hCore' :
                    samePrereleaseCoreAs bound witness :=
                  ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
                have hCandidate :
                    prereleaseLowerCandidate
                        { operator := .gte, bound := bound }
                        witness =
                      strippedBound bound := by
                  simp [prereleaseLowerCandidate, hCore']
                have hStripped :
                    Version.precedence (strippedBound bound) witness =
                      Version.precedence bound witness := by
                  rfl
                rw [hCandidate, hStripped, hReverse]
                rfl
          · apply ordering_isLE_of_ne_gt
            simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_precedence_ne_gt
                witness hWitnessPrerelease
      | eq =>
          by_cases hCore : samePrereleaseCoreAs bound witness
          · rcases hCore with
              ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
            have hEq :
                Version.precedence witness bound = .eq := by
              cases hPrecedence :
                  Version.precedence witness bound with
              | lt =>
                  simp [Comparator.satisfies, hPrecedence] at hSatisfies
              | eq =>
                  rfl
              | gt =>
                  simp [Comparator.satisfies, hPrecedence] at hSatisfies
            have hSwap :=
              Version.precedence_prerelease_swap_of_same_core
                witness bound
                hWitnessPrerelease hBoundPrerelease
                hMajor.symm hMinor.symm hPatch.symm
            have hReverse :
                Version.precedence bound witness = .eq := by
              cases hReverse :
                  Version.precedence bound witness <;>
                simp [hEq, hReverse] at hSwap ⊢
            have hCore' :
                samePrereleaseCoreAs bound witness :=
              ⟨hBoundPrerelease, hMajor, hMinor, hPatch⟩
            have hCandidate :
                prereleaseLowerCandidate
                    { operator := .eq, bound := bound }
                    witness =
                  strippedBound bound := by
              simp [prereleaseLowerCandidate, hCore']
            have hStripped :
                Version.precedence (strippedBound bound) witness =
                  Version.precedence bound witness := by
              rfl
            rw [hCandidate, hStripped, hReverse]
            rfl
          · apply ordering_isLE_of_ne_gt
            simpa [prereleaseLowerCandidate, hCore] using
              prereleaseFloorAtCore_precedence_ne_gt
                witness hWitnessPrerelease

/--
A prerelease candidate between a comparator's canonical lower boundary and an
existing same-core prerelease witness also satisfies that comparator.
-/
private theorem comparator_satisfies_prerelease_sandwich
    (comparator : Comparator)
    (candidate witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hCandidateCore : samePrereleaseCoreAs candidate witness)
    (hFloorCandidate :
      (Version.precedence
        (prereleaseLowerCandidate comparator witness)
        candidate).isLE)
    (hCandidateWitness :
      (Version.precedence candidate witness).isLE)
    (hWitnessSatisfies : comparator.satisfies witness = true) :
    comparator.satisfies candidate = true := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          have hWitnessLt :
              Version.precedence witness bound = .lt := by
            cases hPrecedence : Version.precedence witness bound with
            | lt =>
                rfl
            | eq =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | gt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
          have hCandidateLt :=
            precedence_lt_of_prerelease_le_witness_lt_bound
              candidate witness bound
              hCandidateCore hWitnessPrerelease
              hCandidateWitness hWitnessLt
          simp [Comparator.satisfies, hCandidateLt]
      | lte =>
          cases hWitnessPrecedence : Version.precedence witness bound with
          | gt =>
              simp [Comparator.satisfies, hWitnessPrecedence] at hWitnessSatisfies
          | lt =>
              have hCandidateLt :=
                precedence_lt_of_prerelease_le_witness_lt_bound
                  candidate witness bound
                  hCandidateCore hWitnessPrerelease
                  hCandidateWitness hWitnessPrecedence
              simp [Comparator.satisfies, hCandidateLt]
          | eq =>
              have hBoundCore :=
                samePrereleaseCoreAs_of_precedence_eq
                  witness bound hWitnessPrerelease hWitnessPrecedence
              have hCandidateBoundLE :=
                prereleaseCore_isLE_trans
                  candidate witness bound witness
                  hCandidateCore
                  ⟨hWitnessPrerelease, rfl, rfl, rfl⟩
                  hBoundCore
                  hCandidateWitness
                  (by simp [hWitnessPrecedence])
              cases hCandidatePrecedence :
                  Version.precedence candidate bound with
              | lt =>
                  simp [Comparator.satisfies, hCandidatePrecedence]
              | eq =>
                  simp [Comparator.satisfies, hCandidatePrecedence]
              | gt =>
                  simp [hCandidatePrecedence] at hCandidateBoundLE
      | gt =>
          have hWitnessGt :
              Version.precedence witness bound = .gt := by
            cases hPrecedence : Version.precedence witness bound with
            | lt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | eq =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | gt =>
                rfl
          by_cases hBoundCore : samePrereleaseCoreAs bound witness
          · have hSuccessorCore :=
              prereleaseSuccessor_same_core_as
                bound witness hBoundCore
            have hSuccessorCandidate :
                (Version.precedence
                  (prereleaseSuccessor bound)
                  candidate).isLE := by
              simpa [prereleaseLowerCandidate, hBoundCore] using
                hFloorCandidate
            have hSuccessorGt :=
              prereleaseSuccessor_precedence_gt
                bound hBoundCore.1
            have hSwap :=
              prereleaseCore_swap
                bound (prereleaseSuccessor bound) witness
                hBoundCore hSuccessorCore
            have hBoundSuccessorLt :
                Version.precedence bound (prereleaseSuccessor bound) = .lt := by
              cases hForward :
                  Version.precedence bound (prereleaseSuccessor bound) <;>
                simp [hForward, hSuccessorGt] at hSwap ⊢
            have hBoundCandidateLt :=
              prereleaseCore_lt_of_lt_of_isLE
                bound (prereleaseSuccessor bound) candidate witness
                hBoundCore hSuccessorCore hCandidateCore
                hBoundSuccessorLt hSuccessorCandidate
            have hSwapCandidate :=
              prereleaseCore_swap
                bound candidate witness
                hBoundCore hCandidateCore
            have hCandidateGt :
                Version.precedence candidate bound = .gt := by
              cases hReverse : Version.precedence candidate bound <;>
                simp [hBoundCandidateLt, hReverse] at hSwapCandidate ⊢
            simp [Comparator.satisfies, hCandidateGt]
          · have hBoundWitnessCore :=
              stableCoreLT_of_prerelease_gt_of_not_same_core
                witness bound hWitnessPrerelease
                hWitnessGt hBoundCore
            rcases hCandidateCore with
              ⟨hCandidatePrerelease, hMajor, hMinor, hPatch⟩
            have hBoundCandidateCore : stableCoreLT bound candidate := by
              unfold stableCoreLT at hBoundWitnessCore ⊢
              omega
            have hCandidateGt :=
              precedence_gt_of_stableCoreLT
                bound candidate hBoundCandidateCore
            simp [Comparator.satisfies, hCandidateGt]
      | gte =>
          cases hWitnessPrecedence : Version.precedence witness bound with
          | lt =>
              simp [Comparator.satisfies, hWitnessPrecedence] at hWitnessSatisfies
          | eq =>
              have hBoundCore :=
                samePrereleaseCoreAs_of_precedence_eq
                  witness bound hWitnessPrerelease hWitnessPrecedence
              have hBoundCandidateLE :
                  (Version.precedence bound candidate).isLE := by
                have hLower :
                    prereleaseLowerCandidate
                        { operator := .gte, bound := bound }
                        witness =
                      strippedBound bound := by
                  simp [prereleaseLowerCandidate, hBoundCore]
                rw [hLower] at hFloorCandidate
                simpa [strippedBound] using hFloorCandidate
              have hSwap :=
                prereleaseCore_swap
                  candidate bound witness
                  hCandidateCore hBoundCore
              cases hCandidatePrecedence :
                  Version.precedence candidate bound with
              | lt =>
                  have hReverse :
                      Version.precedence bound candidate = .gt := by
                    cases hReverse :
                        Version.precedence bound candidate <;>
                      simp [hCandidatePrecedence, hReverse] at hSwap ⊢
                  simp [hReverse] at hBoundCandidateLE
              | eq =>
                  simp [Comparator.satisfies, hCandidatePrecedence]
              | gt =>
                  simp [Comparator.satisfies, hCandidatePrecedence]
          | gt =>
              by_cases hBoundCore : samePrereleaseCoreAs bound witness
              · have hBoundCandidateLE :
                    (Version.precedence bound candidate).isLE := by
                  have hLower :
                      prereleaseLowerCandidate
                          { operator := .gte, bound := bound }
                          witness =
                        strippedBound bound := by
                    simp [prereleaseLowerCandidate, hBoundCore]
                  rw [hLower] at hFloorCandidate
                  simpa [strippedBound] using hFloorCandidate
                have hSwap :=
                  prereleaseCore_swap
                    candidate bound witness
                    hCandidateCore hBoundCore
                cases hCandidatePrecedence :
                    Version.precedence candidate bound with
                | lt =>
                    have hReverse :
                        Version.precedence bound candidate = .gt := by
                      cases hReverse :
                          Version.precedence bound candidate <;>
                        simp [hCandidatePrecedence, hReverse] at hSwap ⊢
                    simp [hReverse] at hBoundCandidateLE
                | eq =>
                    simp [Comparator.satisfies, hCandidatePrecedence]
                | gt =>
                    simp [Comparator.satisfies, hCandidatePrecedence]
              · have hBoundWitnessCore :=
                  stableCoreLT_of_prerelease_gt_of_not_same_core
                    witness bound hWitnessPrerelease
                    hWitnessPrecedence hBoundCore
                rcases hCandidateCore with
                  ⟨hCandidatePrerelease, hMajor, hMinor, hPatch⟩
                have hBoundCandidateCore : stableCoreLT bound candidate := by
                  unfold stableCoreLT at hBoundWitnessCore ⊢
                  omega
                have hCandidateGt :=
                  precedence_gt_of_stableCoreLT
                    bound candidate hBoundCandidateCore
                simp [Comparator.satisfies, hCandidateGt]
      | eq =>
          have hWitnessEq :
              Version.precedence witness bound = .eq := by
            cases hPrecedence : Version.precedence witness bound with
            | lt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | eq =>
                rfl
            | gt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
          have hBoundCore :=
            samePrereleaseCoreAs_of_precedence_eq
              witness bound hWitnessPrerelease hWitnessEq
          have hCandidateBoundLE :=
            prereleaseCore_isLE_trans
              candidate witness bound witness
              hCandidateCore
              ⟨hWitnessPrerelease, rfl, rfl, rfl⟩
              hBoundCore
              hCandidateWitness
              (by simp [hWitnessEq])
          have hBoundCandidateLE :
              (Version.precedence bound candidate).isLE := by
            have hLower :
                prereleaseLowerCandidate
                    { operator := .eq, bound := bound }
                    witness =
                  strippedBound bound := by
              simp [prereleaseLowerCandidate, hBoundCore]
            rw [hLower] at hFloorCandidate
            simpa [strippedBound] using hFloorCandidate
          have hCandidateEq :=
            prereleaseCore_eq_of_isLE_of_reverse_isLE
              candidate bound witness
              hCandidateCore hBoundCore
              hCandidateBoundLE hBoundCandidateLE
          simp [Comparator.satisfies, hCandidateEq]

/--
Strongest canonical prerelease lower boundary contributed by a finite
comparator list on one witness core.
-/
private def prereleaseLowerMaximum :
    List Comparator → Version → Version
  | [], witness =>
      prereleaseFloorAtCore witness
  | comparator :: rest, witness =>
      prereleaseCoreMax
        (prereleaseLowerCandidate comparator witness)
        (prereleaseLowerMaximum rest witness)

private theorem prereleaseLowerMaximum_same_core_as
    (comparators : List Comparator)
    (witness : Version) :
    samePrereleaseCoreAs
      (prereleaseLowerMaximum comparators witness)
      witness := by
  induction comparators with
  | nil =>
      simpa [prereleaseLowerMaximum] using
        prereleaseFloorAtCore_same_core_as witness
  | cons comparator rest ih =>
      simp only [prereleaseLowerMaximum]
      exact
        prereleaseCoreMax_same_core_as
          (prereleaseLowerCandidate comparator witness)
          (prereleaseLowerMaximum rest witness)
          witness
          (prereleaseLowerCandidate_same_core_as
            comparator witness)
          ih

private theorem prereleaseLowerCandidate_isLE_maximum_of_mem
    (comparators : List Comparator)
    (comparator : Comparator)
    (witness : Version)
    (hComparator : comparator ∈ comparators) :
    (Version.precedence
      (prereleaseLowerCandidate comparator witness)
      (prereleaseLowerMaximum comparators witness)).isLE := by
  induction comparators with
  | nil =>
      simp at hComparator
  | cons head tail ih =>
      rcases List.mem_cons.mp hComparator with hEq | hTail
      · subst comparator
        simp only [prereleaseLowerMaximum]
        exact
          prereleaseCoreMax_left_isLE
            (prereleaseLowerCandidate head witness)
            (prereleaseLowerMaximum tail witness)
            witness
            (prereleaseLowerCandidate_same_core_as head witness)
            (prereleaseLowerMaximum_same_core_as tail witness)
      · have hCandidateTail :=
          ih hTail
        have hTailMaximum :=
          prereleaseCoreMax_right_isLE
            (prereleaseLowerCandidate head witness)
            (prereleaseLowerMaximum tail witness)
            witness
            (prereleaseLowerCandidate_same_core_as head witness)
            (prereleaseLowerMaximum_same_core_as tail witness)
        have hMaximumCore :=
          prereleaseCoreMax_same_core_as
            (prereleaseLowerCandidate head witness)
            (prereleaseLowerMaximum tail witness)
            witness
            (prereleaseLowerCandidate_same_core_as head witness)
            (prereleaseLowerMaximum_same_core_as tail witness)
        exact
          prereleaseCore_isLE_trans
            (prereleaseLowerCandidate comparator witness)
            (prereleaseLowerMaximum tail witness)
            (prereleaseLowerMaximum (head :: tail) witness)
            witness
            (prereleaseLowerCandidate_same_core_as comparator witness)
            (prereleaseLowerMaximum_same_core_as tail witness)
            (by
              simpa [prereleaseLowerMaximum] using hMaximumCore)
            hCandidateTail
            (by
              simpa [prereleaseLowerMaximum] using hTailMaximum)

private theorem prereleaseLowerMaximum_isLE_witness
    (comparators : List Comparator)
    (witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hSatisfies :
      ∀ comparator ∈ comparators,
        comparator.satisfies witness = true) :
    (Version.precedence
      (prereleaseLowerMaximum comparators witness)
      witness).isLE := by
  induction comparators with
  | nil =>
      apply ordering_isLE_of_ne_gt
      simpa [prereleaseLowerMaximum] using
        prereleaseFloorAtCore_precedence_ne_gt
          witness hWitnessPrerelease
  | cons comparator rest ih =>
      simp only [prereleaseLowerMaximum]
      have hLeftUpper :=
        prereleaseLowerCandidate_isLE_of_satisfies
          comparator
          witness
          hWitnessPrerelease
          (hSatisfies comparator List.mem_cons_self)
      have hRightUpper := by
        apply ih
        intro tailComparator hTail
        exact
          hSatisfies tailComparator
            (List.mem_cons_of_mem comparator hTail)
      exact
        prereleaseCoreMax_isLE
          (prereleaseLowerCandidate comparator witness)
          (prereleaseLowerMaximum rest witness)
          witness
          witness
          (prereleaseLowerCandidate_same_core_as
            comparator witness)
          (prereleaseLowerMaximum_same_core_as
            rest witness)
          ⟨hWitnessPrerelease, rfl, rfl, rfl⟩
          hLeftUpper
          hRightUpper

private theorem prereleaseLowerMaximum_eq_floor_or_exists_lower
    (comparators : List Comparator)
    (witness : Version) :
    prereleaseLowerMaximum comparators witness =
        prereleaseFloorAtCore witness ∨
      ∃ comparator ∈ comparators,
        prereleaseLowerMaximum comparators witness =
          prereleaseLowerCandidate comparator witness := by
  induction comparators with
  | nil =>
      exact Or.inl (by simp [prereleaseLowerMaximum])
  | cons head tail ih =>
      rcases
          prereleaseCoreMax_eq_left_or_right
            (prereleaseLowerCandidate head witness)
            (prereleaseLowerMaximum tail witness) with
        hMax | hMax
      · exact
          Or.inr
            ⟨head,
              List.mem_cons_self,
              by simpa [prereleaseLowerMaximum] using hMax⟩
      · rcases ih with hFloor | ⟨comparator, hComparator, hLower⟩
        · exact
            Or.inl
              (by
                simp only [prereleaseLowerMaximum]
                rw [hMax]
                exact hFloor)
        · exact
            Or.inr
              ⟨comparator,
                List.mem_cons_of_mem head hComparator,
                by
                  simp only [prereleaseLowerMaximum]
                  rw [hMax]
                  exact hLower⟩

/--
One canonical stable lower-bound candidate contributed by a comparator.

Upper-only comparators contribute the global minimum stable release. Inclusive
lower bounds and equality contribute the stable release at the bound's core.
A strict lower bound on a stable release advances one patch; a strict lower
bound on a prerelease can use the stable release at the same core.
-/
private def stableFloorCandidate (comparator : Comparator) : Version :=
  match comparator.operator with
  | .lt | .lte => minimumStable
  | .gte | .eq => stableAtCore comparator.bound
  | .gt =>
      if comparator.bound.prerelease.isEmpty then
        nextStablePatch comparator.bound
      else
        stableAtCore comparator.bound

/--
If semantic precedence does not place `right` below `left`, the core of
`left` is no greater than the core of `right`.

This forgets prerelease ordering exactly when only the stable core order is
needed.
-/
private theorem stableCoreLE_of_precedence_ne_lt
    (left right : Version)
    (hPrecedence : Version.precedence right left ≠ .lt) :
    stableCoreLE left right := by
  cases hMajor : compare right.major left.major with
  | lt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hPrecedence
  | eq =>
      have hMajorEq : right.major = left.major :=
        Nat.compare_eq_eq.mp hMajor
      cases hMinor : compare right.minor left.minor with
      | lt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hPrecedence
      | eq =>
          have hMinorEq : right.minor = left.minor :=
            Nat.compare_eq_eq.mp hMinor
          cases hPatch : compare right.patch left.patch with
          | lt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hPrecedence
          | eq =>
              have hPatchEq : right.patch = left.patch :=
                Nat.compare_eq_eq.mp hPatch
              unfold stableCoreLE
              omega
          | gt =>
              have hPatchGt : left.patch < right.patch :=
                Nat.compare_eq_gt.mp hPatch
              unfold stableCoreLE
              omega
      | gt =>
          have hMinorGt : left.minor < right.minor :=
            Nat.compare_eq_gt.mp hMinor
          unfold stableCoreLE
          omega
  | gt =>
      have hMajorGt : left.major < right.major :=
        Nat.compare_eq_gt.mp hMajor
      unfold stableCoreLE
      omega

/--
A strict comparison above a stable bound must advance far enough in core order
to reach at least the next stable patch.
-/
private theorem nextStablePatch_core_le_of_precedence_gt_of_stable_bound
    (bound candidate : Version)
    (hBoundStable : bound.prerelease.isEmpty = true)
    (hPrecedence : Version.precedence candidate bound = .gt) :
    stableCoreLE (nextStablePatch bound) candidate := by
  have hBoundPrerelease : bound.prerelease = [] := by
    cases hPrerelease : bound.prerelease with
    | nil =>
        rfl
    | cons head tail =>
        simp [hPrerelease] at hBoundStable
  cases hMajor : compare candidate.major bound.major with
  | lt =>
      simp [
        Version.precedence,
        Version.precedenceKey,
        PrecedenceKey.ordering,
        hMajor
      ] at hPrecedence
  | eq =>
      have hMajorEq : candidate.major = bound.major :=
        Nat.compare_eq_eq.mp hMajor
      cases hMinor : compare candidate.minor bound.minor with
      | lt =>
          simp [
            Version.precedence,
            Version.precedenceKey,
            PrecedenceKey.ordering,
            hMajor,
            hMinor
          ] at hPrecedence
      | eq =>
          have hMinorEq : candidate.minor = bound.minor :=
            Nat.compare_eq_eq.mp hMinor
          cases hPatch : compare candidate.patch bound.patch with
          | lt =>
              simp [
                Version.precedence,
                Version.precedenceKey,
                PrecedenceKey.ordering,
                hMajor,
                hMinor,
                hPatch
              ] at hPrecedence
          | eq =>
              have hPatchEq : candidate.patch = bound.patch :=
                Nat.compare_eq_eq.mp hPatch
              cases hCandidatePrerelease : candidate.prerelease with
              | nil =>
                  have hEqPrecedence :
                      Version.precedence candidate bound = .eq := by
                    simp only [
                      Version.precedence,
                      Version.precedenceKey,
                      PrecedenceKey.ordering
                    ]
                    rw [hMajor, hMinor, hPatch]
                    rw [hCandidatePrerelease, hBoundPrerelease]
                    rfl
                  rw [hEqPrecedence] at hPrecedence
                  contradiction
              | cons head tail =>
                  have hLtPrecedence :
                      Version.precedence candidate bound = .lt := by
                    simp only [
                      Version.precedence,
                      Version.precedenceKey,
                      PrecedenceKey.ordering
                    ]
                    rw [hMajor, hMinor, hPatch]
                    rw [hCandidatePrerelease, hBoundPrerelease]
                    rfl
                  rw [hLtPrecedence] at hPrecedence
                  contradiction
          | gt =>
              have hPatchGt : bound.patch < candidate.patch :=
                Nat.compare_eq_gt.mp hPatch
              simp only [stableCoreLE, nextStablePatch]
              omega
      | gt =>
          have hMinorGt : bound.minor < candidate.minor :=
            Nat.compare_eq_gt.mp hMinor
          simp only [stableCoreLE, nextStablePatch]
          omega
  | gt =>
      have hMajorGt : bound.major < candidate.major :=
        Nat.compare_eq_gt.mp hMajor
      simp only [stableCoreLE, nextStablePatch]
      omega

/--
Any candidate satisfying a primitive comparator lies at or above that
comparator's canonical stable floor in core order.
-/
private theorem stableFloorCandidate_core_le_of_satisfies
    (comparator : Comparator)
    (candidate : Version)
    (hSatisfies : comparator.satisfies candidate = true) :
    stableCoreLE (stableFloorCandidate comparator) candidate := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          simpa [stableFloorCandidate] using
            minimumStable_core_le candidate
      | lte =>
          simpa [stableFloorCandidate] using
            minimumStable_core_le candidate
      | gte =>
          have hNotLt : Version.precedence candidate bound ≠ .lt := by
            intro hLt
            simp [Comparator.satisfies, hLt] at hSatisfies
          simpa [stableFloorCandidate, stableAtCore, stableCoreLE] using
            stableCoreLE_of_precedence_ne_lt bound candidate hNotLt
      | eq =>
          have hNotLt : Version.precedence candidate bound ≠ .lt := by
            intro hLt
            simp [Comparator.satisfies, hLt] at hSatisfies
          simpa [stableFloorCandidate, stableAtCore, stableCoreLE] using
            stableCoreLE_of_precedence_ne_lt bound candidate hNotLt
      | gt =>
          cases hBoundStable : bound.prerelease.isEmpty with
          | false =>
              have hNotLt : Version.precedence candidate bound ≠ .lt := by
                intro hLt
                simp [Comparator.satisfies, hLt] at hSatisfies
              simpa [
                stableFloorCandidate,
                hBoundStable,
                stableAtCore,
                stableCoreLE
              ] using
                stableCoreLE_of_precedence_ne_lt bound candidate hNotLt
          | true =>
              have hGt : Version.precedence candidate bound = .gt := by
                cases hPrecedence : Version.precedence candidate bound with
                | lt =>
                    simp [Comparator.satisfies, hPrecedence] at hSatisfies
                | eq =>
                    simp [Comparator.satisfies, hPrecedence] at hSatisfies
                | gt =>
                    rfl
              simpa [stableFloorCandidate, hBoundStable] using
                nextStablePatch_core_le_of_precedence_gt_of_stable_bound
                  bound candidate hBoundStable hGt

/--
If a comparator set accepts a candidate, every comparator floor in that set is
at or below the candidate's core.
-/
private theorem stableFloorCandidate_core_le_of_set_satisfies
    (set : ComparatorSet)
    (candidate : Version)
    (hSet : set.satisfies candidate = true)
    (comparator : Comparator)
    (hComparator : comparator ∈ set.comparators) :
    stableCoreLE (stableFloorCandidate comparator) candidate := by
  have hPrimitive :
      comparator.satisfies candidate = true :=
    ((ComparatorSet.satisfies_eq_true_iff set candidate).mp hSet).1
      comparator hComparator
  exact
    stableFloorCandidate_core_le_of_satisfies
      comparator candidate hPrimitive

/--
A stable candidate between a comparator's canonical floor and an existing
stable witness also satisfies that comparator.
-/
private theorem comparator_satisfies_stable_sandwich
    (comparator : Comparator)
    (candidate witness : Version)
    (hCandidateStable : candidate.prerelease.isEmpty = true)
    (hWitnessStable : witness.prerelease.isEmpty = true)
    (hFloorCandidate :
      stableCoreLE (stableFloorCandidate comparator) candidate)
    (hCandidateWitness : stableCoreLE candidate witness)
    (hWitnessSatisfies : comparator.satisfies witness = true) :
    comparator.satisfies candidate = true := by
  cases comparator with
  | mk operator bound =>
      cases operator with
      | lt =>
          have hWitnessLt :
              Version.precedence witness bound = .lt := by
            cases hPrecedence : Version.precedence witness bound with
            | lt =>
                rfl
            | eq =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | gt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
          have hWitnessCoreLt :=
            stableCoreLT_of_precedence_lt_of_stable
              witness bound hWitnessStable hWitnessLt
          have hCandidateCoreLt :=
            stableCoreLT_of_le_of_lt
              candidate witness bound
              hCandidateWitness hWitnessCoreLt
          have hCandidateLt :=
            precedence_lt_of_stableCoreLT
              candidate bound hCandidateCoreLt
          simp [Comparator.satisfies, hCandidateLt]
      | lte =>
          cases hWitnessPrecedence :
              Version.precedence witness bound with
          | gt =>
              simp [
                Comparator.satisfies,
                hWitnessPrecedence
              ] at hWitnessSatisfies
          | lt =>
              have hWitnessCoreLt :=
                stableCoreLT_of_precedence_lt_of_stable
                  witness bound hWitnessStable hWitnessPrecedence
              have hCandidateCoreLt :=
                stableCoreLT_of_le_of_lt
                  candidate witness bound
                  hCandidateWitness hWitnessCoreLt
              have hCandidateLt :=
                precedence_lt_of_stableCoreLT
                  candidate bound hCandidateCoreLt
              simp [Comparator.satisfies, hCandidateLt]
          | eq =>
              rcases
                  stable_bound_and_same_core_of_precedence_eq
                    witness bound hWitnessStable hWitnessPrecedence with
                ⟨hBoundStable, hMajor, hMinor, hPatch⟩
              have hCandidateBound :
                  stableCoreLE candidate bound := by
                unfold stableCoreLE at hCandidateWitness ⊢
                omega
              by_cases hStrict : stableCoreLT candidate bound
              · have hCandidateLt :=
                  precedence_lt_of_stableCoreLT
                    candidate bound hStrict
                simp [Comparator.satisfies, hCandidateLt]
              · have hCandidateMajor :
                    candidate.major = bound.major := by
                  unfold stableCoreLE at hCandidateBound
                  unfold stableCoreLT at hStrict
                  omega
                have hCandidateMinor :
                    candidate.minor = bound.minor := by
                  unfold stableCoreLE at hCandidateBound
                  unfold stableCoreLT at hStrict
                  omega
                have hCandidatePatch :
                    candidate.patch = bound.patch := by
                  unfold stableCoreLE at hCandidateBound
                  unfold stableCoreLT at hStrict
                  omega
                have hCandidateEq :=
                  precedence_eq_of_stable_same_core
                    candidate bound
                    hCandidateStable hBoundStable
                    hCandidateMajor hCandidateMinor hCandidatePatch
                simp [Comparator.satisfies, hCandidateEq]
      | gt =>
          cases hBoundStable : bound.prerelease.isEmpty with
          | false =>
              have hBoundCandidate :
                  stableCoreLE bound candidate := by
                simpa [
                  stableFloorCandidate,
                  hBoundStable,
                  stableAtCore,
                  stableCoreLE
                ] using hFloorCandidate
              have hNotLt :
                  Version.precedence candidate bound ≠ .lt := by
                intro hLt
                have hCandidateBoundLt :=
                  stableCoreLT_of_precedence_lt_of_stable
                    candidate bound hCandidateStable hLt
                unfold stableCoreLE at hBoundCandidate
                unfold stableCoreLT at hCandidateBoundLt
                omega
              cases hCandidatePrecedence :
                  Version.precedence candidate bound with
              | lt =>
                  exact (hNotLt hCandidatePrecedence).elim
              | eq =>
                  have hBoundStableFromEq :=
                    (stable_bound_and_same_core_of_precedence_eq
                      candidate bound
                      hCandidateStable hCandidatePrecedence).1
                  simp [hBoundStable] at hBoundStableFromEq
              | gt =>
                  simp [
                    Comparator.satisfies,
                    hCandidatePrecedence
                  ]
          | true =>
              have hNextCandidate :
                  stableCoreLE (nextStablePatch bound) candidate := by
                simpa [
                  stableFloorCandidate,
                  hBoundStable
                ] using hFloorCandidate
              have hBoundCandidateLt :
                  stableCoreLT bound candidate := by
                simp only [stableCoreLE, nextStablePatch] at hNextCandidate
                unfold stableCoreLT
                omega
              have hCandidateGt :=
                precedence_gt_of_stableCoreLT
                  bound candidate hBoundCandidateLt
              simp [Comparator.satisfies, hCandidateGt]
      | gte =>
          have hBoundCandidate :
              stableCoreLE bound candidate := by
            simpa [
              stableFloorCandidate,
              stableAtCore,
              stableCoreLE
            ] using hFloorCandidate
          have hNotLt :
              Version.precedence candidate bound ≠ .lt := by
            intro hLt
            have hCandidateBoundLt :=
              stableCoreLT_of_precedence_lt_of_stable
                candidate bound hCandidateStable hLt
            unfold stableCoreLE at hBoundCandidate
            unfold stableCoreLT at hCandidateBoundLt
            omega
          cases hCandidatePrecedence :
              Version.precedence candidate bound with
          | lt =>
              exact (hNotLt hCandidatePrecedence).elim
          | eq =>
              simp [
                Comparator.satisfies,
                hCandidatePrecedence
              ]
          | gt =>
              simp [
                Comparator.satisfies,
                hCandidatePrecedence
              ]
      | eq =>
          have hWitnessEq :
              Version.precedence witness bound = .eq := by
            cases hPrecedence : Version.precedence witness bound with
            | lt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
            | eq =>
                rfl
            | gt =>
                simp [Comparator.satisfies, hPrecedence] at hWitnessSatisfies
          rcases
              stable_bound_and_same_core_of_precedence_eq
                witness bound hWitnessStable hWitnessEq with
            ⟨hBoundStable, hWitnessMajor, hWitnessMinor, hWitnessPatch⟩
          have hBoundCandidate :
              stableCoreLE bound candidate := by
            simpa [
              stableFloorCandidate,
              stableAtCore,
              stableCoreLE
            ] using hFloorCandidate
          have hCandidateMajor :
              candidate.major = bound.major := by
            unfold stableCoreLE at hBoundCandidate hCandidateWitness
            omega
          have hCandidateMinor :
              candidate.minor = bound.minor := by
            unfold stableCoreLE at hBoundCandidate hCandidateWitness
            omega
          have hCandidatePatch :
              candidate.patch = bound.patch := by
            unfold stableCoreLE at hBoundCandidate hCandidateWitness
            omega
          have hCandidateEq :=
            precedence_eq_of_stable_same_core
              candidate bound
              hCandidateStable hBoundStable
              hCandidateMajor hCandidateMinor hCandidatePatch
          simp [Comparator.satisfies, hCandidateEq]

/--
The canonical stable floor never carries prerelease identifiers.
-/
private theorem stableFloorCandidate_is_stable
    (comparator : Comparator) :
    (stableFloorCandidate comparator).prerelease.isEmpty = true := by
  cases comparator with
  | mk operator bound =>
      cases hPrerelease : bound.prerelease.isEmpty <;>
        cases operator <;>
          simp [
            stableFloorCandidate,
            minimumStable,
            stableAtCore,
            nextStablePatch,
            hPrerelease
          ]

/--
Every per-comparator stable floor is already represented by the existing
critical-boundary construction, except for the global minimum which is added
once at comparator-set-pair level.
-/
private theorem stableFloorCandidate_eq_minimum_or_mem_boundary
    (comparator : Comparator) :
    stableFloorCandidate comparator = minimumStable ∨
      stableFloorCandidate comparator ∈ boundaryCandidates comparator := by
  cases comparator with
  | mk operator bound =>
      cases hPrerelease : bound.prerelease.isEmpty <;>
        cases operator <;>
          simp [stableFloorCandidate, boundaryCandidates, hPrerelease]

/--
Strongest canonical stable floor contributed by a finite comparator list.
-/
private def stableFloorMaximum : List Comparator → Version
  | [] => minimumStable
  | comparator :: rest =>
      stableCoreMax
        (stableFloorCandidate comparator)
        (stableFloorMaximum rest)

private theorem stableFloorMaximum_is_stable
    (comparators : List Comparator) :
    (stableFloorMaximum comparators).prerelease.isEmpty = true := by
  induction comparators with
  | nil =>
      simp [stableFloorMaximum, minimumStable]
  | cons comparator rest ih =>
      simp only [stableFloorMaximum]
      exact
        stableCoreMax_is_stable
          (stableFloorCandidate comparator)
          (stableFloorMaximum rest)
          (stableFloorCandidate_is_stable comparator)
          ih

private theorem stableFloorCandidate_core_le_maximum_of_mem
    (comparators : List Comparator)
    (comparator : Comparator)
    (hComparator : comparator ∈ comparators) :
    stableCoreLE
      (stableFloorCandidate comparator)
      (stableFloorMaximum comparators) := by
  induction comparators with
  | nil =>
      simp at hComparator
  | cons head tail ih =>
      rcases List.mem_cons.mp hComparator with hEq | hTail
      · subst comparator
        simp only [stableFloorMaximum]
        exact
          stableCoreLE_left_max
            (stableFloorCandidate head)
            (stableFloorMaximum tail)
      · have hToTail :=
          ih hTail
        have hTailToMaximum :=
          stableCoreLE_right_max
            (stableFloorCandidate head)
            (stableFloorMaximum tail)
        exact
          stableCoreLE_trans
            (stableFloorCandidate comparator)
            (stableFloorMaximum tail)
            (stableFloorMaximum (head :: tail))
            hToTail
            hTailToMaximum

private theorem stableFloorMaximum_core_le
    (comparators : List Comparator)
    (upper : Version)
    (hFloors :
      ∀ comparator ∈ comparators,
        stableCoreLE (stableFloorCandidate comparator) upper) :
    stableCoreLE (stableFloorMaximum comparators) upper := by
  induction comparators with
  | nil =>
      simpa [stableFloorMaximum] using
        minimumStable_core_le upper
  | cons head tail ih =>
      simp only [stableFloorMaximum]
      apply stableCoreMax_core_le
      · exact hFloors head (List.mem_cons_self)
      · apply ih
        intro comparator hComparator
        exact
          hFloors comparator
            (List.mem_cons_of_mem head hComparator)

private theorem stableFloorMaximum_eq_minimum_or_exists_floor
    (comparators : List Comparator) :
    stableFloorMaximum comparators = minimumStable ∨
      ∃ comparator,
        comparator ∈ comparators ∧
        stableFloorMaximum comparators =
          stableFloorCandidate comparator := by
  induction comparators with
  | nil =>
      exact Or.inl rfl
  | cons head tail ih =>
      simp only [stableFloorMaximum]
      rcases
          stableCoreMax_eq_left_or_right
            (stableFloorCandidate head)
            (stableFloorMaximum tail) with
        hHead | hTailMaximum
      · exact
          Or.inr
            ⟨head, List.mem_cons_self, hHead⟩
      · rw [hTailMaximum]
        rcases ih with hMinimum | ⟨comparator, hComparator, hEqual⟩
        · exact Or.inl hMinimum
        · exact
            Or.inr
              ⟨comparator,
                List.mem_cons_of_mem head hComparator,
                hEqual⟩

private def comparatorSetCandidates (set : ComparatorSet) : List Version :=
  set.comparators.flatMap boundaryCandidates

/--
Critical-boundary pool for one pair of conjunctive comparator sets.
-/
def comparatorSetIntersectionCandidates
    (left right : ComparatorSet) : List Version :=
  minimumStable :: (comparatorSetCandidates left ++ comparatorSetCandidates right)

private theorem prereleaseFloorAtCore_eq_of_same_core
    (left right : Version)
    (hMajor : left.major = right.major)
    (hMinor : left.minor = right.minor)
    (hPatch : left.patch = right.patch) :
    prereleaseFloorAtCore left = prereleaseFloorAtCore right := by
  simp [prereleaseFloorAtCore, hMajor, hMinor, hPatch]

/--
The strongest prerelease lower boundary selected from a comparator-set pair is
already present in the finite pair candidate pool.
-/
private theorem prereleaseLowerMaximum_mem_pair_candidates
    (left right : ComparatorSet)
    (witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hLeft : left.satisfies witness = true) :
    prereleaseLowerMaximum
        (left.comparators ++ right.comparators)
        witness ∈
      comparatorSetIntersectionCandidates left right := by
  rcases
      ComparatorSet.exists_prerelease_bound_same_core_of_satisfies
        left witness hWitnessPrerelease hLeft with
    ⟨anchor,
      hAnchor,
      hAnchorPrerelease,
      hAnchorMajor,
      hAnchorMinor,
      hAnchorPatch⟩
  have hFloorEq :
      prereleaseFloorAtCore anchor.bound =
        prereleaseFloorAtCore witness :=
    prereleaseFloorAtCore_eq_of_same_core
      anchor.bound witness
      hAnchorMajor hAnchorMinor hAnchorPatch
  have hAnchorBoundary :
      prereleaseFloorAtCore witness ∈ boundaryCandidates anchor := by
    rw [← hFloorEq]
    exact
      prereleaseFloorAtCore_mem_boundary
        anchor hAnchorPrerelease
  have hFloorInLeft :
      prereleaseFloorAtCore witness ∈
        comparatorSetCandidates left := by
    simp only [comparatorSetCandidates, List.mem_flatMap]
    exact ⟨anchor, hAnchor, hAnchorBoundary⟩
  have hFloorInPair :
      prereleaseFloorAtCore witness ∈
        comparatorSetIntersectionCandidates left right := by
    simp [
      comparatorSetIntersectionCandidates,
      hFloorInLeft
    ]
  rcases
      prereleaseLowerMaximum_eq_floor_or_exists_lower
        (left.comparators ++ right.comparators)
        witness with
    hFloor | ⟨comparator, hComparator, hMaximum⟩
  · rw [hFloor]
    exact hFloorInPair
  · rcases
        prereleaseLowerCandidate_eq_floor_or_mem_boundary
          comparator witness with
      hLowerFloor | hBoundary
    · rw [hMaximum, hLowerFloor]
      exact hFloorInPair
    · rcases List.mem_append.mp hComparator with
        hInLeft | hInRight
      · have hInCandidates :
            prereleaseLowerCandidate comparator witness ∈
              comparatorSetCandidates left := by
          simp only [comparatorSetCandidates, List.mem_flatMap]
          exact ⟨comparator, hInLeft, hBoundary⟩
        rw [hMaximum]
        simp [
          comparatorSetIntersectionCandidates,
          hInCandidates
        ]
      · have hInCandidates :
            prereleaseLowerCandidate comparator witness ∈
              comparatorSetCandidates right := by
          simp only [comparatorSetCandidates, List.mem_flatMap]
          exact ⟨comparator, hInRight, hBoundary⟩
        rw [hMaximum]
        simp [
          comparatorSetIntersectionCandidates,
          hInCandidates
        ]

private theorem stableFloorMaximum_mem_pair_candidates
    (left right : ComparatorSet) :
    stableFloorMaximum (left.comparators ++ right.comparators) ∈
      comparatorSetIntersectionCandidates left right := by
  rcases
      stableFloorMaximum_eq_minimum_or_exists_floor
        (left.comparators ++ right.comparators) with
    hMinimum | ⟨comparator, hComparator, hMaximum⟩
  · rw [hMinimum]
    simp [comparatorSetIntersectionCandidates]
  · rcases List.mem_append.mp hComparator with hLeft | hRight
    · rcases
          stableFloorCandidate_eq_minimum_or_mem_boundary comparator with
        hFloorMinimum | hBoundary
      · rw [hMaximum, hFloorMinimum]
        simp [comparatorSetIntersectionCandidates]
      · have hInLeft :
            stableFloorCandidate comparator ∈
              comparatorSetCandidates left := by
          simp only [comparatorSetCandidates, List.mem_flatMap]
          exact ⟨comparator, hLeft, hBoundary⟩
        rw [hMaximum]
        simp [comparatorSetIntersectionCandidates, hInLeft]
    · rcases
          stableFloorCandidate_eq_minimum_or_mem_boundary comparator with
        hFloorMinimum | hBoundary
      · rw [hMaximum, hFloorMinimum]
        simp [comparatorSetIntersectionCandidates]
      · have hInRight :
            stableFloorCandidate comparator ∈
              comparatorSetCandidates right := by
          simp only [comparatorSetCandidates, List.mem_flatMap]
          exact ⟨comparator, hRight, hBoundary⟩
        rw [hMaximum]
        simp [comparatorSetIntersectionCandidates, hInRight]

private theorem stableFloorMaximum_pair_is_stable
    (left right : ComparatorSet) :
    (stableFloorMaximum
      (left.comparators ++ right.comparators)).prerelease.isEmpty = true := by
  exact
    stableFloorMaximum_is_stable
      (left.comparators ++ right.comparators)

private theorem stableFloorMaximum_pair_core_le_of_satisfies
    (left right : ComparatorSet)
    (witness : Version)
    (hLeft : left.satisfies witness = true)
    (hRight : right.satisfies witness = true) :
    stableCoreLE
      (stableFloorMaximum (left.comparators ++ right.comparators))
      witness := by
  apply
    stableFloorMaximum_core_le
      (left.comparators ++ right.comparators)
      witness
  intro comparator hComparator
  rcases List.mem_append.mp hComparator with hInLeft | hInRight
  · exact
      stableFloorCandidate_core_le_of_set_satisfies
        left witness hLeft comparator hInLeft
  · exact
      stableFloorCandidate_core_le_of_set_satisfies
        right witness hRight comparator hInRight

private theorem stableFloorMaximum_pair_satisfies_of_stable_witness
    (left right : ComparatorSet)
    (witness : Version)
    (hWitnessStable : witness.prerelease.isEmpty = true)
    (hLeft : left.satisfies witness = true)
    (hRight : right.satisfies witness = true) :
    left.satisfies
        (stableFloorMaximum
          (left.comparators ++ right.comparators)) = true ∧
      right.satisfies
        (stableFloorMaximum
          (left.comparators ++ right.comparators)) = true := by
  let candidate :=
    stableFloorMaximum
      (left.comparators ++ right.comparators)
  have hCandidateStable :
      candidate.prerelease.isEmpty = true := by
    simpa [candidate] using
      stableFloorMaximum_pair_is_stable left right
  have hCandidateWitness :
      stableCoreLE candidate witness := by
    simpa [candidate] using
      stableFloorMaximum_pair_core_le_of_satisfies
        left right witness hLeft hRight
  constructor
  · apply
      (ComparatorSet.satisfies_eq_true_iff_stable
        left candidate hCandidateStable).mpr
    intro comparator hComparator
    have hInPair :
        comparator ∈ left.comparators ++ right.comparators := by
      simp [hComparator]
    have hFloorCandidate :=
      stableFloorCandidate_core_le_maximum_of_mem
        (left.comparators ++ right.comparators)
        comparator hInPair
    have hWitnessPrimitive :=
      ((ComparatorSet.satisfies_eq_true_iff left witness).mp hLeft).1
        comparator hComparator
    exact
      comparator_satisfies_stable_sandwich
        comparator candidate witness
        hCandidateStable hWitnessStable
        hFloorCandidate hCandidateWitness hWitnessPrimitive
  · apply
      (ComparatorSet.satisfies_eq_true_iff_stable
        right candidate hCandidateStable).mpr
    intro comparator hComparator
    have hInPair :
        comparator ∈ left.comparators ++ right.comparators := by
      simp [hComparator]
    have hFloorCandidate :=
      stableFloorCandidate_core_le_maximum_of_mem
        (left.comparators ++ right.comparators)
        comparator hInPair
    have hWitnessPrimitive :=
      ((ComparatorSet.satisfies_eq_true_iff right witness).mp hRight).1
        comparator hComparator
    exact
      comparator_satisfies_stable_sandwich
        comparator candidate witness
        hCandidateStable hWitnessStable
        hFloorCandidate hCandidateWitness hWitnessPrimitive

/--
Any pair of comparator sets sharing a prerelease witness has a generated
same-core prerelease candidate that already passes both set-local admission
gates.

The remaining prerelease completeness work is therefore only about primitive
comparator satisfaction.
-/
private theorem exists_pair_prerelease_candidate_with_admission
    (left right : ComparatorSet)
    (witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hLeft : left.satisfies witness = true)
    (hRight : right.satisfies witness = true) :
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      candidate.prerelease.isEmpty = false ∧
      candidate.major = witness.major ∧
      candidate.minor = witness.minor ∧
      candidate.patch = witness.patch ∧
      left.prereleaseAdmitted candidate = true ∧
      right.prereleaseAdmitted candidate = true := by
  rcases
      ComparatorSet.exists_prerelease_bound_same_core_of_satisfies
        left witness hWitnessPrerelease hLeft with
    ⟨anchor,
      hAnchor,
      hAnchorPrerelease,
      hAnchorMajor,
      hAnchorMinor,
      hAnchorPatch⟩
  let candidate := prereleaseFloorAtCore anchor.bound
  have hBoundary :
      candidate ∈ boundaryCandidates anchor := by
    simpa [candidate] using
      prereleaseFloorAtCore_mem_boundary anchor hAnchorPrerelease
  have hLeftCandidates :
      candidate ∈ comparatorSetCandidates left := by
    simp only [comparatorSetCandidates, List.mem_flatMap]
    exact ⟨anchor, hAnchor, hBoundary⟩
  have hPairCandidate :
      candidate ∈ comparatorSetIntersectionCandidates left right := by
    simp [
      comparatorSetIntersectionCandidates,
      hLeftCandidates
    ]
  have hCandidatePrerelease :
      candidate.prerelease.isEmpty = false := by
    simpa [candidate] using
      prereleaseFloorAtCore_is_prerelease anchor.bound
  have hCandidateMajor :
      candidate.major = witness.major := by
    simpa [candidate, prereleaseFloorAtCore] using hAnchorMajor
  have hCandidateMinor :
      candidate.minor = witness.minor := by
    simpa [candidate, prereleaseFloorAtCore] using hAnchorMinor
  have hCandidatePatch :
      candidate.patch = witness.patch := by
    simpa [candidate, prereleaseFloorAtCore] using hAnchorPatch
  have hLeftAdmission :
      left.prereleaseAdmitted candidate = true := by
    exact
      ComparatorSet.prereleaseAdmitted_of_same_core_as_satisfied
        left witness candidate
        hWitnessPrerelease hLeft hCandidatePrerelease
        hCandidateMajor hCandidateMinor hCandidatePatch
  have hRightAdmission :
      right.prereleaseAdmitted candidate = true := by
    exact
      ComparatorSet.prereleaseAdmitted_of_same_core_as_satisfied
        right witness candidate
        hWitnessPrerelease hRight hCandidatePrerelease
        hCandidateMajor hCandidateMinor hCandidatePatch
  exact
    ⟨candidate,
      hPairCandidate,
      hCandidatePrerelease,
      hCandidateMajor,
      hCandidateMinor,
      hCandidatePatch,
      hLeftAdmission,
      hRightAdmission⟩

/--
The local completeness obligation for one pair of comparator sets.

If the two conjunctions have a common semantic witness, one of their generated
critical-boundary candidates must also satisfy both conjunctions.
-/
def ComparatorSetPairCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
Stable-witness half of comparator-set-pair candidate completeness.

This isolates the ordinary release-ordering problem from node-semver's
set-local prerelease admission rule.
-/
def ComparatorSetPairStableCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      candidate.prerelease.isEmpty = true ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
The finite critical-boundary pool is complete for comparator-set intersections
that have a stable common witness.
-/
theorem comparatorSetPairStableCandidatesComplete
    (left right : ComparatorSet) :
    ComparatorSetPairStableCandidatesComplete left right := by
  intro hWitness
  rcases hWitness with
    ⟨witness, hWitnessStable, hLeft, hRight⟩
  let candidate :=
    stableFloorMaximum
      (left.comparators ++ right.comparators)
  have hCandidate :
      candidate ∈ comparatorSetIntersectionCandidates left right := by
    simpa [candidate] using
      stableFloorMaximum_mem_pair_candidates left right
  have hSatisfies :=
    stableFloorMaximum_pair_satisfies_of_stable_witness
      left right witness hWitnessStable hLeft hRight
  exact
    ⟨candidate,
      hCandidate,
      by simpa [candidate] using hSatisfies.1,
      by simpa [candidate] using hSatisfies.2⟩

/--
Prerelease-witness half of comparator-set-pair candidate completeness.

Unlike the stable case, this branch must preserve the same-core prerelease
admission carried by each comparator set.
-/
def ComparatorSetPairPrereleaseCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      candidate.prerelease.isEmpty = false ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
Primitive-only remainder of prerelease comparator-set-pair completeness.

Admission is intentionally absent here. A candidate only has to stay on the
witness core, remain a prerelease, belong to the generated pool, and satisfy
every primitive comparator in both sets.
-/
def ComparatorSetPairPrereleasePrimitiveCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  ∀ witness,
    witness.prerelease.isEmpty = false →
    left.satisfies witness = true →
    right.satisfies witness = true →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      candidate.prerelease.isEmpty = false ∧
      candidate.major = witness.major ∧
      candidate.minor = witness.minor ∧
      candidate.patch = witness.patch ∧
      (∀ comparator ∈ left.comparators,
        comparator.satisfies candidate = true) ∧
      (∀ comparator ∈ right.comparators,
        comparator.satisfies candidate = true)

/--
Once the primitive-only prerelease obligation is solved, set-local admission
is recovered automatically from the original same-core witness.
-/
theorem comparatorSetPairPrereleaseCandidatesComplete_of_primitives
    (left right : ComparatorSet)
    (hPrimitive :
      ComparatorSetPairPrereleasePrimitiveCandidatesComplete left right) :
    ComparatorSetPairPrereleaseCandidatesComplete left right := by
  intro hWitness
  rcases hWitness with
    ⟨witness, hWitnessPrerelease, hLeftWitness, hRightWitness⟩
  rcases
      hPrimitive witness
        hWitnessPrerelease hLeftWitness hRightWitness with
    ⟨candidate,
      hCandidate,
      hCandidatePrerelease,
      hMajor,
      hMinor,
      hPatch,
      hLeftPrimitive,
      hRightPrimitive⟩
  have hLeftAdmission :
      left.prereleaseAdmitted candidate = true := by
    exact
      ComparatorSet.prereleaseAdmitted_of_same_core_as_satisfied
        left witness candidate
        hWitnessPrerelease hLeftWitness hCandidatePrerelease
        hMajor hMinor hPatch
  have hRightAdmission :
      right.prereleaseAdmitted candidate = true := by
    exact
      ComparatorSet.prereleaseAdmitted_of_same_core_as_satisfied
        right witness candidate
        hWitnessPrerelease hRightWitness hCandidatePrerelease
        hMajor hMinor hPatch
  have hLeftCandidate :
      left.satisfies candidate = true := by
    exact
      (ComparatorSet.satisfies_eq_true_iff left candidate).mpr
        ⟨hLeftPrimitive, hLeftAdmission⟩
  have hRightCandidate :
      right.satisfies candidate = true := by
    exact
      (ComparatorSet.satisfies_eq_true_iff right candidate).mpr
        ⟨hRightPrimitive, hRightAdmission⟩
  exact
    ⟨candidate,
      hCandidate,
      hLeftCandidate,
      hRightCandidate⟩

/--
The local completeness obligation splits exactly into stable and prerelease
witness cases.
-/
theorem comparatorSetPairCandidatesComplete_of_stable_and_prerelease
    (left right : ComparatorSet)
    (hStable : ComparatorSetPairStableCandidatesComplete left right)
    (hPrerelease : ComparatorSetPairPrereleaseCandidatesComplete left right) :
    ComparatorSetPairCandidatesComplete left right := by
  intro hWitness
  rcases hWitness with ⟨candidate, hLeft, hRight⟩
  cases hEmpty : candidate.prerelease.isEmpty with
  | false =>
      exact hPrerelease ⟨candidate, hEmpty, hLeft, hRight⟩
  | true =>
      exact hStable ⟨candidate, hEmpty, hLeft, hRight⟩

private def rangeBoundaryCandidates (range : Range) : List Version :=
  range.sets.flatMap comparatorSetCandidates

/--
Finite candidate pool used by the first intersection witness search.

This pool is deliberately exposed for inspection. At this stage Semverifier
proves only soundness of returned witnesses; completeness of this finite pool
is a separate theorem still to be established.
-/
def intersectionCandidates (left right : Range) : List Version :=
  minimumStable ::
    (rangeBoundaryCandidates left ++ rangeBoundaryCandidates right)

private def firstOverlap?
    (left right : Range) :
    List Version → Option Version
  | [] => none
  | candidate :: rest =>
      if overlapsAt left right candidate then
        some candidate
      else
        firstOverlap? left right rest

/--
Search the finite critical-boundary pool for a concrete intersection witness.

A returned version is proved sound below. Returning `none` does not yet mean
that the ranges are disjoint; that conclusion waits for a completeness proof
for `intersectionCandidates`.
-/
def findIntersectionWitness? (left right : Range) : Option Version :=
  firstOverlap? left right (intersectionCandidates left right)

/--
The one remaining mathematical obligation for global completeness of the finite
intersection search.

It says that whenever the semantic ranges intersect, at least one generated
critical-boundary candidate is itself a concrete overlap witness.
-/
def IntersectionCandidatesComplete (left right : Range) : Prop :=
  Intersects left right →
    ∃ candidate,
      candidate ∈ intersectionCandidates left right ∧
      overlapsAt left right candidate = true

private theorem comparatorSetCandidate_mem_rangeCandidates
    (range : Range)
    (set : ComparatorSet)
    (hSet : set ∈ range.sets)
    (candidate : Version)
    (hCandidate : candidate ∈ comparatorSetCandidates set) :
    candidate ∈ rangeBoundaryCandidates range := by
  simp only [rangeBoundaryCandidates, List.mem_flatMap]
  exact ⟨set, hSet, hCandidate⟩

private theorem comparatorSetIntersectionCandidate_mem_intersectionCandidates
    (left right : Range)
    (leftSet rightSet : ComparatorSet)
    (hLeftSet : leftSet ∈ left.sets)
    (hRightSet : rightSet ∈ right.sets)
    (candidate : Version)
    (hCandidate :
      candidate ∈ comparatorSetIntersectionCandidates leftSet rightSet) :
    candidate ∈ intersectionCandidates left right := by
  simp only [
    comparatorSetIntersectionCandidates,
    List.mem_cons,
    List.mem_append
  ] at hCandidate
  rcases hCandidate with hMinimum | hLeft | hRight
  · subst candidate
    simp [intersectionCandidates]
  · have hInLeft :=
      comparatorSetCandidate_mem_rangeCandidates
        left leftSet hLeftSet candidate hLeft
    simp [intersectionCandidates, hInLeft]
  · have hInRight :=
      comparatorSetCandidate_mem_rangeCandidates
        right rightSet hRightSet candidate hRight
    simp [intersectionCandidates, hInRight]

/--
Range-level candidate completeness follows from completeness of every
conjunctive comparator-set pair.

This removes `||` union structure from the remaining global proof obligation.
-/
theorem intersectionCandidatesComplete_of_comparator_set_pairs
    (left right : Range)
    (hPairs :
      ∀ leftSet,
        leftSet ∈ left.sets →
        ∀ rightSet,
          rightSet ∈ right.sets →
          ComparatorSetPairCandidatesComplete leftSet rightSet) :
    IntersectionCandidatesComplete left right := by
  intro hIntersects
  rcases hIntersects with ⟨witness, hLeft, hRight⟩
  unfold Contains at hLeft hRight
  rcases
      (Range.satisfies_eq_true_iff left witness).mp hLeft with
    ⟨leftSet, hLeftSet, hLeftWitness⟩
  rcases
      (Range.satisfies_eq_true_iff right witness).mp hRight with
    ⟨rightSet, hRightSet, hRightWitness⟩
  have hPairWitness :
      ∃ candidate,
        leftSet.satisfies candidate = true ∧
        rightSet.satisfies candidate = true :=
    ⟨witness, hLeftWitness, hRightWitness⟩
  rcases
      hPairs leftSet hLeftSet rightSet hRightSet hPairWitness with
    ⟨candidate, hCandidate, hLeftCandidate, hRightCandidate⟩
  refine ⟨candidate, ?_, ?_⟩
  · exact
      comparatorSetIntersectionCandidate_mem_intersectionCandidates
        left right leftSet rightSet
        hLeftSet hRightSet candidate hCandidate
  · apply (overlapsAt_eq_true_iff left right candidate).mpr
    constructor
    · unfold Contains
      exact
        (Range.satisfies_eq_true_iff left candidate).mpr
          ⟨leftSet, hLeftSet, hLeftCandidate⟩
    · unfold Contains
      exact
        (Range.satisfies_eq_true_iff right candidate).mpr
          ⟨rightSet, hRightSet, hRightCandidate⟩

private theorem firstOverlap?_exists_some_of_mem_overlap
    (left right : Range)
    (candidates : List Version)
    (h :
      ∃ candidate,
        candidate ∈ candidates ∧
        overlapsAt left right candidate = true) :
    ∃ candidate, firstOverlap? left right candidates = some candidate := by
  induction candidates with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases hHead : overlapsAt left right head with
      | false =>
          have hTail :
              ∃ candidate,
                candidate ∈ tail ∧
                overlapsAt left right candidate = true := by
            rcases h with ⟨candidate, hMem, hOverlap⟩
            rcases List.mem_cons.mp hMem with hEq | hMemTail
            · subst candidate
              simp [hHead] at hOverlap
            · exact ⟨candidate, hMemTail, hOverlap⟩
          rcases ih hTail with ⟨candidate, hFound⟩
          exact ⟨candidate, by simp [firstOverlap?, hHead, hFound]⟩
      | true =>
          exact ⟨head, by simp [firstOverlap?, hHead]⟩

private theorem firstOverlap?_sound
    (left right : Range)
    (candidates : List Version)
    (candidate : Version)
    (h : firstOverlap? left right candidates = some candidate) :
    overlapsAt left right candidate = true := by
  induction candidates with
  | nil =>
      simp [firstOverlap?] at h
  | cons head tail ih =>
      by_cases hOverlap : overlapsAt left right head = true
      · simp [firstOverlap?, hOverlap] at h
        subst candidate
        exact hOverlap
      · have hFalse : overlapsAt left right head = false := by
          cases hValue : overlapsAt left right head <;> simp_all
        simp [firstOverlap?, hFalse] at h
        exact ih h

/-- Any returned witness is accepted by both ranges. -/
theorem findIntersectionWitness?_overlaps
    (left right : Range)
    (candidate : Version)
    (h : findIntersectionWitness? left right = some candidate) :
    overlapsAt left right candidate = true := by
  exact firstOverlap?_sound
    left
    right
    (intersectionCandidates left right)
    candidate
    h

/-- Any returned witness proves semantic intersection. -/
theorem findIntersectionWitness?_sound
    (left right : Range)
    (candidate : Version)
    (h : findIntersectionWitness? left right = some candidate) :
    Intersects left right := by
  have hOverlap :=
    findIntersectionWitness?_overlaps left right candidate h
  have hBoth :=
    (overlapsAt_eq_true_iff left right candidate).mp hOverlap
  exact ⟨candidate, hBoth.1, hBoth.2⟩

/--
Once the critical-boundary candidate pool is complete, the existing finite
search is complete as an algorithm: every semantic intersection produces a
returned witness.
-/
theorem findIntersectionWitness?_complete
    (left right : Range)
    (hCandidates : IntersectionCandidatesComplete left right)
    (hIntersects : Intersects left right) :
    ∃ candidate, findIntersectionWitness? left right = some candidate := by
  have hCandidate := hCandidates hIntersects
  simpa [findIntersectionWitness?] using
    firstOverlap?_exists_some_of_mem_overlap
      left
      right
      (intersectionCandidates left right)
      hCandidate

/--
Under the candidate-completeness obligation, returning `none` is equivalent to
semantic disjointness.
-/
theorem findIntersectionWitness?_none_iff_not_intersects
    (left right : Range)
    (hCandidates : IntersectionCandidatesComplete left right) :
    findIntersectionWitness? left right = none ↔
      ¬ Intersects left right := by
  constructor
  · intro hNone hIntersects
    rcases
      findIntersectionWitness?_complete
        left right hCandidates hIntersects with
      ⟨candidate, hSome⟩
    rw [hNone] at hSome
    contradiction
  · intro hNotIntersects
    cases hSearch : findIntersectionWitness? left right with
    | none =>
        rfl
    | some candidate =>
        have hIntersects :=
          findIntersectionWitness?_sound left right candidate hSearch
        exact (hNotIntersects hIntersects).elim

end Range
end Semverifier
