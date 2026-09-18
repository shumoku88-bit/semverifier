import Init.Data.Order.Ord
import Semverifier.Identifier

namespace Semverifier

/--
A semantic version after syntax validation.

Build identifiers are retained because they are part of a SemVer version, but
they deliberately do not participate in precedence.
-/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : List PrereleaseIdentifier := []
  build : List String := []
deriving Repr, BEq, DecidableEq

/--
The part of a semantic version that participates in SemVer precedence.

Keeping this distinct from `Version` matters because build metadata is part of
version identity but is explicitly ignored for precedence.
-/
structure PrecedenceKey where
  major : Nat
  minor : Nat
  patch : Nat
  prerelease : List PrereleaseIdentifier := []
deriving Repr, BEq, DecidableEq

namespace PrecedenceKey

private def prereleasePrecedence :
    List PrereleaseIdentifier → List PrereleaseIdentifier → Ordering :=
  List.compareLex PrereleaseIdentifier.precedence

private def releasePrecedence
    (left right : List PrereleaseIdentifier) : Ordering :=
  match left, right with
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | _ :: _, _ :: _ => prereleasePrecedence left right

/-- SemVer precedence for two precedence-bearing keys. -/
def ordering (left right : PrecedenceKey) : Ordering :=
  match compare left.major right.major with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
      match compare left.minor right.minor with
      | .lt => .lt
      | .gt => .gt
      | .eq =>
          match compare left.patch right.patch with
          | .lt => .lt
          | .gt => .gt
          | .eq => releasePrecedence left.prerelease right.prerelease

private theorem prereleasePrecedence_append_zero_gt
    (prerelease : List PrereleaseIdentifier) :
    prereleasePrecedence
        (prerelease ++ [.numeric 0])
        prerelease = .gt := by
  induction prerelease with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead :
          PrereleaseIdentifier.precedence head head = .eq := by
        cases head <;>
          simp [PrereleaseIdentifier.precedence]
      simp only [List.cons_append, prereleasePrecedence]
      rw [hHead]
      exact ih

/--
Appending numeric zero to a non-empty prerelease list produces a strictly
higher prerelease at the same major/minor/patch core.
-/
theorem ordering_prerelease_append_zero_gt
    (major minor patch : Nat)
    (prerelease : List PrereleaseIdentifier)
    (hPrerelease : prerelease.isEmpty = false) :
    ordering
        {
          major := major
          minor := minor
          patch := patch
          prerelease := prerelease ++ [.numeric 0]
        }
        {
          major := major
          minor := minor
          patch := patch
          prerelease := prerelease
        } = .gt := by
  cases hList : prerelease with
  | nil =>
      simp [hList] at hPrerelease
  | cons head tail =>
      simpa [
        ordering,
        releasePrecedence,
        hList
      ] using
        prereleasePrecedence_append_zero_gt (head :: tail)

private theorem prereleaseIdentifier_precedence_swap
    (left right : PrereleaseIdentifier) :
    PrereleaseIdentifier.precedence left right =
      (PrereleaseIdentifier.precedence right left).swap := by
  cases left with
  | numeric leftValue =>
      cases right with
      | numeric rightValue =>
          simpa [PrereleaseIdentifier.precedence] using
            (Std.OrientedOrd.eq_swap
              (α := Nat)
              (a := leftValue)
              (b := rightValue))
      | text rightValue =>
          rfl
  | text leftValue =>
      cases right with
      | numeric rightValue =>
          rfl
      | text rightValue =>
          simpa [PrereleaseIdentifier.precedence] using
            (Std.OrientedOrd.eq_swap
              (α := String)
              (a := leftValue.value)
              (b := rightValue.value))

private instance prereleaseIdentifierPrecedenceTrans :
    Std.TransCmp PrereleaseIdentifier.precedence where
  eq_swap := prereleaseIdentifier_precedence_swap
  isLE_trans := by
    intro first second third hFirstSecond hSecondThird
    cases first with
    | numeric firstValue =>
        cases second with
        | numeric secondValue =>
            cases third with
            | numeric thirdValue =>
                have hFirstSecond' :
                    (compare firstValue secondValue).isLE := by
                  simpa [PrereleaseIdentifier.precedence] using hFirstSecond
                have hSecondThird' :
                    (compare secondValue thirdValue).isLE := by
                  simpa [PrereleaseIdentifier.precedence] using hSecondThird
                have hTrans :=
                  Std.TransCmp.isLE_trans
                    (cmp := compare)
                    hFirstSecond'
                    hSecondThird'
                simpa [PrereleaseIdentifier.precedence] using hTrans
            | text thirdValue =>
                simp [PrereleaseIdentifier.precedence]
        | text secondValue =>
            cases third with
            | numeric thirdValue =>
                simp [PrereleaseIdentifier.precedence] at hSecondThird
            | text thirdValue =>
                simp [PrereleaseIdentifier.precedence]
    | text firstValue =>
        cases second with
        | numeric secondValue =>
            simp [PrereleaseIdentifier.precedence] at hFirstSecond
        | text secondValue =>
            cases third with
            | numeric thirdValue =>
                simp [PrereleaseIdentifier.precedence] at hSecondThird
            | text thirdValue =>
                have hFirstSecond' :
                    (compare firstValue.value secondValue.value).isLE := by
                  simpa [PrereleaseIdentifier.precedence] using hFirstSecond
                have hSecondThird' :
                    (compare secondValue.value thirdValue.value).isLE := by
                  simpa [PrereleaseIdentifier.precedence] using hSecondThird
                have hTrans :=
                  Std.TransCmp.isLE_trans
                    (cmp := compare)
                    hFirstSecond'
                    hSecondThird'
                simpa [PrereleaseIdentifier.precedence] using hTrans

/--
The prerelease list `[0]` is never greater than any non-empty prerelease
list at the same major/minor/patch core.
-/
theorem ordering_prerelease_zero_ne_gt
    (major minor patch : Nat)
    (prerelease : List PrereleaseIdentifier)
    (hPrerelease : prerelease.isEmpty = false) :
    ordering
        {
          major := major
          minor := minor
          patch := patch
          prerelease := [.numeric 0]
        }
        {
          major := major
          minor := minor
          patch := patch
          prerelease := prerelease
        } ≠ .gt := by
  cases hList : prerelease with
  | nil =>
      simp [hList] at hPrerelease
  | cons head tail =>
      cases head with
      | numeric value =>
          cases value with
          | zero =>
              cases tail with
              | nil =>
                  simp [
                    ordering,
                    releasePrecedence,
                    prereleasePrecedence,
                    PrereleaseIdentifier.precedence,
                    hList
                  ]
              | cons next rest =>
                  simp [
                    ordering,
                    releasePrecedence,
                    prereleasePrecedence,
                    PrereleaseIdentifier.precedence,
                    hList
                  ]
          | succ value =>
              have hCompare :
                  compare 0 (Nat.succ value) = .lt :=
                Nat.compare_eq_lt.mpr (Nat.zero_lt_succ value)
              simp [
                ordering,
                releasePrecedence,
                prereleasePrecedence,
                PrereleaseIdentifier.precedence,
                hCompare
              ]
      | text value =>
          simp [
            ordering,
            releasePrecedence,
            prereleasePrecedence,
            PrereleaseIdentifier.precedence,
            hList
          ]

private theorem prereleasePrecedence_append_zero_ne_gt_of_gt
    (bound witness : List PrereleaseIdentifier)
    (hBound : bound.isEmpty = false)
    (hWitness : witness.isEmpty = false)
    (hGt : prereleasePrecedence witness bound = .gt) :
    prereleasePrecedence
        (bound ++ [.numeric 0])
        witness ≠ .gt := by
  induction bound generalizing witness with
  | nil =>
      simp at hBound
  | cons boundHead boundTail ih =>
      cases witness with
      | nil =>
          simp at hWitness
      | cons witnessHead witnessTail =>
          cases hHead :
              PrereleaseIdentifier.precedence witnessHead boundHead with
          | lt =>
              simp [prereleasePrecedence, hHead] at hGt
          | gt =>
              have hSwap :=
                prereleaseIdentifier_precedence_swap
                  witnessHead boundHead
              have hReverse :
                  PrereleaseIdentifier.precedence
                    boundHead witnessHead = .lt := by
                cases hReverse :
                    PrereleaseIdentifier.precedence
                      boundHead witnessHead <;>
                  simp [hHead, hReverse] at hSwap ⊢
              simp [prereleasePrecedence, hReverse]
          | eq =>
              have hSwap :=
                prereleaseIdentifier_precedence_swap
                  witnessHead boundHead
              have hReverse :
                  PrereleaseIdentifier.precedence
                    boundHead witnessHead = .eq := by
                cases hReverse :
                    PrereleaseIdentifier.precedence
                      boundHead witnessHead <;>
                  simp [hHead, hReverse] at hSwap ⊢
              have hTailGt :
                  prereleasePrecedence witnessTail boundTail = .gt := by
                simpa [prereleasePrecedence, hHead] using hGt
              cases boundTail with
              | nil =>
                  cases witnessTail with
                  | nil =>
                      simp [prereleasePrecedence] at hTailGt
                  | cons witnessNext witnessRest =>
                      have hZero :=
                        ordering_prerelease_zero_ne_gt
                          0 0 0
                          (witnessNext :: witnessRest)
                          (by simp)
                      have hZeroTail :
                          prereleasePrecedence
                              [.numeric 0]
                              (witnessNext :: witnessRest) ≠ .gt := by
                        simpa [
                          ordering,
                          releasePrecedence
                        ] using hZero
                      simpa [
                        prereleasePrecedence,
                        hReverse
                      ] using hZeroTail
              | cons boundNext boundRest =>
                  cases witnessTail with
                  | nil =>
                      simp [prereleasePrecedence] at hTailGt
                  | cons witnessNext witnessRest =>
                      have hRec :=
                        ih
                          (witnessNext :: witnessRest)
                          (by simp)
                          (by simp)
                          hTailGt
                      simpa [
                        prereleasePrecedence,
                        hReverse
                      ] using hRec

/--
For non-empty prerelease lists on one core, appending numeric zero to a strict
lower bound yields a candidate that does not exceed any strict witness.

This is the discrete-successor fact used by prerelease range intersection:
if `witness > bound`, then `bound.0 ≤ witness`.
-/
theorem ordering_prerelease_append_zero_ne_gt_of_gt
    (major minor patch : Nat)
    (bound witness : List PrereleaseIdentifier)
    (hBound : bound.isEmpty = false)
    (hWitness : witness.isEmpty = false)
    (hGt :
      ordering
          {
            major := major
            minor := minor
            patch := patch
            prerelease := witness
          }
          {
            major := major
            minor := minor
            patch := patch
            prerelease := bound
          } = .gt) :
    ordering
        {
          major := major
          minor := minor
          patch := patch
          prerelease := bound ++ [.numeric 0]
        }
        {
          major := major
          minor := minor
          patch := patch
          prerelease := witness
        } ≠ .gt := by
  cases hBoundList : bound with
  | nil =>
      simp [hBoundList] at hBound
  | cons boundHead boundTail =>
      cases hWitnessList : witness with
      | nil =>
          simp [hWitnessList] at hWitness
      | cons witnessHead witnessTail =>
          have hListGt :
              prereleasePrecedence
                  (witnessHead :: witnessTail)
                  (boundHead :: boundTail) = .gt := by
            simpa [
              ordering,
              releasePrecedence,
              hBoundList,
              hWitnessList
            ] using hGt
          have hList :=
            prereleasePrecedence_append_zero_ne_gt_of_gt
              (boundHead :: boundTail)
              (witnessHead :: witnessTail)
              (by simp)
              (by simp)
              hListGt
          simpa [
            ordering,
            releasePrecedence,
            hBoundList,
            hWitnessList
          ] using hList

/--
SemVer precedence is transitive within one fixed core when all three values are
prereleases.

This is the order law needed to combine multiple generated prerelease lower
boundaries without leaving the witness core.
-/
theorem ordering_prerelease_isLE_trans
    (major minor patch : Nat)
    (first second third : List PrereleaseIdentifier)
    (hFirst : first.isEmpty = false)
    (hSecond : second.isEmpty = false)
    (hThird : third.isEmpty = false)
    (hFirstSecond :
      (ordering
        { major := major, minor := minor, patch := patch, prerelease := first }
        { major := major, minor := minor, patch := patch, prerelease := second }).isLE)
    (hSecondThird :
      (ordering
        { major := major, minor := minor, patch := patch, prerelease := second }
        { major := major, minor := minor, patch := patch, prerelease := third }).isLE) :
    (ordering
      { major := major, minor := minor, patch := patch, prerelease := first }
      { major := major, minor := minor, patch := patch, prerelease := third }).isLE := by
  cases hFirstList : first with
  | nil =>
      simp [hFirstList] at hFirst
  | cons firstHead firstTail =>
      cases hSecondList : second with
      | nil =>
          simp [hSecondList] at hSecond
      | cons secondHead secondTail =>
          cases hThirdList : third with
          | nil =>
              simp [hThirdList] at hThird
          | cons thirdHead thirdTail =>
              have hTrans :=
                Std.TransCmp.isLE_trans
                  (cmp := List.compareLex PrereleaseIdentifier.precedence)
                  (a := firstHead :: firstTail)
                  (b := secondHead :: secondTail)
                  (c := thirdHead :: thirdTail)
                  (by
                    simpa [
                      ordering,
                      releasePrecedence,
                      prereleasePrecedence,
                      hFirstList,
                      hSecondList
                    ] using hFirstSecond)
                  (by
                    simpa [
                      ordering,
                      releasePrecedence,
                      prereleasePrecedence,
                      hSecondList,
                      hThirdList
                    ] using hSecondThird)
              simpa [
                ordering,
                releasePrecedence,
                prereleasePrecedence,
                hFirstList,
                hThirdList
              ] using hTrans

instance : Ord PrecedenceKey where
  compare := ordering

end PrecedenceKey

namespace Version

/-- Project a full version to exactly the fields used by SemVer precedence. -/
def precedenceKey (version : Version) : PrecedenceKey :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch
    prerelease := version.prerelease
  }

/--
SemVer precedence between two validated versions.

Version identity and precedence are intentionally different notions: build
metadata belongs to the former but not the latter.
-/
def precedence (left right : Version) : Ordering :=
  PrecedenceKey.ordering left.precedenceKey right.precedenceKey

/-- Changing build metadata cannot change the precedence-bearing key. -/
theorem precedenceKey_ignores_build
    (version : Version)
    (build : List String) :
    precedenceKey { version with build := build } = precedenceKey version := by
  rfl

/-- Changing only build metadata cannot change SemVer precedence. -/
theorem precedence_ignores_build
    (left right : Version)
    (leftBuild rightBuild : List String) :
    precedence { left with build := leftBuild } { right with build := rightBuild } =
      precedence left right := by
  rfl

end Version
end Semverifier
