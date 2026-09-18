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
    List PrereleaseIdentifier → List PrereleaseIdentifier → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: leftRest, right :: rightRest =>
      match PrereleaseIdentifier.precedence left right with
      | .eq => prereleasePrecedence leftRest rightRest
      | order => order

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
