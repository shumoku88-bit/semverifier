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
