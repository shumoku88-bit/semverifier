namespace Semverifier

/--
A pre-release identifier after syntax validation.

Numeric and non-numeric identifiers are separated here because SemVer assigns
different precedence rules to them. Parsing and textual validation belong to a
later boundary.
-/
inductive PrereleaseIdentifier where
  | numeric (value : Nat)
  | text (value : String)
deriving Repr, BEq, DecidableEq

namespace PrereleaseIdentifier

/-- SemVer precedence for one validated pre-release identifier. -/
def precedence : PrereleaseIdentifier → PrereleaseIdentifier → Ordering
  | .numeric left, .numeric right => compare left right
  | .numeric _, .text _ => .lt
  | .text _, .numeric _ => .gt
  | .text left, .text right => compare left right

end PrereleaseIdentifier

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

namespace Version

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

/--
SemVer precedence between two validated versions.

The comparison follows major, minor, patch, then pre-release precedence.
Build metadata is intentionally ignored.
-/
def precedence (left right : Version) : Ordering :=
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

instance : Ord Version where
  compare := precedence

/-- Changing only build metadata cannot change SemVer precedence. -/
theorem precedence_ignores_build
    (left right : Version)
    (leftBuild rightBuild : List String) :
    precedence { left with build := leftBuild } { right with build := rightBuild } =
      precedence left right := by
  rfl

end Version
end Semverifier
