import Semverifier.Version

open Semverifier

private def release : Version :=
  { major := 1, minor := 0, patch := 0 }

private def releaseWithBuild (build : List String) : Version :=
  { release with build := build }

private def pre (ids : List PrereleaseIdentifier) : Version :=
  { major := 1, minor := 0, patch := 0, prerelease := ids }

private def text (value : String) : PrereleaseIdentifier :=
  .text value

private def numeric (value : Nat) : PrereleaseIdentifier :=
  .numeric value

-- SemVer 2.0.0 precedence example:
-- alpha < alpha.1 < alpha.beta < beta < beta.2 < beta.11 < rc.1 < release

example : Version.precedence (pre [text "alpha"]) (pre [text "alpha", numeric 1]) = .lt := by
  decide

example : Version.precedence (pre [text "alpha", numeric 1]) (pre [text "alpha", text "beta"]) = .lt := by
  decide

example : Version.precedence (pre [text "alpha", text "beta"]) (pre [text "beta"]) = .lt := by
  decide

example : Version.precedence (pre [text "beta"]) (pre [text "beta", numeric 2]) = .lt := by
  decide

example : Version.precedence (pre [text "beta", numeric 2]) (pre [text "beta", numeric 11]) = .lt := by
  decide

example : Version.precedence (pre [text "beta", numeric 11]) (pre [text "rc", numeric 1]) = .lt := by
  decide

example : Version.precedence (pre [text "rc", numeric 1]) release = .lt := by
  decide

-- Version identity and precedence are deliberately different.
example : releaseWithBuild ["left"] ≠ releaseWithBuild ["right"] := by
  decide

example :
    Version.precedence
      (releaseWithBuild ["left"])
      (releaseWithBuild ["right"]) = .eq := by
  decide

example :
    Version.precedenceKey (releaseWithBuild ["left"]) =
      Version.precedenceKey (releaseWithBuild ["right"]) := by
  decide
