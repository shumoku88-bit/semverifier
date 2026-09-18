import Semverifier.Tilde

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def tilde (raw : String) : ComparatorSet :=
  (Tilde.parse? raw).getD { comparators := [] }

example :
    Tilde.upperBound (version "1.2.3") =
      { major := 1, minor := 3, patch := 0, prerelease := [.numeric 0] } := by
  native_decide

example :
    Tilde.upperBound (version "0.2.3") =
      { major := 0, minor := 3, patch := 0, prerelease := [.numeric 0] } := by
  native_decide

example :
    Tilde.upperBound (version "0.0.1") =
      { major := 0, minor := 1, patch := 0, prerelease := [.numeric 0] } := by
  native_decide

example :
    (tilde "~1.2.3").satisfies (version "1.2.3") = true := by
  native_decide

example :
    (tilde "~1.2.3").satisfies (version "1.2.99") = true := by
  native_decide

example :
    (tilde "~1.2.3").satisfies (version "1.3.0") = false := by
  native_decide

example :
    (tilde "~0.0.1").satisfies (version "0.0.9") = true := by
  native_decide

example :
    (tilde "~0.0.1").satisfies (version "0.1.0") = false := by
  native_decide

example :
    (tilde "~1.2.3-beta.2").satisfies
      (version "1.2.3-beta.4") = true := by
  native_decide

example :
    (tilde "~1.2.3-beta.2").satisfies
      (version "1.2.4-beta.1") = false := by
  native_decide

example :
    (tilde "~1.2.3-beta.2").satisfies
      (version "1.2.4") = true := by
  native_decide

example :
    (tilde "~1.2.3+build.7").satisfies
      (version "1.2.3+other") = true := by
  native_decide

-- Partial tilde ranges reuse the bare X-range boundary.
example : Tilde.parse? "~1" = XRange.parseBare? "1" := by
  native_decide

example : Tilde.parse? "~1.2" = XRange.parseBare? "1.2" := by
  native_decide

example : Tilde.parse? "~1.x" = XRange.parseBare? "1.x" := by
  native_decide

example : Tilde.parse? "~1.2.x" = XRange.parseBare? "1.2.x" := by
  native_decide

example : Tilde.parse? "~*" = XRange.parseBare? "*" := by
  native_decide

example :
    (tilde "~1").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (tilde "~1").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (tilde "~1.2").satisfies (version "1.2.99") = true := by
  native_decide

example :
    (tilde "~1.2").satisfies (version "1.3.0") = false := by
  native_decide

example :
    (tilde "~1.2.x").satisfies (version "1.2.7") = true := by
  native_decide

example :
    (tilde "~*").satisfies (version "9.9.9") = true := by
  native_decide

example :
    (tilde "~*").satisfies (version "9.9.9-alpha") = false := by
  native_decide

example : Tilde.parse? "~>1.2.3" = none := by
  native_decide

example : Tilde.parse? "~>1.2" = none := by
  native_decide

example : Tilde.parse? "~<1.2" = none := by
  native_decide

example : Tilde.parse? "1.2.3" = none := by
  native_decide
