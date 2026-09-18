import Semverifier.Caret

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def caret (raw : String) : ComparatorSet :=
  (Caret.parse? raw).getD { comparators := [] }

example :
    Caret.upperBound (version "1.2.3") =
      { major := 2, minor := 0, patch := 0, prerelease := [.numeric 0] } := by
  native_decide

example :
    Caret.upperBound (version "0.2.3") =
      { major := 0, minor := 3, patch := 0, prerelease := [.numeric 0] } := by
  native_decide

example :
    Caret.upperBound (version "0.0.3") =
      { major := 0, minor := 0, patch := 4, prerelease := [.numeric 0] } := by
  native_decide

example :
    (caret "^1.2.3").satisfies (version "1.2.3") = true := by
  native_decide

example :
    (caret "^1.2.3").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (caret "^1.2.3").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (caret "^1.2.3").satisfies (version "2.0.0-alpha") = false := by
  native_decide

example :
    (caret "^0.2.3").satisfies (version "0.2.99") = true := by
  native_decide

example :
    (caret "^0.2.3").satisfies (version "0.3.0") = false := by
  native_decide

example :
    (caret "^0.0.3").satisfies (version "0.0.3") = true := by
  native_decide

example :
    (caret "^0.0.3").satisfies (version "0.0.4") = false := by
  native_decide

-- Pre-release admission stays delegated to ComparatorSet.
example :
    (caret "^1.2.3-beta.2").satisfies
      (version "1.2.3-beta.4") = true := by
  native_decide

example :
    (caret "^1.2.3-beta.2").satisfies
      (version "1.2.4-beta.1") = false := by
  native_decide

example :
    (caret "^1.2.3-beta.2").satisfies
      (version "1.2.4") = true := by
  native_decide

-- Build metadata has no effect on the caret's semantic lower bound.
example :
    (caret "^1.2.3+build.7").satisfies
      (version "1.2.3+other") = true := by
  native_decide

-- Partial-version caret syntax remains deliberately out of scope.
example : Caret.parse? "^1.2" = none := by
  native_decide

example : Caret.parse? "^1" = none := by
  native_decide

example : Caret.parse? "1.2.3" = none := by
  native_decide
