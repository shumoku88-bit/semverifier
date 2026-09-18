import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "1.2.7 || >=1.2.9 <2.0.0").satisfies
      (version "1.2.7") = true := by
  native_decide

example :
    (parsedRange "1.2.7 || >=1.2.9 <2.0.0").satisfies
      (version "1.2.8") = false := by
  native_decide

example :
    (parsedRange "1.2.7 || >=1.2.9 <2.0.0").satisfies
      (version "1.5.0") = true := by
  native_decide

example :
    (parsedRange "1.2.7 || >=1.2.9 <2.0.0").satisfies
      (version "2.0.0") = false := by
  native_decide

-- Prerelease admission is branch-local.
example :
    (parsedRange ">1.2.3-alpha.3 || >=3.0.0").satisfies
      (version "1.2.3-alpha.7") = true := by
  native_decide

example :
    (parsedRange ">1.2.3-alpha.3 || >=3.0.0").satisfies
      (version "3.4.5-alpha.9") = false := by
  native_decide

example :
    (parsedRange ">1.2.3-alpha.3 || >=3.0.0-alpha").satisfies
      (version "3.0.0-beta") = true := by
  native_decide

-- Empty branches behave like the empty range branch: any stable release.
example :
    (parsedRange "").satisfies (version "9.9.9") = true := by
  native_decide

example :
    (parsedRange "").satisfies (version "9.9.9-alpha") = false := by
  native_decide

example :
    (parsedRange ">=1.2.3 || ").satisfies (version "0.1.0") = true := by
  native_decide

-- Advanced range sugar is still rejected by branch parsing.
example : Range.parse? "^1.2.3 || ~2.0.0" = none := by
  native_decide
