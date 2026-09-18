import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "~1.2.3").satisfies (version "1.2.9") = true := by
  native_decide

example :
    (parsedRange "~1.2.3").satisfies (version "1.3.0") = false := by
  native_decide

example :
    (parsedRange "~1.2.3 <1.2.8").satisfies (version "1.2.7") = true := by
  native_decide

example :
    (parsedRange "~1.2.3 <1.2.8").satisfies (version "1.2.8") = false := by
  native_decide

example :
    (parsedRange "~1.2.3 || ^2.0.0").satisfies (version "1.2.8") = true := by
  native_decide

example :
    (parsedRange "~1.2.3 || ^2.0.0").satisfies (version "2.5.0") = true := by
  native_decide

example :
    (parsedRange "~1.2.3 || ^2.0.0").satisfies (version "1.5.0") = false := by
  native_decide

example :
    (parsedRange "~1.2.3-beta.2").satisfies
      (version "1.2.3-beta.4") = true := by
  native_decide

example :
    (parsedRange "~1.2.3-beta.2").satisfies
      (version "1.2.4-beta.1") = false := by
  native_decide

example : Range.parse? "~1.2" = none := by
  native_decide

example : Range.parse? "~>1.2.3" = none := by
  native_decide
