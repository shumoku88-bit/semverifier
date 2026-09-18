import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "*").satisfies (version "7.8.9") = true := by
  native_decide

example :
    (parsedRange "*").satisfies (version "7.8.9-alpha") = false := by
  native_decide

example :
    (parsedRange "1").satisfies (version "1.8.0") = true := by
  native_decide

example :
    (parsedRange "1").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (parsedRange "1.x").satisfies (version "1.8.0") = true := by
  native_decide

example :
    (parsedRange "1.2").satisfies (version "1.2.99") = true := by
  native_decide

example :
    (parsedRange "1.2").satisfies (version "1.3.0") = false := by
  native_decide

example :
    (parsedRange "1.2.x").satisfies (version "1.2.7") = true := by
  native_decide

example :
    (parsedRange "1.2.x || ^2.0.0").satisfies (version "1.2.8") = true := by
  native_decide

example :
    (parsedRange "1.2.x || ^2.0.0").satisfies (version "2.4.0") = true := by
  native_decide

example :
    (parsedRange "1.2.x || ^2.0.0").satisfies (version "1.4.0") = false := by
  native_decide

example :
    (parsedRange "1.x <1.5.0").satisfies (version "1.4.9") = true := by
  native_decide

example :
    (parsedRange "1.x <1.5.0").satisfies (version "1.5.0") = false := by
  native_decide

-- Operator-prefixed partial versions remain outside this frontend.
example : Range.parse? ">1" = none := by
  native_decide

example : Range.parse? "<=1.2" = none := by
  native_decide
