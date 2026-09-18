import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "^1.2.3").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (parsedRange "^1.2.3").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (parsedRange "^0.2.3").satisfies (version "0.2.9") = true := by
  native_decide

example :
    (parsedRange "^0.2.3").satisfies (version "0.3.0") = false := by
  native_decide

example :
    (parsedRange "^1.2.3 <1.5.0").satisfies (version "1.4.9") = true := by
  native_decide

example :
    (parsedRange "^1.2.3 <1.5.0").satisfies (version "1.5.0") = false := by
  native_decide

example :
    (parsedRange "^1.2.3 || >=3.0.0").satisfies (version "1.8.0") = true := by
  native_decide

example :
    (parsedRange "^1.2.3 || >=3.0.0").satisfies (version "3.2.0") = true := by
  native_decide

example :
    (parsedRange "^1.2.3 || >=3.0.0").satisfies (version "2.5.0") = false := by
  native_decide

example :
    (parsedRange "^1.2.3-beta.2").satisfies
      (version "1.2.3-beta.4") = true := by
  native_decide

example :
    (parsedRange "^1.2.3-beta.2").satisfies
      (version "1.2.4-beta.1") = false := by
  native_decide

-- Partial carets flow through the same Range frontend.
example :
    (parsedRange "^1.2").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (parsedRange "^1.2").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (parsedRange "^0.2").satisfies (version "0.2.9") = true := by
  native_decide

example :
    (parsedRange "^0.2").satisfies (version "0.3.0") = false := by
  native_decide

example :
    (parsedRange "^0.0").satisfies (version "0.0.9") = true := by
  native_decide

example :
    (parsedRange "^0.0").satisfies (version "0.1.0") = false := by
  native_decide

example :
    (parsedRange "^0").satisfies (version "0.9.9") = true := by
  native_decide

example :
    (parsedRange "^0").satisfies (version "1.0.0") = false := by
  native_decide

example :
    (parsedRange "^0.2.x <0.2.8").satisfies (version "0.2.7") = true := by
  native_decide

example :
    (parsedRange "^0.2.x <0.2.8").satisfies (version "0.2.8") = false := by
  native_decide

example :
    (parsedRange "^0.2 || ^2.5").satisfies (version "2.7.0") = true := by
  native_decide

example :
    (parsedRange "^0.2 || ^2.5").satisfies (version "1.5.0") = false := by
  native_decide

example :
    (parsedRange "^*").satisfies (version "7.8.9") = true := by
  native_decide

example :
    (parsedRange "^*").satisfies (version "7.8.9-alpha") = false := by
  native_decide
