import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "1.2.3 - 2.3.4").satisfies (version "1.2.3") = true := by
  native_decide

example :
    (parsedRange "1.2.3 - 2.3.4").satisfies (version "2.3.4") = true := by
  native_decide

example :
    (parsedRange "1.2.3 - 2.3.4").satisfies (version "2.3.5") = false := by
  native_decide

example :
    (parsedRange "1.2 - 3.4").satisfies (version "1.2.0") = true := by
  native_decide

example :
    (parsedRange "1.2 - 3.4").satisfies (version "3.4.99") = true := by
  native_decide

example :
    (parsedRange "1.2 - 3.4").satisfies (version "3.5.0") = false := by
  native_decide

example :
    (parsedRange "0.2.x - 1.3.x").satisfies (version "0.2.0") = true := by
  native_decide

example :
    (parsedRange "0.2.x - 1.3.x").satisfies (version "1.3.99") = true := by
  native_decide

example :
    (parsedRange "0.2.x - 1.3.x").satisfies (version "1.4.0") = false := by
  native_decide

example :
    (parsedRange "* - 1.2.3").satisfies (version "0.0.0") = true := by
  native_decide

example :
    (parsedRange "* - 1.2.3").satisfies (version "1.2.4") = false := by
  native_decide

example :
    (parsedRange "1.2.3 - *").satisfies (version "9.9.9") = true := by
  native_decide

example :
    (parsedRange "1.2.3-alpha.2 - 1.2.3").satisfies
      (version "1.2.3-beta.1") = true := by
  native_decide

example :
    (parsedRange "1.2.3-alpha.2 - 1.2.3").satisfies
      (version "1.2.4-alpha.1") = false := by
  native_decide

example :
    (parsedRange "1.2 - 2.3 || ^4.0").satisfies (version "2.3.9") = true := by
  native_decide

example :
    (parsedRange "1.2 - 2.3 || ^4.0").satisfies (version "4.5.0") = true := by
  native_decide

example :
    (parsedRange "1.2 - 2.3 || ^4.0").satisfies (version "3.0.0") = false := by
  native_decide

-- Hyphen syntax owns a complete branch. Mixing trailing comparator syntax is
-- deliberately rejected, matching node-semver's anchored strict hyphen form.
example : Range.parse? "1.2 - 2.3 <3.0.0" = none := by
  native_decide

example : Range.parse? "1.2 -2.3" = none := by
  native_decide
