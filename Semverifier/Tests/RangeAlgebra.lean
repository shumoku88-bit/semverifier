import Semverifier.Range

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (parsedRange "1.2.7").satisfies (version "1.2.7") = true := by
  native_decide

example :
    Range.satisfies
      (Range.union (parsedRange "1.2.7") (parsedRange ">=2.0.0"))
      (version "2.1.0") = true := by
  native_decide
