import Semverifier.HyphenRange

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def hyphen (raw : String) : ComparatorSet :=
  (HyphenRange.parse? raw).getD { comparators := [] }

example :
    HyphenRange.parse? "1.2.3 - 2.3.4" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.3" },
          { operator := .lte, bound := version "2.3.4" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "1.2 - 3.4.5" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.0" },
          { operator := .lte, bound := version "3.4.5" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "1.2.3 - 3.4" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.3" },
          { operator := .lt, bound := version "3.5.0-0" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "1.2 - 3.4" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.0" },
          { operator := .lt, bound := version "3.5.0-0" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "1 - 2" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.0.0" },
          { operator := .lt, bound := version "3.0.0-0" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "* - 1.2" =
      some {
        comparators := [
          { operator := .lt, bound := version "1.3.0-0" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "1.2 - *" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.0" }
        ]
      } := by
  native_decide

example :
    HyphenRange.parse? "* - *" =
      some { comparators := [] } := by
  native_decide

example :
    HyphenRange.parse? "1.2.3+build.7 - 1.2.4+build.9" =
      some {
        comparators := [
          { operator := .gte, bound := version "1.2.3" },
          { operator := .lte, bound := version "1.2.4" }
        ]
      } := by
  native_decide

example :
    (hyphen "1.2.3 - 2.3.4").satisfies (version "1.2.3") = true := by
  native_decide

example :
    (hyphen "1.2.3 - 2.3.4").satisfies (version "2.3.4") = true := by
  native_decide

example :
    (hyphen "1.2.3 - 2.3.4").satisfies (version "2.3.5") = false := by
  native_decide

example :
    (hyphen "1.2.3 - 3.4").satisfies (version "3.4.99") = true := by
  native_decide

example :
    (hyphen "1.2.3 - 3.4").satisfies (version "3.5.0") = false := by
  native_decide

example :
    (hyphen "1.2.3-alpha.2 - 1.2.3").satisfies
      (version "1.2.3-beta.1") = true := by
  native_decide

example :
    (hyphen "1.2.3-alpha.2 - 1.2.3").satisfies
      (version "1.2.4-alpha.1") = false := by
  native_decide

example :
    (hyphen "* - *").satisfies (version "9.9.9") = true := by
  native_decide

example :
    (hyphen "* - *").satisfies (version "9.9.9-alpha") = false := by
  native_decide

-- Strict hyphen syntax requires whitespace around the standalone hyphen.
example : HyphenRange.parse? "1.2-2.3" = none := by
  native_decide

example : HyphenRange.parse? "1.2 -2.3" = none := by
  native_decide

example : HyphenRange.parse? "1.2- 2.3" = none := by
  native_decide

-- A hyphen range owns the whole branch, not a prefix of another expression.
example : HyphenRange.parse? "1.2 - 2.3 <3.0.0" = none := by
  native_decide
