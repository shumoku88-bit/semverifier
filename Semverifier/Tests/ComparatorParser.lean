import Semverifier.Comparator

open Semverifier

private def parsedComparator (raw : String) : Comparator :=
  (Comparator.parse? raw).getD {
    operator := .eq
    bound := { major := 0, minor := 0, patch := 0 }
  }

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

example : (Comparator.parse? ">=1.2.7").isSome = true := by
  native_decide

example : (Comparator.parse? "<=1.2.7").isSome = true := by
  native_decide

example : (Comparator.parse? ">1.2.7").isSome = true := by
  native_decide

example : (Comparator.parse? "<1.2.7").isSome = true := by
  native_decide

example : (Comparator.parse? "=1.2.7").isSome = true := by
  native_decide

example : (Comparator.parse? "1.2.7").isSome = true := by
  native_decide

example :
    (parsedComparator ">=1.2.7").satisfies (version "1.3.0") = true := by
  native_decide

example :
    (parsedComparator "<1.2.7").satisfies (version "1.2.7") = false := by
  native_decide

example :
    (parsedComparator "=1.0.0+left").satisfies
      (version "1.0.0+right") = true := by
  native_decide

-- Partial versions and higher-level range syntax remain outside primitive parsing.
example : Comparator.parse? ">1" = none := by
  native_decide

example : Comparator.parse? ">=1.2" = none := by
  native_decide

example : Comparator.parse? "^1.2.3" = none := by
  native_decide

example : Comparator.parse? "~1.2.3" = none := by
  native_decide

example : Comparator.parse? ">=01.2.3" = none := by
  native_decide

example : Comparator.parse? ">>1.2.3" = none := by
  native_decide

example : Comparator.parse? "" = none := by
  native_decide
