import Semverifier.Comparator

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def comparator
    (operator : ComparatorOperator)
    (bound : String) : Comparator :=
  { operator, bound := version bound }

example :
    (comparator .gte "1.2.7").satisfies (version "1.2.7") = true := by
  native_decide

example :
    (comparator .gte "1.2.7").satisfies (version "1.2.6") = false := by
  native_decide

example :
    (comparator .lt "2.0.0").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (comparator .lt "2.0.0").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (comparator .lte "1.2.3").satisfies (version "1.2.3") = true := by
  native_decide

example :
    (comparator .gt "1.2.3-alpha.3").satisfies
      (version "1.2.3-alpha.4") = true := by
  native_decide

example :
    (comparator .eq "1.0.0+left").satisfies
      (version "1.0.0+right") = true := by
  native_decide

example : version "1.0.0+left" ≠ version "1.0.0+right" := by
  native_decide

example :
    (comparator .eq "1.0.0-alpha").satisfies
      (version "1.0.0") = false := by
  native_decide
