import Semverifier.XRange

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def xrange (raw : String) : ComparatorSet :=
  (XRange.parse? raw).getD { comparators := [] }

example :
    (xrange "*").satisfies (version "9.9.9") = true := by
  native_decide

example :
    (xrange "*").satisfies (version "9.9.9-alpha") = false := by
  native_decide

example :
    (xrange "1").satisfies (version "1.0.0") = true := by
  native_decide

example :
    (xrange "1").satisfies (version "1.9.9") = true := by
  native_decide

example :
    (xrange "1").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (xrange "1.x").satisfies (version "1.7.3") = true := by
  native_decide

example :
    (xrange "1.X").satisfies (version "1.7.3") = true := by
  native_decide

example :
    (xrange "1.*").satisfies (version "1.7.3") = true := by
  native_decide

example :
    (xrange "1.x.x").satisfies (version "1.7.3") = true := by
  native_decide

example :
    (xrange "1.2").satisfies (version "1.2.0") = true := by
  native_decide

example :
    (xrange "1.2").satisfies (version "1.2.99") = true := by
  native_decide

example :
    (xrange "1.2").satisfies (version "1.3.0") = false := by
  native_decide

example :
    (xrange "1.2.x").satisfies (version "1.2.8") = true := by
  native_decide

example :
    (xrange "1.2.X").satisfies (version "1.2.8") = true := by
  native_decide

example :
    (xrange "1.2.*").satisfies (version "1.2.8") = true := by
  native_decide

example : XRange.parse? "1.x.3" = none := by
  native_decide

example : XRange.parse? "x.2.3" = none := by
  native_decide

example : XRange.parse? "1.2.3" = none := by
  native_decide

example : XRange.parse? ">1" = none := by
  native_decide

example : XRange.parse? "01.2" = none := by
  native_decide
