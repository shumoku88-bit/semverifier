import Semverifier.Parser

open Semverifier

private def parsed (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

example :
    Version.parse? "1.2.3" =
      some { major := 1, minor := 2, patch := 3 } := by
  native_decide

example : (Version.parse? "1.0.0-alpha").isSome = true := by
  native_decide

example : (Version.parse? "1.0.0-alpha.1").isSome = true := by
  native_decide

example : (Version.parse? "1.0.0-alpha-beta").isSome = true := by
  native_decide

example : (Version.parse? "1.0.0-x-y-z.--").isSome = true := by
  native_decide

example : (Version.parse? "1.0.0+001").isSome = true := by
  native_decide

example : (Version.parse? "1.0.0-alpha+001").isSome = true := by
  native_decide

example : Version.parse? "01.0.0" = none := by
  native_decide

example : Version.parse? "1.01.0" = none := by
  native_decide

example : Version.parse? "1.0.01" = none := by
  native_decide

example : Version.parse? "1.0" = none := by
  native_decide

example : Version.parse? "1.0.0-" = none := by
  native_decide

example : Version.parse? "1.0.0-alpha..1" = none := by
  native_decide

example : Version.parse? "1.0.0-01" = none := by
  native_decide

example : Version.parse? "1.0.0-alpha_1" = none := by
  native_decide

example : Version.parse? "1.0.0+build..7" = none := by
  native_decide

example : Version.parse? "1.0.0+build+again" = none := by
  native_decide

example : Version.parse? "1.0.0-é" = none := by
  native_decide

example :
    Version.precedence
      (parsed "1.0.0-alpha")
      (parsed "1.0.0") = .lt := by
  native_decide

example :
    Version.precedence
      (parsed "1.0.0+left")
      (parsed "1.0.0+right") = .eq := by
  native_decide
