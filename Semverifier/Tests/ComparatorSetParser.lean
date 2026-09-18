import Semverifier.ComparatorSet

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedSet (raw : String) : ComparatorSet :=
  (ComparatorSet.parse? raw).getD { comparators := [] }

example : (ComparatorSet.parse? ">=1.2.7 <2.0.0").isSome = true := by
  native_decide

example : (ComparatorSet.parse? "  >=1.2.7   <2.0.0  ").isSome = true := by
  native_decide

example : (ComparatorSet.parse? ">=1.2.7\t<2.0.0").isSome = true := by
  native_decide

example : (ComparatorSet.parse? "").isSome = true := by
  native_decide

example : (ComparatorSet.parse? "   ").isSome = true := by
  native_decide

example :
    (parsedSet ">=1.2.7 <2.0.0").satisfies (version "1.5.0") = true := by
  native_decide

example :
    (parsedSet ">=1.2.7 <2.0.0").satisfies (version "2.0.0") = false := by
  native_decide

example :
    (parsedSet ">1.2.3-alpha.3").satisfies
      (version "1.2.3-alpha.7") = true := by
  native_decide

example :
    (parsedSet ">1.2.3-alpha.3").satisfies
      (version "3.4.5-alpha.9") = false := by
  native_decide

-- Empty comparator sets behave like the empty range branch: stable versions
-- satisfy vacuously, prereleases remain excluded by default admission.
example :
    (parsedSet "").satisfies (version "1.0.0") = true := by
  native_decide

example :
    (parsedSet "").satisfies (version "1.0.0-alpha") = false := by
  native_decide

-- Higher-level range syntax remains outside this parser.
example : ComparatorSet.parse? ">=1.2.7 || <2.0.0" = none := by
  native_decide

example : ComparatorSet.parse? "^1.2.3" = none := by
  native_decide

example : ComparatorSet.parse? ">1" = none := by
  native_decide
