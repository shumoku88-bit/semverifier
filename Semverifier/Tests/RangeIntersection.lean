import Semverifier.RangeIntersection

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    Range.findIntersectionWitness?
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=1.5.0 <3.0.0") =
      some (version "1.5.0") := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=2.0.0 <3.0.0") =
      none := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange ">1.2.3-alpha")
      (parsedRange "<1.2.3-beta") =
      some (version "1.2.3-alpha.0") := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange ">1.2.3-alpha")
      (parsedRange "<1.2.3-alpha.0") =
      none := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange "1.2.3-alpha")
      (parsedRange ">=1.2.3-alpha <=1.2.3-alpha") =
      some (version "1.2.3-alpha") := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange "*")
      (parsedRange "<1.0.0") =
      some (version "0.0.0") := by
  native_decide

example :
    Range.findIntersectionWitness?
      (parsedRange ">=1.2.3-alpha")
      (parsedRange "<2.0.0") =
      some (version "1.2.3") := by
  native_decide

example :
    Range.overlapsAt
      (parsedRange ">=1.2.3-alpha")
      (parsedRange "<2.0.0")
      (version "1.2.3-beta") = false := by
  native_decide

example :
    Range.Intersects
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=1.5.0 <3.0.0") := by
  apply Range.findIntersectionWitness?_sound
    (candidate := version "1.5.0")
  native_decide

example :
    Range.intersects
      (parsedRange "1.2.3-alpha.2")
      (parsedRange "1.2.3-alpha.2 - 1.2.3") = true := by
  native_decide

example :
    Range.intersects
      (parsedRange "1.2.3-alpha.2 - 1.2.3")
      (parsedRange "1.2.3-alpha.2") = true := by
  native_decide

example :
    Range.intersects
      (parsedRange "1.x")
      (parsedRange "2.x") = false := by
  native_decide

example :
    Range.intersects
      (parsedRange "1.2.3-alpha.2")
      (parsedRange "1.2.3-alpha.2 - 1.2.3") =
    Range.intersects
      (parsedRange "1.2.3-alpha.2 - 1.2.3")
      (parsedRange "1.2.3-alpha.2") := by
  exact Range.intersects_commutative _ _

