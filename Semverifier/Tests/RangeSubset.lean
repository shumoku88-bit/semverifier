import Semverifier.RangeSubset

open Semverifier

private def parsedRange (raw : String) : Range :=
  (Range.parse? raw).getD { sets := [] }

example :
    (Range.findSubsetCounterexample?
      (parsedRange ">=1.0.0 <3.0.0")
      (parsedRange ">=1.2.0 <2.0.0")).isSome = true := by
  native_decide

example :
    Range.findSubsetCounterexample?
      (parsedRange ">=1.2.0 <2.0.0")
      (parsedRange ">=1.0.0 <3.0.0") = none := by
  native_decide

example
    (candidate : Version)
    (h :
      Range.findSubsetCounterexample?
        (parsedRange ">=1.0.0 <3.0.0")
        (parsedRange ">=1.2.0 <2.0.0") =
          some candidate) :
    Range.Contains
        (parsedRange ">=1.0.0 <3.0.0")
        candidate ∧
      ¬ Range.Contains
        (parsedRange ">=1.2.0 <2.0.0")
        candidate :=
  Range.findSubsetCounterexample?_counterexample _ _ _ h
