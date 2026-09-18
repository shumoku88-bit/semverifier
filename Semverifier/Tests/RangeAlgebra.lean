import Semverifier.RangeAlgebra

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

example :
    Range.overlapsAt
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=1.5.0 <3.0.0")
      (version "1.5.0") = true := by
  native_decide

example :
    Range.Intersects
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=1.5.0 <3.0.0") := by
  refine ⟨version "1.5.0", ?_, ?_⟩ <;> native_decide

example :
    Range.SubsetOf
      (parsedRange "1.2.7")
      (Range.union (parsedRange "1.2.7") (parsedRange ">=2.0.0")) :=
  Range.subset_union_left _ _

example :
    Range.Equivalent
      (parsedRange ">=1.0.0 <2.0.0")
      (parsedRange ">=1.0.0 <2.0.0") :=
  Range.equivalent_refl _

/-
Default prerelease admission makes semantic intersection different from simply
joining comparator syntax into one comparator set.

The combined syntax below admits 1.2.3-beta because the prerelease comparator
and the upper bound live in the same set.
-/
example :
    (parsedRange ">=1.2.3-alpha <2.0.0").satisfies
      (version "1.2.3-beta") = true := by
  native_decide

/-
But as two independent ranges, <2.0.0 does not admit prereleases at all.
Therefore the same candidate is not a witness of their mathematical
intersection.
-/
example :
    Range.overlapsAt
      (parsedRange ">=1.2.3-alpha")
      (parsedRange "<2.0.0")
      (version "1.2.3-beta") = false := by
  native_decide
