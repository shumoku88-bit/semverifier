import Semverifier.ComparatorSet

open Semverifier

private def version (raw : String) : Version :=
  (Version.parse? raw).getD { major := 0, minor := 0, patch := 0 }

private def comparator (raw : String) : Comparator :=
  (Comparator.parse? raw).getD {
    operator := .eq
    bound := { major := 0, minor := 0, patch := 0 }
  }

private def set (raw : List String) : ComparatorSet :=
  { comparators := raw.map comparator }

example :
    (set [">=1.2.7", "<2.0.0"]).satisfies
      (version "1.5.0") = true := by
  native_decide

example :
    (set [">=1.2.7", "<2.0.0"]).satisfies
      (version "2.0.0") = false := by
  native_decide

-- The comparator itself says 3.4.5-alpha.9 is greater than 1.2.3-alpha.3.
example :
    (comparator ">1.2.3-alpha.3").satisfies
      (version "3.4.5-alpha.9") = true := by
  native_decide

-- The comparator set rejects that prerelease because no 3.4.5 prerelease was named.
example :
    (set [">1.2.3-alpha.3"]).satisfies
      (version "3.4.5-alpha.9") = false := by
  native_decide

-- The same core prerelease is explicitly admitted.
example :
    (set [">1.2.3-alpha.3"]).satisfies
      (version "1.2.3-alpha.7") = true := by
  native_decide

-- A later stable release is not blocked by prerelease admission.
example :
    (set [">1.2.3-alpha.3"]).satisfies
      (version "3.4.5") = true := by
  native_decide

example :
    (set [">=1.2.3", "<2.0.0"]).satisfies
      (version "1.3.0-beta.1") = false := by
  native_decide

example :
    (set [">=1.2.3-alpha", "<2.0.0"]).satisfies
      (version "1.2.3-beta.1") = true := by
  native_decide

-- An empty set admits stable releases but not prereleases by default.
example :
    (set []).satisfies (version "1.0.0") = true := by
  native_decide

example :
    (set []).satisfies (version "1.0.0-alpha") = false := by
  native_decide
