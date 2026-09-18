import Semverifier.Identifier

open Semverifier

example : PrereleaseIdentifier.parse? "" = none := by
  decide

example : PrereleaseIdentifier.parse? "0" = some (.numeric 0) := by
  decide

example : PrereleaseIdentifier.parse? "7" = some (.numeric 7) := by
  decide

example : PrereleaseIdentifier.parse? "01" = none := by
  decide

example : (PrereleaseIdentifier.parse? "alpha").isSome = true := by
  decide

example : (PrereleaseIdentifier.parse? "01a").isSome = true := by
  decide

example : (PrereleaseIdentifier.parse? "-").isSome = true := by
  decide

example : PrereleaseIdentifier.parse? "alpha_1" = none := by
  decide

example : PrereleaseIdentifier.parse? "alpha.1" = none := by
  decide

example : PrereleaseIdentifier.parse? "é" = none := by
  decide
