import Semverifier.XRange

namespace Semverifier

namespace Caret

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

private def lowerVersion (major minor patch : Nat) : Version :=
  { major, minor, patch }

private def prereleaseFloor (major minor patch : Nat) : Version :=
  {
    major
    minor
    patch
    prerelease := zeroPrerelease
  }

/--
Upper bound for a full-version caret range.

For a complete version, caret compatibility allows changes that do not modify
the left-most non-zero component. The upper bound is exclusive and carries
`-0`, matching node-semver's desugaring boundary.
-/
def upperBound (version : Version) : Version :=
  if version.major != 0 then
    prereleaseFloor (version.major + 1) 0 0
  else if version.minor != 0 then
    prereleaseFloor 0 (version.minor + 1) 0
  else
    prereleaseFloor 0 0 (version.patch + 1)

/--
Desugar one complete-version caret into the existing comparator-set kernel.

Build metadata is dropped from the lower bound because it has no precedence
effect. Pre-release data is preserved.
-/
def desugar (version : Version) : ComparatorSet :=
  let lower : Version := { version with build := [] }
  {
    comparators := [
      { operator := .gte, bound := lower },
      { operator := .lt, bound := upperBound version }
    ]
  }

/--
Desugar an incomplete caret tuple while preserving which components were
omitted.

For partial carets, omission is semantically significant:

- `^M` permits the whole major line, including `^0`;
- `^M.m` permits the whole major line when `M != 0`;
- `^0.m` permits the matching minor line.

This matches node-semver's X-aware caret boundary rules.
-/
def desugarPartial : XRange.Partial → ComparatorSet
  | .any =>
      XRange.any
  | .major major =>
      {
        comparators := [
          { operator := .gte, bound := lowerVersion major 0 0 },
          { operator := .lt, bound := prereleaseFloor (major + 1) 0 0 }
        ]
      }
  | .minor major minor =>
      let upper :=
        if major == 0 then
          prereleaseFloor 0 (minor + 1) 0
        else
          prereleaseFloor (major + 1) 0 0
      {
        comparators := [
          { operator := .gte, bound := lowerVersion major minor 0 },
          { operator := .lt, bound := upper }
        ]
      }

/--
Parse caret syntax into the existing comparator-set kernel.

Complete versions retain the existing left-most-non-zero rule. Partial and
X-range forms preserve omission information before desugaring, so boundaries
such as `^0` and `^0.0` remain distinct.

Examples:

- `^1` -> `>=1.0.0 <2.0.0-0`
- `^1.2` -> `>=1.2.0 <2.0.0-0`
- `^0` -> `>=0.0.0 <1.0.0-0`
- `^0.2` -> `>=0.2.0 <0.3.0-0`
- `^0.0` -> `>=0.0.0 <0.1.0-0`
-/
def parse? (raw : String) : Option ComparatorSet := do
  let rest ← raw.dropPrefix? "^"
  let body := rest.toString
  match Version.parse? body with
  | some version => some (desugar version)
  | none => do
      let shape ← XRange.parsePartial? body
      some (desugarPartial shape)

end Caret
end Semverifier
