import Semverifier.ComparatorSet

namespace Semverifier

namespace XRange

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

private def isWildcard (raw : String) : Bool :=
  raw == "x" || raw == "X" || raw == "*"

private def lowerVersion (major minor patch : Nat) : Version :=
  { major, minor, patch }

private def majorUpperBound (major : Nat) : Version :=
  {
    major := major + 1
    minor := 0
    patch := 0
    prerelease := zeroPrerelease
  }

private def minorUpperBound (major minor : Nat) : Version :=
  {
    major
    minor := minor + 1
    patch := 0
    prerelease := zeroPrerelease
  }

private def majorRange (major : Nat) : ComparatorSet :=
  {
    comparators := [
      { operator := .gte, bound := lowerVersion major 0 0 },
      { operator := .lt, bound := majorUpperBound major }
    ]
  }

private def minorRange (major minor : Nat) : ComparatorSet :=
  {
    comparators := [
      { operator := .gte, bound := lowerVersion major minor 0 },
      { operator := .lt, bound := minorUpperBound major minor }
    ]
  }

/-- The unconstrained default range under ordinary prerelease admission. -/
def any : ComparatorSet :=
  { comparators := [] }

/--
Parse bare partial versions and X-ranges into the existing comparator-set
kernel.

Supported forms:

- `*`, `x`, `X`
- `1`, `1.x`, `1.X`, `1.*`, `1.x.x`
- `1.2`, `1.2.x`, `1.2.X`, `1.2.*`

Complete versions remain owned by the primitive-comparator parser. Operator-
prefixed partial ranges such as `>1` are intentionally outside this boundary.
-/
def parse? (raw : String) : Option ComparatorSet :=
  let parts := raw.split "." |>.toStringList
  match parts with
  | [majorRaw] =>
      if isWildcard majorRaw then
        some any
      else do
        let major ← parseNumericIdentifier? majorRaw
        some (majorRange major)
  | [majorRaw, minorRaw] => do
      let major ← parseNumericIdentifier? majorRaw
      if isWildcard minorRaw then
        some (majorRange major)
      else do
        let minor ← parseNumericIdentifier? minorRaw
        some (minorRange major minor)
  | [majorRaw, minorRaw, patchRaw] => do
      let major ← parseNumericIdentifier? majorRaw
      if isWildcard minorRaw then
        if isWildcard patchRaw then
          some (majorRange major)
        else
          none
      else do
        let minor ← parseNumericIdentifier? minorRaw
        if isWildcard patchRaw then
          some (minorRange major minor)
        else
          none
  | _ => none

end XRange
end Semverifier
