import Semverifier.ComparatorSet

namespace Semverifier

namespace XRange

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

private def isWildcard (raw : String) : Bool :=
  raw == "x" || raw == "X" || raw == "*"

private def lowerVersion (major minor patch : Nat) : Version :=
  { major, minor, patch }

private def prereleaseFloor (major minor patch : Nat) : Version :=
  {
    major
    minor
    patch
    prerelease := zeroPrerelease
  }

private def majorUpperBound (major : Nat) : Version :=
  prereleaseFloor (major + 1) 0 0

private def minorUpperBound (major minor : Nat) : Version :=
  prereleaseFloor major (minor + 1) 0

private def singleton
    (operator : ComparatorOperator)
    (bound : Version) : ComparatorSet :=
  {
    comparators := [
      { operator, bound }
    ]
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

private def nullSet : ComparatorSet :=
  singleton .lt (prereleaseFloor 0 0 0)

/--
The canonical syntactic shapes of an incomplete SemVer tuple.

This type is shared by frontends whose semantics depend on which components
were omitted, rather than only on the zero-filled lower version.
-/
inductive Partial where
  | any
  | major (major : Nat)
  | minor (major minor : Nat)
deriving Repr, BEq, DecidableEq

/--
Parse a bare partial version or X-range into its canonical tuple shape.

Complete versions are intentionally excluded.
-/
def parsePartial? (raw : String) : Option Partial :=
  let parts := raw.split "." |>.toStringList
  match parts with
  | [majorRaw] =>
      if isWildcard majorRaw then
        some .any
      else do
        let major ← parseNumericIdentifier? majorRaw
        some (.major major)
  | [majorRaw, minorRaw] => do
      let major ← parseNumericIdentifier? majorRaw
      if isWildcard minorRaw then
        some (.major major)
      else do
        let minor ← parseNumericIdentifier? minorRaw
        some (.minor major minor)
  | [majorRaw, minorRaw, patchRaw] => do
      let major ← parseNumericIdentifier? majorRaw
      if isWildcard minorRaw then
        if isWildcard patchRaw then
          some (.major major)
        else
          none
      else do
        let minor ← parseNumericIdentifier? minorRaw
        if isWildcard patchRaw then
          some (.minor major minor)
        else
          none
  | _ => none

private def splitOperator
    (raw : String) : Option ComparatorOperator × String :=
  if let some rest := raw.dropPrefix? "<=" then
    (some .lte, rest.toString)
  else if let some rest := raw.dropPrefix? ">=" then
    (some .gte, rest.toString)
  else if let some rest := raw.dropPrefix? "<" then
    (some .lt, rest.toString)
  else if let some rest := raw.dropPrefix? ">" then
    (some .gt, rest.toString)
  else if let some rest := raw.dropPrefix? "=" then
    (some .eq, rest.toString)
  else
    (none, raw)

private def bareRange : Partial → ComparatorSet
  | .any => any
  | .major major => majorRange major
  | .minor major minor => minorRange major minor

private def operatorRange
    (operator : ComparatorOperator)
    (shape : Partial) : ComparatorSet :=
  match operator, shape with
  | .eq, shape =>
      bareRange shape
  | .gte, .any =>
      any
  | .gte, .major major =>
      singleton .gte (lowerVersion major 0 0)
  | .gte, .minor major minor =>
      singleton .gte (lowerVersion major minor 0)
  | .gt, .any =>
      nullSet
  | .gt, .major major =>
      singleton .gte (lowerVersion (major + 1) 0 0)
  | .gt, .minor major minor =>
      singleton .gte (lowerVersion major (minor + 1) 0)
  | .lt, .any =>
      nullSet
  | .lt, .major major =>
      singleton .lt (prereleaseFloor major 0 0)
  | .lt, .minor major minor =>
      singleton .lt (prereleaseFloor major minor 0)
  | .lte, .any =>
      any
  | .lte, .major major =>
      singleton .lt (majorUpperBound major)
  | .lte, .minor major minor =>
      singleton .lt (minorUpperBound major minor)

/--
Parse only a bare partial version or X-range.

This entry point intentionally excludes comparator operators so other frontends
can reuse the canonical partial-version boundaries without accidentally
admitting their own operator syntax.
-/
def parseBare? (raw : String) : Option ComparatorSet := do
  let shape ← parsePartial? raw
  some (bareRange shape)

/--
Parse partial versions and X-ranges into the existing comparator-set kernel.

Bare forms desugar to intervals:

- `1`, `1.x` -> `>=1.0.0 <2.0.0-0`
- `1.2`, `1.2.x` -> `>=1.2.0 <1.3.0-0`

Operator-prefixed partials follow node-semver's X-range boundary rules:

- `>1` -> `>=2.0.0`
- `>1.2` -> `>=1.3.0`
- `>=1.2` -> `>=1.2.0`
- `<1.2` -> `<1.2.0-0`
- `<=1.2` -> `<1.3.0-0`

Complete versions remain owned by the primitive-comparator parser.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let (operator?, partialRaw) := splitOperator raw
  match operator? with
  | none => parseBare? partialRaw
  | some operator => do
      let shape ← parsePartial? partialRaw
      some (operatorRange operator shape)

end XRange
end Semverifier
