import Semverifier.XRange

namespace Semverifier

namespace HyphenRange

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

private def prereleaseFloor (major minor patch : Nat) : Version :=
  {
    major
    minor
    patch
    prerelease := zeroPrerelease
  }

private def stableVersion (major minor patch : Nat) : Version :=
  { major, minor, patch }

private inductive Endpoint where
  | full (version : Version)
  | incomplete (shape : XRange.Partial)

private def parseEndpoint? (raw : String) : Option Endpoint :=
  match Version.parse? raw with
  | some version => some (.full version)
  | none => (XRange.parsePartial? raw).map Endpoint.incomplete

private def lowerComparators : Endpoint → List Comparator
  | .full version =>
      [
        {
          operator := .gte
          bound := { version with build := [] }
        }
      ]
  | .incomplete .any =>
      []
  | .incomplete (.major major) =>
      [
        {
          operator := .gte
          bound := stableVersion major 0 0
        }
      ]
  | .incomplete (.minor major minor) =>
      [
        {
          operator := .gte
          bound := stableVersion major minor 0
        }
      ]

private def upperComparators : Endpoint → List Comparator
  | .full version =>
      [
        {
          operator := .lte
          bound := { version with build := [] }
        }
      ]
  | .incomplete .any =>
      []
  | .incomplete (.major major) =>
      [
        {
          operator := .lt
          bound := prereleaseFloor (major + 1) 0 0
        }
      ]
  | .incomplete (.minor major minor) =>
      [
        {
          operator := .lt
          bound := prereleaseFloor major (minor + 1) 0
        }
      ]

private def tokens (raw : String) : List String :=
  raw.split Char.isWhitespace
    |>.toStringList
    |>.filter (fun token => !token.isEmpty)

/--
Parse a strict hyphen range and desugar it into the existing comparator-set
kernel.

The whole branch must have the form `left - right` with whitespace around the
hyphen. Endpoints may be complete versions or partial/X-range tuples.

Examples:

- `1.2.3 - 2.3.4` -> `>=1.2.3 <=2.3.4`
- `1.2 - 3.4.5` -> `>=1.2.0 <=3.4.5`
- `1.2.3 - 3.4` -> `>=1.2.3 <3.5.0-0`
- `1 - 2` -> `>=1.0.0 <3.0.0-0`

No new satisfaction semantics are introduced.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let parts := tokens raw
  match parts with
  | [leftRaw, "-", rightRaw] =>
      let left ← parseEndpoint? leftRaw
      let right ← parseEndpoint? rightRaw
      some {
        comparators := lowerComparators left ++ upperComparators right
      }
  | _ =>
      none

end HyphenRange
end Semverifier
