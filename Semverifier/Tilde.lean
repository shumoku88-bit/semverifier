import Semverifier.XRange

namespace Semverifier

namespace Tilde

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

/--
Exclusive upper bound for a complete-version tilde range.

For a full version `M.m.p`, tilde permits patch-level movement within the same
minor line, so the upper bound is `M.(m+1).0-0`.
-/
def upperBound (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor + 1
    patch := 0
    prerelease := zeroPrerelease
  }

/--
Desugar one complete-version tilde into the existing comparator-set kernel.

Build metadata is removed from the lower bound because it has no precedence
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

private def dropTildePrefix? (raw : String) : Option String :=
  if let some rest := raw.dropPrefix? "~>" then
    some rest.toString
  else if let some rest := raw.dropPrefix? "~" then
    some rest.toString
  else
    none

/--
Parse tilde syntax into the existing comparator-set kernel.

Complete versions retain the existing tilde rule:

- `~1.2.3` -> `>=1.2.3 <1.3.0-0`

Partial versions reuse the canonical bare X-range boundaries:

- `~1`, `~1.x` -> `>=1.0.0 <2.0.0-0`
- `~1.2`, `~1.2.x` -> `>=1.2.0 <1.3.0-0`
- `~*` -> the unconstrained comparator set

The npm `~>` alias is accepted as an exact synonym for `~`; both prefixes
share the same desugaring path.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let body ← dropTildePrefix? raw
  match Version.parse? body with
  | some version => some (desugar version)
  | none => XRange.parseBare? body

end Tilde
end Semverifier
