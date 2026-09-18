import Semverifier.Range

namespace Semverifier

namespace Caret

private def zeroPrerelease : List PrereleaseIdentifier :=
  [.numeric 0]

/--
Upper bound for a full-version caret range.

For a complete version, caret compatibility allows changes that do not modify
the left-most non-zero component. The upper bound is exclusive and carries
`-0`, matching node-semver's desugaring boundary.
-/
def upperBound (version : Version) : Version :=
  if version.major != 0 then
    {
      major := version.major + 1
      minor := 0
      patch := 0
      prerelease := zeroPrerelease
    }
  else if version.minor != 0 then
    {
      major := 0
      minor := version.minor + 1
      patch := 0
      prerelease := zeroPrerelease
    }
  else
    {
      major := 0
      minor := 0
      patch := version.patch + 1
      prerelease := zeroPrerelease
    }

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
Parse a complete-version caret expression such as `^1.2.3`.

Partial versions (`^1.2`, `^1`) intentionally remain outside this boundary.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let rest ← raw.dropPrefix? "^"
  let version ← Version.parse? rest.toString
  some (desugar version)

end Caret
end Semverifier
