import Semverifier.ComparatorSet

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

/--
Parse a complete-version tilde expression such as `~1.2.3`.

Partial versions (`~1.2`, `~1`) and the npm alias `~>` intentionally remain
outside this boundary for now.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let rest ← raw.dropPrefix? "~"
  let version ← Version.parse? rest.toString
  some (desugar version)

end Tilde
end Semverifier
