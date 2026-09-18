import Semverifier.Comparator

namespace Semverifier

/--
A conjunction of primitive comparators.

A candidate must satisfy every primitive comparator. Pre-release candidates
also pass the npm/node-semver admission rule: at least one comparator bound in
the set must itself be a pre-release of the same major/minor/patch tuple.
-/
structure ComparatorSet where
  comparators : List Comparator
deriving Repr, BEq, DecidableEq

namespace ComparatorSet

private def sameCore (left right : Version) : Bool :=
  left.major == right.major &&
    left.minor == right.minor &&
    left.patch == right.patch

/--
Default pre-release admission used by node-semver comparator sets.

Normal releases are always eligible for comparator testing. A pre-release
candidate is eligible only if this set explicitly mentions a pre-release bound
with the same core tuple.
-/
def prereleaseAdmitted (set : ComparatorSet) (candidate : Version) : Bool :=
  if candidate.prerelease.isEmpty then
    true
  else
    set.comparators.any fun comparator =>
      !comparator.bound.prerelease.isEmpty &&
        sameCore comparator.bound candidate

/-- Decide whether a version satisfies one comparator set. -/
def satisfies (set : ComparatorSet) (candidate : Version) : Bool :=
  set.comparators.all (fun comparator => comparator.satisfies candidate) &&
    set.prereleaseAdmitted candidate

end ComparatorSet
end Semverifier
