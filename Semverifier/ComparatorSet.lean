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

private def tokens (raw : String) : List String :=
  raw.split Char.isWhitespace
    |>.toStringList
    |>.filter (fun token => !token.isEmpty)

/--
Parse one whitespace-separated comparator set.

The empty string and whitespace-only input produce the empty set, matching the
empty-range branch of node-semver's grammar. Higher-level range operators such
as `||`, caret, tilde, wildcards, and partial versions remain outside this
parser and are rejected by the primitive-comparator boundary.
-/
def parse? (raw : String) : Option ComparatorSet := do
  let comparators ← (tokens raw).mapM Comparator.parse?
  some { comparators }

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

/--
Executable conjunction semantics, exposed propositionally.

A comparator set satisfies a candidate exactly when every primitive comparator
does and the candidate passes the set-local prerelease admission rule.
-/
theorem satisfies_eq_true_iff
    (set : ComparatorSet)
    (candidate : Version) :
    set.satisfies candidate = true ↔
      (∀ comparator ∈ set.comparators,
        comparator.satisfies candidate = true) ∧
      set.prereleaseAdmitted candidate = true := by
  simp [satisfies]

/--
Stable candidates are admitted by every comparator set.

The node-semver prerelease gate is therefore irrelevant in the stable branch
of the intersection-completeness proof.
-/
theorem prereleaseAdmitted_of_stable
    (set : ComparatorSet)
    (candidate : Version)
    (hStable : candidate.prerelease.isEmpty = true) :
    set.prereleaseAdmitted candidate = true := by
  simp [prereleaseAdmitted, hStable]

/--
For a stable candidate, comparator-set satisfaction is exactly conjunction of
its primitive comparator constraints.
-/
theorem satisfies_eq_true_iff_stable
    (set : ComparatorSet)
    (candidate : Version)
    (hStable : candidate.prerelease.isEmpty = true) :
    set.satisfies candidate = true ↔
      ∀ comparator ∈ set.comparators,
        comparator.satisfies candidate = true := by
  constructor
  · intro h
    exact ((satisfies_eq_true_iff set candidate).mp h).1
  · intro hComparators
    exact
      (satisfies_eq_true_iff set candidate).mpr
        ⟨hComparators, prereleaseAdmitted_of_stable set candidate hStable⟩

/--
For a prerelease candidate, set-local admission is exactly the existence of a
prerelease comparator bound with the same major/minor/patch core.
-/
theorem prereleaseAdmitted_eq_true_iff_of_prerelease
    (set : ComparatorSet)
    (candidate : Version)
    (hPrerelease : candidate.prerelease.isEmpty = false) :
    set.prereleaseAdmitted candidate = true ↔
      ∃ comparator ∈ set.comparators,
        comparator.bound.prerelease.isEmpty = false ∧
        comparator.bound.major = candidate.major ∧
        comparator.bound.minor = candidate.minor ∧
        comparator.bound.patch = candidate.patch := by
  simp [
    prereleaseAdmitted,
    hPrerelease,
    sameCore,
    Bool.not_eq_true
  ]

/--
Any prerelease version accepted by a comparator set carries a concrete
same-core prerelease admission anchor inside that set.
-/
theorem exists_prerelease_anchor_of_satisfies
    (set : ComparatorSet)
    (candidate : Version)
    (hPrerelease : candidate.prerelease.isEmpty = false)
    (hSatisfies : set.satisfies candidate = true) :
    ∃ comparator ∈ set.comparators,
      comparator.bound.prerelease.isEmpty = false ∧
      comparator.bound.major = candidate.major ∧
      comparator.bound.minor = candidate.minor ∧
      comparator.bound.patch = candidate.patch := by
  have hAdmitted :
      set.prereleaseAdmitted candidate = true :=
    ((satisfies_eq_true_iff set candidate).mp hSatisfies).2
  exact
    (prereleaseAdmitted_eq_true_iff_of_prerelease
      set candidate hPrerelease).mp hAdmitted

end ComparatorSet
end Semverifier
