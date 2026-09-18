import Semverifier.RangeAlgebra

namespace Semverifier

namespace Range

private def minimumStable : Version :=
  { major := 0, minor := 0, patch := 0 }

private def stableAtCore (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch
  }

private def nextStablePatch (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch + 1
  }

private def prereleaseFloorAtCore (version : Version) : Version :=
  {
    major := version.major
    minor := version.minor
    patch := version.patch
    prerelease := [.numeric 0]
  }

private def strippedBound (version : Version) : Version :=
  { version with build := [] }

private def prereleaseSuccessor (version : Version) : Version :=
  {
    strippedBound version with
    prerelease := version.prerelease ++ [.numeric 0]
  }

/--
Finite boundary candidates contributed by one primitive comparator.

Stable candidates include the release at the bound's core and the next patch
release. A prerelease bound additionally contributes the lowest prerelease at
that core, the bound itself, and the immediate prefix extension obtained by
appending numeric zero.

The list may contain duplicates. Keeping generation simple is more important
than deduplication at this stage.
-/
private def boundaryCandidates (comparator : Comparator) : List Version :=
  let bound := comparator.bound
  let stable := stableAtCore bound
  let nextStable := nextStablePatch bound
  if bound.prerelease.isEmpty then
    [stable, nextStable]
  else
    [
      stable,
      nextStable,
      prereleaseFloorAtCore bound,
      strippedBound bound,
      prereleaseSuccessor bound
    ]

/--
One canonical stable lower-bound candidate contributed by a comparator.

Upper-only comparators contribute the global minimum stable release. Inclusive
lower bounds and equality contribute the stable release at the bound's core.
A strict lower bound on a stable release advances one patch; a strict lower
bound on a prerelease can use the stable release at the same core.
-/
private def stableFloorCandidate (comparator : Comparator) : Version :=
  match comparator.operator with
  | .lt | .lte => minimumStable
  | .gte | .eq => stableAtCore comparator.bound
  | .gt =>
      if comparator.bound.prerelease.isEmpty then
        nextStablePatch comparator.bound
      else
        stableAtCore comparator.bound

/--
Every per-comparator stable floor is already represented by the existing
critical-boundary construction, except for the global minimum which is added
once at comparator-set-pair level.
-/
private theorem stableFloorCandidate_eq_minimum_or_mem_boundary
    (comparator : Comparator) :
    stableFloorCandidate comparator = minimumStable ∨
      stableFloorCandidate comparator ∈ boundaryCandidates comparator := by
  cases comparator with
  | mk operator bound =>
      cases hPrerelease : bound.prerelease.isEmpty <;>
        cases operator <;>
          simp [stableFloorCandidate, boundaryCandidates, hPrerelease]

private def comparatorSetCandidates (set : ComparatorSet) : List Version :=
  set.comparators.flatMap boundaryCandidates

/--
Critical-boundary pool for one pair of conjunctive comparator sets.
-/
def comparatorSetIntersectionCandidates
    (left right : ComparatorSet) : List Version :=
  minimumStable :: (comparatorSetCandidates left ++ comparatorSetCandidates right)

/--
The local completeness obligation for one pair of comparator sets.

If the two conjunctions have a common semantic witness, one of their generated
critical-boundary candidates must also satisfy both conjunctions.
-/
def ComparatorSetPairCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
Stable-witness half of comparator-set-pair candidate completeness.

This isolates the ordinary release-ordering problem from node-semver's
set-local prerelease admission rule.
-/
def ComparatorSetPairStableCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      candidate.prerelease.isEmpty = true ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
Prerelease-witness half of comparator-set-pair candidate completeness.

Unlike the stable case, this branch must preserve the same-core prerelease
admission carried by each comparator set.
-/
def ComparatorSetPairPrereleaseCandidatesComplete
    (left right : ComparatorSet) : Prop :=
  (∃ candidate,
      candidate.prerelease.isEmpty = false ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true) →
    ∃ candidate,
      candidate ∈ comparatorSetIntersectionCandidates left right ∧
      left.satisfies candidate = true ∧
      right.satisfies candidate = true

/--
The local completeness obligation splits exactly into stable and prerelease
witness cases.
-/
theorem comparatorSetPairCandidatesComplete_of_stable_and_prerelease
    (left right : ComparatorSet)
    (hStable : ComparatorSetPairStableCandidatesComplete left right)
    (hPrerelease : ComparatorSetPairPrereleaseCandidatesComplete left right) :
    ComparatorSetPairCandidatesComplete left right := by
  intro hWitness
  rcases hWitness with ⟨candidate, hLeft, hRight⟩
  cases hEmpty : candidate.prerelease.isEmpty with
  | false =>
      exact hPrerelease ⟨candidate, hEmpty, hLeft, hRight⟩
  | true =>
      exact hStable ⟨candidate, hEmpty, hLeft, hRight⟩

private def rangeBoundaryCandidates (range : Range) : List Version :=
  range.sets.flatMap comparatorSetCandidates

/--
Finite candidate pool used by the first intersection witness search.

This pool is deliberately exposed for inspection. At this stage Semverifier
proves only soundness of returned witnesses; completeness of this finite pool
is a separate theorem still to be established.
-/
def intersectionCandidates (left right : Range) : List Version :=
  minimumStable ::
    (rangeBoundaryCandidates left ++ rangeBoundaryCandidates right)

private def firstOverlap?
    (left right : Range) :
    List Version → Option Version
  | [] => none
  | candidate :: rest =>
      if overlapsAt left right candidate then
        some candidate
      else
        firstOverlap? left right rest

/--
Search the finite critical-boundary pool for a concrete intersection witness.

A returned version is proved sound below. Returning `none` does not yet mean
that the ranges are disjoint; that conclusion waits for a completeness proof
for `intersectionCandidates`.
-/
def findIntersectionWitness? (left right : Range) : Option Version :=
  firstOverlap? left right (intersectionCandidates left right)

/--
The one remaining mathematical obligation for global completeness of the finite
intersection search.

It says that whenever the semantic ranges intersect, at least one generated
critical-boundary candidate is itself a concrete overlap witness.
-/
def IntersectionCandidatesComplete (left right : Range) : Prop :=
  Intersects left right →
    ∃ candidate,
      candidate ∈ intersectionCandidates left right ∧
      overlapsAt left right candidate = true

private theorem comparatorSetCandidate_mem_rangeCandidates
    (range : Range)
    (set : ComparatorSet)
    (hSet : set ∈ range.sets)
    (candidate : Version)
    (hCandidate : candidate ∈ comparatorSetCandidates set) :
    candidate ∈ rangeBoundaryCandidates range := by
  simp only [rangeBoundaryCandidates, List.mem_flatMap]
  exact ⟨set, hSet, hCandidate⟩

private theorem comparatorSetIntersectionCandidate_mem_intersectionCandidates
    (left right : Range)
    (leftSet rightSet : ComparatorSet)
    (hLeftSet : leftSet ∈ left.sets)
    (hRightSet : rightSet ∈ right.sets)
    (candidate : Version)
    (hCandidate :
      candidate ∈ comparatorSetIntersectionCandidates leftSet rightSet) :
    candidate ∈ intersectionCandidates left right := by
  simp only [
    comparatorSetIntersectionCandidates,
    List.mem_cons,
    List.mem_append
  ] at hCandidate
  rcases hCandidate with hMinimum | hLeft | hRight
  · subst candidate
    simp [intersectionCandidates]
  · have hInLeft :=
      comparatorSetCandidate_mem_rangeCandidates
        left leftSet hLeftSet candidate hLeft
    simp [intersectionCandidates, hInLeft]
  · have hInRight :=
      comparatorSetCandidate_mem_rangeCandidates
        right rightSet hRightSet candidate hRight
    simp [intersectionCandidates, hInRight]

/--
Range-level candidate completeness follows from completeness of every
conjunctive comparator-set pair.

This removes `||` union structure from the remaining global proof obligation.
-/
theorem intersectionCandidatesComplete_of_comparator_set_pairs
    (left right : Range)
    (hPairs :
      ∀ leftSet,
        leftSet ∈ left.sets →
        ∀ rightSet,
          rightSet ∈ right.sets →
          ComparatorSetPairCandidatesComplete leftSet rightSet) :
    IntersectionCandidatesComplete left right := by
  intro hIntersects
  rcases hIntersects with ⟨witness, hLeft, hRight⟩
  unfold Contains at hLeft hRight
  rcases
      (Range.satisfies_eq_true_iff left witness).mp hLeft with
    ⟨leftSet, hLeftSet, hLeftWitness⟩
  rcases
      (Range.satisfies_eq_true_iff right witness).mp hRight with
    ⟨rightSet, hRightSet, hRightWitness⟩
  have hPairWitness :
      ∃ candidate,
        leftSet.satisfies candidate = true ∧
        rightSet.satisfies candidate = true :=
    ⟨witness, hLeftWitness, hRightWitness⟩
  rcases
      hPairs leftSet hLeftSet rightSet hRightSet hPairWitness with
    ⟨candidate, hCandidate, hLeftCandidate, hRightCandidate⟩
  refine ⟨candidate, ?_, ?_⟩
  · exact
      comparatorSetIntersectionCandidate_mem_intersectionCandidates
        left right leftSet rightSet
        hLeftSet hRightSet candidate hCandidate
  · apply (overlapsAt_eq_true_iff left right candidate).mpr
    constructor
    · unfold Contains
      exact
        (Range.satisfies_eq_true_iff left candidate).mpr
          ⟨leftSet, hLeftSet, hLeftCandidate⟩
    · unfold Contains
      exact
        (Range.satisfies_eq_true_iff right candidate).mpr
          ⟨rightSet, hRightSet, hRightCandidate⟩

private theorem firstOverlap?_exists_some_of_mem_overlap
    (left right : Range)
    (candidates : List Version)
    (h :
      ∃ candidate,
        candidate ∈ candidates ∧
        overlapsAt left right candidate = true) :
    ∃ candidate, firstOverlap? left right candidates = some candidate := by
  induction candidates with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases hHead : overlapsAt left right head with
      | false =>
          have hTail :
              ∃ candidate,
                candidate ∈ tail ∧
                overlapsAt left right candidate = true := by
            rcases h with ⟨candidate, hMem, hOverlap⟩
            rcases List.mem_cons.mp hMem with hEq | hMemTail
            · subst candidate
              simp [hHead] at hOverlap
            · exact ⟨candidate, hMemTail, hOverlap⟩
          rcases ih hTail with ⟨candidate, hFound⟩
          exact ⟨candidate, by simp [firstOverlap?, hHead, hFound]⟩
      | true =>
          exact ⟨head, by simp [firstOverlap?, hHead]⟩

private theorem firstOverlap?_sound
    (left right : Range)
    (candidates : List Version)
    (candidate : Version)
    (h : firstOverlap? left right candidates = some candidate) :
    overlapsAt left right candidate = true := by
  induction candidates with
  | nil =>
      simp [firstOverlap?] at h
  | cons head tail ih =>
      by_cases hOverlap : overlapsAt left right head = true
      · simp [firstOverlap?, hOverlap] at h
        subst candidate
        exact hOverlap
      · have hFalse : overlapsAt left right head = false := by
          cases hValue : overlapsAt left right head <;> simp_all
        simp [firstOverlap?, hFalse] at h
        exact ih h

/-- Any returned witness is accepted by both ranges. -/
theorem findIntersectionWitness?_overlaps
    (left right : Range)
    (candidate : Version)
    (h : findIntersectionWitness? left right = some candidate) :
    overlapsAt left right candidate = true := by
  exact firstOverlap?_sound
    left
    right
    (intersectionCandidates left right)
    candidate
    h

/-- Any returned witness proves semantic intersection. -/
theorem findIntersectionWitness?_sound
    (left right : Range)
    (candidate : Version)
    (h : findIntersectionWitness? left right = some candidate) :
    Intersects left right := by
  have hOverlap :=
    findIntersectionWitness?_overlaps left right candidate h
  have hBoth :=
    (overlapsAt_eq_true_iff left right candidate).mp hOverlap
  exact ⟨candidate, hBoth.1, hBoth.2⟩

/--
Once the critical-boundary candidate pool is complete, the existing finite
search is complete as an algorithm: every semantic intersection produces a
returned witness.
-/
theorem findIntersectionWitness?_complete
    (left right : Range)
    (hCandidates : IntersectionCandidatesComplete left right)
    (hIntersects : Intersects left right) :
    ∃ candidate, findIntersectionWitness? left right = some candidate := by
  have hCandidate := hCandidates hIntersects
  simpa [findIntersectionWitness?] using
    firstOverlap?_exists_some_of_mem_overlap
      left
      right
      (intersectionCandidates left right)
      hCandidate

/--
Under the candidate-completeness obligation, returning `none` is equivalent to
semantic disjointness.
-/
theorem findIntersectionWitness?_none_iff_not_intersects
    (left right : Range)
    (hCandidates : IntersectionCandidatesComplete left right) :
    findIntersectionWitness? left right = none ↔
      ¬ Intersects left right := by
  constructor
  · intro hNone hIntersects
    rcases
      findIntersectionWitness?_complete
        left right hCandidates hIntersects with
      ⟨candidate, hSome⟩
    rw [hNone] at hSome
    contradiction
  · intro hNotIntersects
    cases hSearch : findIntersectionWitness? left right with
    | none =>
        rfl
    | some candidate =>
        have hIntersects :=
          findIntersectionWitness?_sound left right candidate hSearch
        exact (hNotIntersects hIntersects).elim

end Range
end Semverifier
