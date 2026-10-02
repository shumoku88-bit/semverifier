import Semverifier.RangeIntersection

namespace Semverifier

namespace Range

/--
A candidate is a concrete counterexample to `sub ⊆ dom` when the candidate is
accepted by `sub` and rejected by `dom`.
-/
def subsetCounterexampleAt
    (sub dom : Range)
    (candidate : Version) : Bool :=
  sub.satisfies candidate && !dom.satisfies candidate

/-- Boolean counterexamples agree with the extensional subset meaning. -/
theorem subsetCounterexampleAt_eq_true_iff
    (sub dom : Range)
    (candidate : Version) :
    subsetCounterexampleAt sub dom candidate = true ↔
      Contains sub candidate ∧ ¬ Contains dom candidate := by
  simp [subsetCounterexampleAt, Contains]

/-- There is a semantic witness that `sub` is not contained in `dom`. -/
def HasSubsetCounterexample
    (sub dom : Range) : Prop :=
  ∃ candidate,
    Contains sub candidate ∧
    ¬ Contains dom candidate

/--
Finite boundary pool explored for subset counterexamples.

It reuses the proved intersection critical-boundary pool. The completeness
theorem later in this file shows that this shared pool is sufficient for
subset counterexamples too.
-/
def subsetCounterexampleCandidates
    (sub dom : Range) : List Version :=
  intersectionCandidates sub dom

private def firstSubsetCounterexample?
    (sub dom : Range) :
    List Version → Option Version
  | [] => none
  | candidate :: rest =>
      if subsetCounterexampleAt sub dom candidate then
        some candidate
      else
        firstSubsetCounterexample? sub dom rest

/-- Search the finite critical-boundary pool for a concrete subset failure. -/
def findSubsetCounterexample?
    (sub dom : Range) : Option Version :=
  firstSubsetCounterexample?
    sub dom
    (subsetCounterexampleCandidates sub dom)

/--
Completeness property for the finite subset-counterexample pool.

It is phrased using an explicit semantic witness rather than classical
negation of a universal subset statement, keeping the proof constructive.
-/
def SubsetCounterexampleCandidatesComplete
    (sub dom : Range) : Prop :=
  HasSubsetCounterexample sub dom →
    ∃ candidate,
      candidate ∈ subsetCounterexampleCandidates sub dom ∧
      subsetCounterexampleAt sub dom candidate = true

private theorem listAll_eq_false_of_mem_false
    {α : Type}
    (items : List α)
    (predicate : α → Bool)
    (item : α)
    (hMem : item ∈ items)
    (hFalse : predicate item = false) :
    items.all predicate = false := by
  induction items with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      rcases List.mem_cons.mp hMem with hEq | hTail
      · subst item
        simp [hFalse]
      · cases hHead : predicate head with
        | false =>
            simp [hHead]
        | true =>
            simp [hHead, ih item hTail hFalse]

private theorem exists_mem_false_of_listAll_eq_false
    {α : Type}
    (items : List α)
    (predicate : α → Bool)
    (hAll : items.all predicate = false) :
    ∃ item,
      item ∈ items ∧
      predicate item = false := by
  induction items with
  | nil =>
      simp at hAll
  | cons head tail ih =>
      cases hHead : predicate head with
      | false =>
          exact ⟨head, List.mem_cons_self, hHead⟩
      | true =>
          have hTail : tail.all predicate = false := by
            simpa [hHead] using hAll
          rcases ih hTail with ⟨item, hMem, hFalse⟩
          exact
            ⟨item,
              List.mem_cons_of_mem head hMem,
              hFalse⟩

private theorem listAny_eq_false_of_all_false
    {α : Type}
    (items : List α)
    (predicate : α → Bool)
    (h :
      ∀ item,
        item ∈ items →
        predicate item = false) :
    items.any predicate = false := by
  induction items with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead := h head List.mem_cons_self
      have hTail :
          ∀ item,
            item ∈ tail →
            predicate item = false := by
        intro item hMem
        exact h item (List.mem_cons_of_mem head hMem)
      simp [hHead, ih hTail]

private theorem listAny_eq_true_of_mem_true
    {α : Type}
    (items : List α)
    (predicate : α → Bool)
    (item : α)
    (hMem : item ∈ items)
    (hTrue : predicate item = true) :
    items.any predicate = true := by
  induction items with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      rcases List.mem_cons.mp hMem with hEq | hTail
      · subst item
        simp [hTrue]
      · cases hHead : predicate head with
        | true =>
            simp [hHead]
        | false =>
            simp [hHead, ih item hTail hTrue]

/--
One primitive condition that witnesses rejection by a source comparator.

For non-equality operators this is the exact Boolean complement. For equality,
the original witness chooses the strict side on which it lies.
-/
private def rejectingComparator
    (source : Comparator)
    (witness : Version) : Comparator :=
  match source.operator with
  | .lt =>
      { operator := .gte, bound := source.bound }
  | .lte =>
      { operator := .gt, bound := source.bound }
  | .gt =>
      { operator := .lte, bound := source.bound }
  | .gte =>
      { operator := .lt, bound := source.bound }
  | .eq =>
      match Version.precedence witness source.bound with
      | .gt =>
          { operator := .gt, bound := source.bound }
      | .lt | .eq =>
          { operator := .lt, bound := source.bound }

private theorem rejectingComparator_bound
    (source : Comparator)
    (witness : Version) :
    (rejectingComparator source witness).bound =
      source.bound := by
  cases source with
  | mk operator bound =>
      cases operator with
      | lt => rfl
      | lte => rfl
      | gt => rfl
      | gte => rfl
      | eq =>
          cases Version.precedence witness bound <;> rfl

private theorem rejectingComparator_satisfies_of_source_false
    (source : Comparator)
    (witness : Version)
    (hSource : source.satisfies witness = false) :
    (rejectingComparator source witness).satisfies witness = true := by
  cases source with
  | mk operator bound =>
      cases hPrecedence : Version.precedence witness bound <;>
        cases operator <;>
        simp [
          Comparator.satisfies,
          rejectingComparator,
          hPrecedence
        ] at hSource ⊢

private theorem source_false_of_rejectingComparator_satisfies
    (source : Comparator)
    (witness candidate : Version)
    (hSourceWitness : source.satisfies witness = false)
    (hRejecting :
      (rejectingComparator source witness).satisfies candidate = true) :
    source.satisfies candidate = false := by
  cases source with
  | mk operator bound =>
      cases hWitnessPrecedence :
          Version.precedence witness bound <;>
        cases hCandidatePrecedence :
          Version.precedence candidate bound <;>
        cases operator <;>
        simp [
          Comparator.satisfies,
          rejectingComparator,
          hWitnessPrecedence,
          hCandidatePrecedence
        ] at hSourceWitness hRejecting ⊢

private theorem boundaryCandidates_eq_of_bound_eq
    (left right : Comparator)
    (hBound : left.bound = right.bound) :
    boundaryCandidates left = boundaryCandidates right := by
  cases left with
  | mk leftOperator leftBound =>
      cases right with
      | mk rightOperator rightBound =>
          simp at hBound
          subst rightBound
          rfl

private def rejectingComparators
    (set : ComparatorSet)
    (witness : Version) : List Comparator :=
  set.comparators.flatMap fun source =>
    if source.satisfies witness then
      []
    else
      [rejectingComparator source witness]

private def domainRejectingComparators
    (dom : Range)
    (witness : Version) : List Comparator :=
  dom.sets.flatMap fun set =>
    rejectingComparators set witness

private def counterexampleComparatorSet
    (leftSet : ComparatorSet)
    (dom : Range)
    (witness : Version) : ComparatorSet :=
  {
    comparators :=
      leftSet.comparators ++
        domainRejectingComparators dom witness
  }

private theorem rejectingComparator_mem_domain
    (dom : Range)
    (witness : Version)
    (set : ComparatorSet)
    (hSet : set ∈ dom.sets)
    (source : Comparator)
    (hSource : source ∈ set.comparators)
    (hFalse : source.satisfies witness = false) :
    rejectingComparator source witness ∈
      domainRejectingComparators dom witness := by
  unfold domainRejectingComparators
  apply List.mem_flatMap.mpr
  refine ⟨set, hSet, ?_⟩
  unfold rejectingComparators
  apply List.mem_flatMap.mpr
  refine ⟨source, hSource, ?_⟩
  simp [hFalse]

private theorem mem_domainRejectingComparators_source
    (dom : Range)
    (witness : Version)
    (rejecting : Comparator)
    (hRejecting :
      rejecting ∈ domainRejectingComparators dom witness) :
    ∃ set,
      set ∈ dom.sets ∧
      ∃ source,
        source ∈ set.comparators ∧
        source.satisfies witness = false ∧
        rejecting = rejectingComparator source witness := by
  unfold domainRejectingComparators at hRejecting
  rcases List.mem_flatMap.mp hRejecting with
    ⟨set, hSet, hInSet⟩
  unfold rejectingComparators at hInSet
  rcases List.mem_flatMap.mp hInSet with
    ⟨source, hSource, hInOne⟩
  cases hValue : source.satisfies witness with
  | true =>
      simp [hValue] at hInOne
  | false =>
      have hEq :
          rejecting = rejectingComparator source witness := by
        simpa [hValue] using hInOne
      exact
        ⟨set,
          hSet,
          source,
          hSource,
          hValue,
          hEq⟩

private theorem domainRejectingComparators_satisfy_witness
    (dom : Range)
    (witness : Version)
    (rejecting : Comparator)
    (hRejecting :
      rejecting ∈ domainRejectingComparators dom witness) :
    rejecting.satisfies witness = true := by
  rcases
      mem_domainRejectingComparators_source
        dom witness rejecting hRejecting with
    ⟨set,
      hSet,
      source,
      hSource,
      hFalse,
      hEq⟩
  subst rejecting
  exact
    rejectingComparator_satisfies_of_source_false
      source witness hFalse

private theorem counterexampleSet_satisfies_stable_witness
    (leftSet : ComparatorSet)
    (dom : Range)
    (witness : Version)
    (hStable : witness.prerelease.isEmpty = true)
    (hLeft : leftSet.satisfies witness = true) :
    (counterexampleComparatorSet
      leftSet dom witness).satisfies witness = true := by
  apply
    (ComparatorSet.satisfies_eq_true_iff_stable
      (counterexampleComparatorSet leftSet dom witness)
      witness
      hStable).mpr
  intro comparator hComparator
  have hLeftPrimitive :=
    ((ComparatorSet.satisfies_eq_true_iff
      leftSet witness).mp hLeft).1
  rcases
      List.mem_append.mp hComparator with
    hInLeft | hInRejecting
  · exact hLeftPrimitive comparator hInLeft
  · exact
      domainRejectingComparators_satisfy_witness
        dom witness comparator hInRejecting

private theorem counterexampleSet_satisfies_prerelease_witness
    (leftSet : ComparatorSet)
    (dom : Range)
    (witness : Version)
    (hPrerelease : witness.prerelease.isEmpty = false)
    (hLeft : leftSet.satisfies witness = true) :
    (counterexampleComparatorSet
      leftSet dom witness).satisfies witness = true := by
  apply
    (ComparatorSet.satisfies_eq_true_iff
      (counterexampleComparatorSet leftSet dom witness)
      witness).mpr
  constructor
  · intro comparator hComparator
    have hLeftPrimitive :=
      ((ComparatorSet.satisfies_eq_true_iff
        leftSet witness).mp hLeft).1
    rcases
        List.mem_append.mp hComparator with
      hInLeft | hInRejecting
    · exact hLeftPrimitive comparator hInLeft
    · exact
        domainRejectingComparators_satisfy_witness
          dom witness comparator hInRejecting
  · rcases
        ComparatorSet.exists_prerelease_bound_same_core_of_satisfies
          leftSet witness hPrerelease hLeft with
      ⟨anchor,
        hAnchor,
        hAnchorPrerelease,
        hMajor,
        hMinor,
        hPatch⟩
    apply
      ComparatorSet.prereleaseAdmitted_of_anchor
        (counterexampleComparatorSet leftSet dom witness)
        witness
        hPrerelease
        anchor
    · simp [counterexampleComparatorSet, hAnchor]
    · exact hAnchorPrerelease
    · exact hMajor
    · exact hMinor
    · exact hPatch

private theorem comparatorSet_rejection_reason
    (set : ComparatorSet)
    (witness : Version)
    (hReject : set.satisfies witness = false) :
    (∃ source,
        source ∈ set.comparators ∧
        source.satisfies witness = false) ∨
      set.prereleaseAdmitted witness = false := by
  unfold ComparatorSet.satisfies at hReject
  cases hAll :
      set.comparators.all
        (fun comparator => comparator.satisfies witness) with
  | false =>
      exact
        Or.inl
          (exists_mem_false_of_listAll_eq_false
            set.comparators
            (fun comparator => comparator.satisfies witness)
            hAll)
  | true =>
      cases hAdmission : set.prereleaseAdmitted witness with
      | false =>
          exact Or.inr hAdmission
      | true =>
          simp [hAll, hAdmission] at hReject

private theorem exists_failed_comparator_of_stable_rejection
    (set : ComparatorSet)
    (witness : Version)
    (hStable : witness.prerelease.isEmpty = true)
    (hReject : set.satisfies witness = false) :
    ∃ source,
      source ∈ set.comparators ∧
      source.satisfies witness = false := by
  rcases
      comparatorSet_rejection_reason set witness hReject with
    hPrimitive | hAdmission
  · exact hPrimitive
  · have hAdmissionTrue :=
      ComparatorSet.prereleaseAdmitted_of_stable
        set witness hStable
    rw [hAdmission] at hAdmissionTrue
    contradiction

private theorem comparatorSet_rejects_of_failed_comparator
    (set : ComparatorSet)
    (candidate : Version)
    (source : Comparator)
    (hSource : source ∈ set.comparators)
    (hFalse : source.satisfies candidate = false) :
    set.satisfies candidate = false := by
  have hAllFalse :
      set.comparators.all
        (fun comparator => comparator.satisfies candidate) = false :=
    listAll_eq_false_of_mem_false
      set.comparators
      (fun comparator => comparator.satisfies candidate)
      source
      hSource
      hFalse
  simp [ComparatorSet.satisfies, hAllFalse]

private theorem prereleaseAdmission_false_of_same_core
    (set : ComparatorSet)
    (witness candidate : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hWitnessAdmission :
      set.prereleaseAdmitted witness = false)
    (hCandidatePrerelease :
      candidate.prerelease.isEmpty = false)
    (hMajor : candidate.major = witness.major)
    (hMinor : candidate.minor = witness.minor)
    (hPatch : candidate.patch = witness.patch) :
    set.prereleaseAdmitted candidate = false := by
  cases hCandidateAdmission :
      set.prereleaseAdmitted candidate with
  | false =>
      rfl
  | true =>
      rcases
          (ComparatorSet.prereleaseAdmitted_eq_true_iff_of_prerelease
            set candidate hCandidatePrerelease).mp
            hCandidateAdmission with
        ⟨anchor,
          hAnchor,
          hAnchorPrerelease,
          hAnchorMajor,
          hAnchorMinor,
          hAnchorPatch⟩
      have hWitnessAdmissionTrue :
          set.prereleaseAdmitted witness = true := by
        exact
          ComparatorSet.prereleaseAdmitted_of_anchor
            set witness hWitnessPrerelease
            anchor hAnchor hAnchorPrerelease
            (hAnchorMajor.trans hMajor)
            (hAnchorMinor.trans hMinor)
            (hAnchorPatch.trans hPatch)
      rw [hWitnessAdmission] at hWitnessAdmissionTrue
      contradiction

private theorem set_false_of_range_false
    (range : Range)
    (candidate : Version)
    (set : ComparatorSet)
    (hSet : set ∈ range.sets)
    (hRangeFalse : range.satisfies candidate = false) :
    set.satisfies candidate = false := by
  cases hSetValue : set.satisfies candidate with
  | false =>
      rfl
  | true =>
      have hAnyTrue :
          range.sets.any
            (fun item => item.satisfies candidate) = true :=
        listAny_eq_true_of_mem_true
          range.sets
          (fun item => item.satisfies candidate)
          set
          hSet
          hSetValue
      unfold Range.satisfies at hRangeFalse
      rw [hRangeFalse] at hAnyTrue
      contradiction

private theorem range_false_of_all_sets_false
    (range : Range)
    (candidate : Version)
    (h :
      ∀ set,
        set ∈ range.sets →
        set.satisfies candidate = false) :
    range.satisfies candidate = false := by
  unfold Range.satisfies
  exact
    listAny_eq_false_of_all_false
      range.sets
      (fun set => set.satisfies candidate)
      h

private theorem boundaryCandidate_mem_rangeBoundaryCandidates
    (range : Range)
    (set : ComparatorSet)
    (hSet : set ∈ range.sets)
    (source : Comparator)
    (hSource : source ∈ set.comparators)
    (candidate : Version)
    (hBoundary :
      candidate ∈ boundaryCandidates source) :
    candidate ∈ rangeBoundaryCandidates range := by
  simp only [rangeBoundaryCandidates, List.mem_flatMap]
  refine ⟨set, hSet, ?_⟩
  simp only [comparatorSetCandidates, List.mem_flatMap]
  exact ⟨source, hSource, hBoundary⟩

private theorem boundaryCandidate_of_domainRejecting_mem_range
    (dom : Range)
    (witness : Version)
    (rejecting : Comparator)
    (hRejecting :
      rejecting ∈ domainRejectingComparators dom witness)
    (candidate : Version)
    (hBoundary :
      candidate ∈ boundaryCandidates rejecting) :
    candidate ∈ rangeBoundaryCandidates dom := by
  rcases
      mem_domainRejectingComparators_source
        dom witness rejecting hRejecting with
    ⟨set,
      hSet,
      source,
      hSource,
      hFalse,
      hEq⟩
  subst rejecting
  have hBoundarySource :
      candidate ∈ boundaryCandidates source := by
    rw [
      ← boundaryCandidates_eq_of_bound_eq
        (rejectingComparator source witness)
        source
        (rejectingComparator_bound source witness)
    ]
    exact hBoundary
  exact
    boundaryCandidate_mem_rangeBoundaryCandidates
      dom set hSet source hSource candidate hBoundarySource

private theorem comparatorSetCandidate_of_counterexampleSet_mem_subsetPool
    (sub dom : Range)
    (leftSet : ComparatorSet)
    (hLeftSet : leftSet ∈ sub.sets)
    (witness candidate : Version)
    (hCandidate :
      candidate ∈
        comparatorSetCandidates
          (counterexampleComparatorSet leftSet dom witness)) :
    candidate ∈ subsetCounterexampleCandidates sub dom := by
  simp only [comparatorSetCandidates, List.mem_flatMap] at hCandidate
  rcases hCandidate with
    ⟨comparator, hComparator, hBoundary⟩
  rcases
      List.mem_append.mp hComparator with
    hInLeft | hInRejecting
  · have hInSub :=
      boundaryCandidate_mem_rangeBoundaryCandidates
        sub leftSet hLeftSet comparator hInLeft
        candidate hBoundary
    simp [
      subsetCounterexampleCandidates,
      intersectionCandidates,
      hInSub
    ]
  · have hInDom :=
      boundaryCandidate_of_domainRejecting_mem_range
        dom witness comparator hInRejecting
        candidate hBoundary
    simp [
      subsetCounterexampleCandidates,
      intersectionCandidates,
      hInDom
    ]

private theorem pairCandidate_of_counterexampleSet_mem_subsetPool
    (sub dom : Range)
    (leftSet : ComparatorSet)
    (hLeftSet : leftSet ∈ sub.sets)
    (witness candidate : Version)
    (hCandidate :
      candidate ∈
        comparatorSetIntersectionCandidates
          (counterexampleComparatorSet leftSet dom witness)
          (counterexampleComparatorSet leftSet dom witness)) :
    candidate ∈ subsetCounterexampleCandidates sub dom := by
  simp only [
    comparatorSetIntersectionCandidates,
    List.mem_cons,
    List.mem_append
  ] at hCandidate
  rcases hCandidate with
    hMinimum | hLeft | hRight
  · subst candidate
    simp [
      subsetCounterexampleCandidates,
      intersectionCandidates
    ]
  · exact
      comparatorSetCandidate_of_counterexampleSet_mem_subsetPool
        sub dom leftSet hLeftSet witness candidate hLeft
  · exact
      comparatorSetCandidate_of_counterexampleSet_mem_subsetPool
        sub dom leftSet hLeftSet witness candidate hRight

private theorem counterexampleSet_candidate_left_satisfies_stable
    (leftSet : ComparatorSet)
    (dom : Range)
    (witness candidate : Version)
    (hCandidateStable : candidate.prerelease.isEmpty = true)
    (hCombined :
      (counterexampleComparatorSet
        leftSet dom witness).satisfies candidate = true) :
    leftSet.satisfies candidate = true := by
  apply
    (ComparatorSet.satisfies_eq_true_iff_stable
      leftSet candidate hCandidateStable).mpr
  intro comparator hComparator
  have hPrimitive :=
    ((ComparatorSet.satisfies_eq_true_iff
      (counterexampleComparatorSet leftSet dom witness)
      candidate).mp hCombined).1
  exact
    hPrimitive comparator
      (by
        simp [counterexampleComparatorSet, hComparator])

private theorem counterexampleSet_candidate_left_satisfies_prerelease
    (leftSet : ComparatorSet)
    (dom : Range)
    (witness candidate : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hLeftWitness : leftSet.satisfies witness = true)
    (hCandidatePrerelease : candidate.prerelease.isEmpty = false)
    (hMajor : candidate.major = witness.major)
    (hMinor : candidate.minor = witness.minor)
    (hPatch : candidate.patch = witness.patch)
    (hCombined :
      (counterexampleComparatorSet
        leftSet dom witness).satisfies candidate = true) :
    leftSet.satisfies candidate = true := by
  apply
    (ComparatorSet.satisfies_eq_true_iff
      leftSet candidate).mpr
  constructor
  · intro comparator hComparator
    have hPrimitive :=
      ((ComparatorSet.satisfies_eq_true_iff
        (counterexampleComparatorSet leftSet dom witness)
        candidate).mp hCombined).1
    exact
      hPrimitive comparator
        (by
          simp [counterexampleComparatorSet, hComparator])
  · exact
      ComparatorSet.prereleaseAdmitted_of_same_core_as_satisfied
        leftSet witness candidate
        hWitnessPrerelease hLeftWitness hCandidatePrerelease
        hMajor hMinor hPatch

private theorem rightSet_rejects_stable_candidate
    (dom : Range)
    (witness candidate : Version)
    (rightSet : ComparatorSet)
    (hRightSet : rightSet ∈ dom.sets)
    (hWitnessStable : witness.prerelease.isEmpty = true)
    (hDomWitness : dom.satisfies witness = false)
    (hCombined :
      ∀ comparator ∈
          (counterexampleComparatorSet
            rightSet dom witness).comparators,
        comparator.satisfies candidate = true) :
    rightSet.satisfies candidate = false := by
  have hRightWitness :=
    set_false_of_range_false
      dom witness rightSet hRightSet hDomWitness
  rcases
      exists_failed_comparator_of_stable_rejection
        rightSet witness hWitnessStable hRightWitness with
    ⟨source, hSource, hSourceFalse⟩
  have hRejectingMem :
      rejectingComparator source witness ∈
        domainRejectingComparators dom witness :=
    rejectingComparator_mem_domain
      dom witness rightSet hRightSet
      source hSource hSourceFalse
  have hRejectingCombined :
      rejectingComparator source witness ∈
        (counterexampleComparatorSet
          rightSet dom witness).comparators := by
    simp [
      counterexampleComparatorSet,
      hRejectingMem
    ]
  have hRejectingCandidate :=
    hCombined
      (rejectingComparator source witness)
      hRejectingCombined
  have hSourceCandidateFalse :=
    source_false_of_rejectingComparator_satisfies
      source witness candidate
      hSourceFalse hRejectingCandidate
  exact
    comparatorSet_rejects_of_failed_comparator
      rightSet candidate source hSource hSourceCandidateFalse

private theorem rightSet_rejects_prerelease_candidate
    (dom : Range)
    (leftSet : ComparatorSet)
    (witness candidate : Version)
    (rightSet : ComparatorSet)
    (hRightSet : rightSet ∈ dom.sets)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hDomWitness : dom.satisfies witness = false)
    (hCandidatePrerelease : candidate.prerelease.isEmpty = false)
    (hMajor : candidate.major = witness.major)
    (hMinor : candidate.minor = witness.minor)
    (hPatch : candidate.patch = witness.patch)
    (hCombined :
      (counterexampleComparatorSet
        leftSet dom witness).satisfies candidate = true) :
    rightSet.satisfies candidate = false := by
  have hRightWitness :=
    set_false_of_range_false
      dom witness rightSet hRightSet hDomWitness
  rcases
      comparatorSet_rejection_reason
        rightSet witness hRightWitness with
    hPrimitive | hAdmission
  · rcases hPrimitive with
      ⟨source, hSource, hSourceFalse⟩
    have hRejectingMem :
        rejectingComparator source witness ∈
          domainRejectingComparators dom witness :=
      rejectingComparator_mem_domain
        dom witness rightSet hRightSet
        source hSource hSourceFalse
    have hCombinedPrimitive :=
      ((ComparatorSet.satisfies_eq_true_iff
        (counterexampleComparatorSet leftSet dom witness)
        candidate).mp hCombined).1
    have hRejectingCandidate :=
      hCombinedPrimitive
        (rejectingComparator source witness)
        (by
          simp [
            counterexampleComparatorSet,
            hRejectingMem
          ])
    have hSourceCandidateFalse :=
      source_false_of_rejectingComparator_satisfies
        source witness candidate
        hSourceFalse hRejectingCandidate
    exact
      comparatorSet_rejects_of_failed_comparator
        rightSet candidate source hSource hSourceCandidateFalse
  · have hCandidateAdmission :
        rightSet.prereleaseAdmitted candidate = false :=
      prereleaseAdmission_false_of_same_core
        rightSet witness candidate
        hWitnessPrerelease hAdmission
        hCandidatePrerelease hMajor hMinor hPatch
    simp [
      ComparatorSet.satisfies,
      hCandidateAdmission
    ]

private theorem stable_subset_counterexample_candidate
    (sub dom : Range)
    (witness : Version)
    (hWitnessStable : witness.prerelease.isEmpty = true)
    (hSubWitness : Contains sub witness)
    (hDomWitness : ¬ Contains dom witness) :
    ∃ candidate,
      candidate ∈ subsetCounterexampleCandidates sub dom ∧
      subsetCounterexampleAt sub dom candidate = true := by
  unfold Contains at hSubWitness hDomWitness
  have hDomFalse : dom.satisfies witness = false := by
    cases hValue : dom.satisfies witness with
    | false =>
        rfl
    | true =>
        exact (hDomWitness hValue).elim
  rcases
      (Range.satisfies_eq_true_iff
        sub witness).mp hSubWitness with
    ⟨leftSet, hLeftSet, hLeftWitness⟩
  let combined :=
    counterexampleComparatorSet leftSet dom witness
  have hCombinedWitness :
      combined.satisfies witness = true := by
    simpa [combined] using
      counterexampleSet_satisfies_stable_witness
        leftSet dom witness
        hWitnessStable hLeftWitness
  rcases
      comparatorSetPairStableWitnessCandidate
        combined combined witness
        hWitnessStable
        hCombinedWitness
        hCombinedWitness with
    ⟨candidate,
      hCandidate,
      hCandidateStable,
      hCombinedCandidate,
      hCombinedCandidateAgain⟩
  have hCandidatePool :
      candidate ∈ subsetCounterexampleCandidates sub dom := by
    simpa [combined] using
      pairCandidate_of_counterexampleSet_mem_subsetPool
        sub dom leftSet hLeftSet witness
        candidate hCandidate
  have hLeftCandidate :
      leftSet.satisfies candidate = true := by
    simpa [combined] using
      counterexampleSet_candidate_left_satisfies_stable
        leftSet dom witness candidate
        hCandidateStable hCombinedCandidate
  have hSubCandidate :
      sub.satisfies candidate = true :=
    (Range.satisfies_eq_true_iff sub candidate).mpr
      ⟨leftSet, hLeftSet, hLeftCandidate⟩
  have hCombinedPrimitive :=
    ((ComparatorSet.satisfies_eq_true_iff
      combined candidate).mp hCombinedCandidate).1
  have hDomCandidate :
      dom.satisfies candidate = false := by
    apply range_false_of_all_sets_false
    intro rightSet hRightSet
    have hRightCombined :
        ∀ comparator ∈
            (counterexampleComparatorSet
              rightSet dom witness).comparators,
          comparator.satisfies candidate = true := by
      intro comparator hComparator
      rcases
          List.mem_append.mp hComparator with
        hInRight | hInRejecting
      · have hRightWitness :=
          set_false_of_range_false
            dom witness rightSet hRightSet hDomFalse
        rcases
            exists_failed_comparator_of_stable_rejection
              rightSet witness
              hWitnessStable hRightWitness with
          ⟨source, hSource, hSourceFalse⟩
        -- A right-set primitive need not belong to the synthetic conjunction
        -- unless it was failed by the witness. This branch is never needed by
        -- the rejection proof below.
        cases hSourceValue : comparator.satisfies candidate with
        | true => exact hSourceValue
        | false =>
            exact False.elim (by
              have := hSourceFalse
              contradiction)
      · exact
          hCombinedPrimitive comparator
            (by
              simp [
                combined,
                counterexampleComparatorSet,
                hInRejecting
              ])
    have hRightWitness :=
      set_false_of_range_false
        dom witness rightSet hRightSet hDomFalse
    rcases
        exists_failed_comparator_of_stable_rejection
          rightSet witness hWitnessStable hRightWitness with
      ⟨source, hSource, hSourceFalse⟩
    have hRejectingMem :
        rejectingComparator source witness ∈
          domainRejectingComparators dom witness :=
      rejectingComparator_mem_domain
        dom witness rightSet hRightSet
        source hSource hSourceFalse
    have hRejectingCandidate :=
      hCombinedPrimitive
        (rejectingComparator source witness)
        (by
          simp [
            combined,
            counterexampleComparatorSet,
            hRejectingMem
          ])
    have hSourceCandidateFalse :=
      source_false_of_rejectingComparator_satisfies
        source witness candidate
        hSourceFalse hRejectingCandidate
    exact
      comparatorSet_rejects_of_failed_comparator
        rightSet candidate source hSource hSourceCandidateFalse
  refine
    ⟨candidate,
      hCandidatePool,
      ?_⟩
  simp [
    subsetCounterexampleAt,
    hSubCandidate,
    hDomCandidate
  ]

private theorem prerelease_subset_counterexample_candidate
    (sub dom : Range)
    (witness : Version)
    (hWitnessPrerelease : witness.prerelease.isEmpty = false)
    (hSubWitness : Contains sub witness)
    (hDomWitness : ¬ Contains dom witness) :
    ∃ candidate,
      candidate ∈ subsetCounterexampleCandidates sub dom ∧
      subsetCounterexampleAt sub dom candidate = true := by
  unfold Contains at hSubWitness hDomWitness
  have hDomFalse : dom.satisfies witness = false := by
    cases hValue : dom.satisfies witness with
    | false =>
        rfl
    | true =>
        exact (hDomWitness hValue).elim
  rcases
      (Range.satisfies_eq_true_iff
        sub witness).mp hSubWitness with
    ⟨leftSet, hLeftSet, hLeftWitness⟩
  let combined :=
    counterexampleComparatorSet leftSet dom witness
  have hCombinedWitness :
      combined.satisfies witness = true := by
    simpa [combined] using
      counterexampleSet_satisfies_prerelease_witness
        leftSet dom witness
        hWitnessPrerelease hLeftWitness
  rcases
      comparatorSetPairPrereleaseWitnessCandidate
        combined combined witness
        hWitnessPrerelease
        hCombinedWitness
        hCombinedWitness with
    ⟨candidate,
      hCandidate,
      hCandidatePrerelease,
      hMajor,
      hMinor,
      hPatch,
      hCombinedCandidate,
      hCombinedCandidateAgain⟩
  have hCandidatePool :
      candidate ∈ subsetCounterexampleCandidates sub dom := by
    simpa [combined] using
      pairCandidate_of_counterexampleSet_mem_subsetPool
        sub dom leftSet hLeftSet witness
        candidate hCandidate
  have hLeftCandidate :
      leftSet.satisfies candidate = true := by
    simpa [combined] using
      counterexampleSet_candidate_left_satisfies_prerelease
        leftSet dom witness candidate
        hWitnessPrerelease hLeftWitness
        hCandidatePrerelease
        hMajor hMinor hPatch
        hCombinedCandidate
  have hSubCandidate :
      sub.satisfies candidate = true :=
    (Range.satisfies_eq_true_iff sub candidate).mpr
      ⟨leftSet, hLeftSet, hLeftCandidate⟩
  have hDomCandidate :
      dom.satisfies candidate = false := by
    apply range_false_of_all_sets_false
    intro rightSet hRightSet
    exact
      rightSet_rejects_prerelease_candidate
        dom leftSet witness candidate
        rightSet hRightSet
        hWitnessPrerelease hDomFalse
        hCandidatePrerelease
        hMajor hMinor hPatch
        hCombinedCandidate
  refine
    ⟨candidate,
      hCandidatePool,
      ?_⟩
  simp [
    subsetCounterexampleAt,
    hSubCandidate,
    hDomCandidate
  ]

/--
The existing critical-boundary pool is complete for semantic subset failures.

The proof splits stable and prerelease witnesses. It reuses the strengthened
intersection boundary lemmas, adding exact primitive rejection constraints with
the same bounds. Since those synthetic comparators contribute no new boundary
versions, the resulting counterexample is already in the original shared pool.
-/
theorem subsetCounterexampleCandidatesComplete
    (sub dom : Range) :
    SubsetCounterexampleCandidatesComplete sub dom := by
  intro hCounterexample
  rcases hCounterexample with
    ⟨witness, hSubWitness, hDomWitness⟩
  cases hPrerelease :
      witness.prerelease.isEmpty with
  | true =>
      exact
        stable_subset_counterexample_candidate
          sub dom witness
          hPrerelease
          hSubWitness hDomWitness
  | false =>
      exact
        prerelease_subset_counterexample_candidate
          sub dom witness
          hPrerelease
          hSubWitness hDomWitness

private theorem firstSubsetCounterexample?_exists_some_of_mem
    (sub dom : Range)
    (candidates : List Version)
    (h :
      ∃ candidate,
        candidate ∈ candidates ∧
        subsetCounterexampleAt sub dom candidate = true) :
    ∃ candidate,
      firstSubsetCounterexample? sub dom candidates = some candidate := by
  induction candidates with
  | nil =>
      simp at h
  | cons head tail ih =>
      cases hHead : subsetCounterexampleAt sub dom head with
      | false =>
          have hTail :
              ∃ candidate,
                candidate ∈ tail ∧
                subsetCounterexampleAt sub dom candidate = true := by
            rcases h with ⟨candidate, hMem, hCounterexample⟩
            rcases List.mem_cons.mp hMem with hEq | hMemTail
            · subst candidate
              simp [hHead] at hCounterexample
            · exact ⟨candidate, hMemTail, hCounterexample⟩
          rcases ih hTail with ⟨candidate, hFound⟩
          exact
            ⟨candidate,
              by
                simp [
                  firstSubsetCounterexample?,
                  hHead,
                  hFound
                ]⟩
      | true =>
          exact
            ⟨head,
              by
                simp [firstSubsetCounterexample?, hHead]⟩

private theorem firstSubsetCounterexample?_sound
    (sub dom : Range)
    (candidates : List Version)
    (candidate : Version)
    (h :
      firstSubsetCounterexample? sub dom candidates =
        some candidate) :
    subsetCounterexampleAt sub dom candidate = true := by
  induction candidates with
  | nil =>
      simp [firstSubsetCounterexample?] at h
  | cons head tail ih =>
      by_cases hCounterexample :
          subsetCounterexampleAt sub dom head = true
      · simp [
          firstSubsetCounterexample?,
          hCounterexample
        ] at h
        subst candidate
        exact hCounterexample
      · have hFalse :
          subsetCounterexampleAt sub dom head = false := by
          cases hValue :
              subsetCounterexampleAt sub dom head <;>
            simp_all
        simp [
          firstSubsetCounterexample?,
          hFalse
        ] at h
        exact ih h

/-- Any returned witness really is accepted by `sub` and rejected by `dom`. -/
theorem findSubsetCounterexample?_counterexample
    (sub dom : Range)
    (candidate : Version)
    (h :
      findSubsetCounterexample? sub dom = some candidate) :
    Contains sub candidate ∧ ¬ Contains dom candidate := by
  have hCounterexample :
      subsetCounterexampleAt sub dom candidate = true :=
    firstSubsetCounterexample?_sound
      sub
      dom
      (subsetCounterexampleCandidates sub dom)
      candidate
      h
  exact
    (subsetCounterexampleAt_eq_true_iff
      sub dom candidate).mp hCounterexample

/-- Any returned witness proves that semantic subset does not hold. -/
theorem findSubsetCounterexample?_sound
    (sub dom : Range)
    (candidate : Version)
    (h :
      findSubsetCounterexample? sub dom = some candidate) :
    ¬ SubsetOf sub dom := by
  have hCounterexample :=
    findSubsetCounterexample?_counterexample
      sub dom candidate h
  intro hSubset
  exact
    hCounterexample.2
      (hSubset candidate hCounterexample.1)

/-- Every semantic counterexample produces a returned concrete witness. -/
theorem findSubsetCounterexample?_complete_verified
    (sub dom : Range)
    (hCounterexample : HasSubsetCounterexample sub dom) :
    ∃ candidate,
      findSubsetCounterexample? sub dom = some candidate := by
  have hCandidate :=
    subsetCounterexampleCandidatesComplete
      sub dom hCounterexample
  simpa [findSubsetCounterexample?] using
    firstSubsetCounterexample?_exists_some_of_mem
      sub
      dom
      (subsetCounterexampleCandidates sub dom)
      hCandidate

/--
Returning `none` from the verified finite search is exactly semantic subset.
-/
theorem findSubsetCounterexample?_none_iff_subset_verified
    (sub dom : Range) :
    findSubsetCounterexample? sub dom = none ↔
      SubsetOf sub dom := by
  constructor
  · intro hNone
    intro candidate hSub
    cases hDom : dom.satisfies candidate with
    | true =>
        exact hDom
    | false =>
        have hNotDom : ¬ Contains dom candidate := by
          unfold Contains
          simp [hDom]
        have hCounterexample :
            HasSubsetCounterexample sub dom :=
          ⟨candidate, hSub, hNotDom⟩
        rcases
            findSubsetCounterexample?_complete_verified
              sub dom hCounterexample with
          ⟨found, hSome⟩
        rw [hNone] at hSome
        contradiction
  · intro hSubset
    cases hSearch :
        findSubsetCounterexample? sub dom with
    | none =>
        rfl
    | some candidate =>
        have hNotSubset :=
          findSubsetCounterexample?_sound
            sub dom candidate hSearch
        exact (hNotSubset hSubset).elim

/-- Executable semantic subset decision backed by counterexample search. -/
def isSubsetOf (sub dom : Range) : Bool :=
  (findSubsetCounterexample? sub dom).isNone

/-- The executable subset decision agrees exactly with extensional subset. -/
theorem isSubsetOf_eq_true_iff
    (sub dom : Range) :
    isSubsetOf sub dom = true ↔
      SubsetOf sub dom := by
  simp [
    isSubsetOf,
    findSubsetCounterexample?_none_iff_subset_verified
  ]

end Range

end Semverifier
