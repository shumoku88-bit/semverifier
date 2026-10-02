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

/--
Finite boundary pool currently explored for subset counterexamples.

This deliberately reuses the already-audited intersection boundary pool. The
search below is proved sound unconditionally. Completeness is kept as a
separate explicit obligation until it is proved for subset counterexamples.
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

/--
Search the finite boundary pool for a concrete witness that `sub` is not a
subset of `dom`.

A returned witness is always sound. Returning `none` is not yet exposed as a
subset decision until candidate-pool completeness is proved.
-/
def findSubsetCounterexample?
    (sub dom : Range) : Option Version :=
  firstSubsetCounterexample?
    sub dom
    (subsetCounterexampleCandidates sub dom)

/--
Completeness obligation for the finite subset-counterexample candidate pool.

Keeping this proposition explicit prevents the executable search from silently
being promoted to a decision procedure before the infinite semantic claim is
proved.
-/
def SubsetCounterexampleCandidatesComplete
    (sub dom : Range) : Prop :=
  ¬ SubsetOf sub dom →
    ∃ candidate,
      candidate ∈ subsetCounterexampleCandidates sub dom ∧
      subsetCounterexampleAt sub dom candidate = true

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

/--
If the finite candidate pool is complete, every semantic subset failure
produces a returned concrete counterexample.
-/
theorem findSubsetCounterexample?_complete
    (sub dom : Range)
    (hCandidates :
      SubsetCounterexampleCandidatesComplete sub dom)
    (hNotSubset : ¬ SubsetOf sub dom) :
    ∃ candidate,
      findSubsetCounterexample? sub dom = some candidate := by
  have hCandidate := hCandidates hNotSubset
  simpa [findSubsetCounterexample?] using
    firstSubsetCounterexample?_exists_some_of_mem
      sub
      dom
      (subsetCounterexampleCandidates sub dom)
      hCandidate

/--
Under the explicit completeness obligation, returning `none` is exactly
semantic subset.
-/
theorem findSubsetCounterexample?_none_iff_subset
    (sub dom : Range)
    (hCandidates :
      SubsetCounterexampleCandidatesComplete sub dom) :
    findSubsetCounterexample? sub dom = none ↔
      SubsetOf sub dom := by
  constructor
  · intro hNone
    intro candidate hSub
    by_contra hDom
    have hNotSubset : ¬ SubsetOf sub dom := by
      intro hSubset
      exact hDom (hSubset candidate hSub)
    rcases
        findSubsetCounterexample?_complete
          sub dom hCandidates hNotSubset with
      ⟨found, hSome⟩
    rw [hNone] at hSome
    contradiction
  · intro hSubset
    cases hSearch : findSubsetCounterexample? sub dom with
    | none =>
        rfl
    | some candidate =>
        have hNotSubset :=
          findSubsetCounterexample?_sound
            sub dom candidate hSearch
        exact (hNotSubset hSubset).elim

end Range

end Semverifier
