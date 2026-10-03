import Mathlib
import Submission.Work.PlanarSC.BO.Defs
import Submission.Work.PlanarSC.BO.Geometry

open Set

namespace Work.PlanarSC.BO

open Work.HornSC.CellBoundaryJordan.BO

/-- Put this in `Submission/Work/PlanarSC/BO/graph_connected.lean`, with imports `Mathlib`,
`Submission.Work.PlanarSC.BO.Defs` and `Submission.Work.PlanarSC.BO.Geometry`, inside
`namespace Work.HornSC.CellBoundaryJordan.BO`.

If the union of the unit segments of a finite family `A` of unit steps is preconnected then the
graph on `stepVerts A` with adjacency `StepAdj A` is connected.  Route (copy the sorry-free
`Work.PlanarSC.runGraph_connected`, which does exactly this for the run graph of a polyomino):
assume `a₀` cannot reach `a₁`; let `A_set ⊆ ↥(stepVerts A)` be the reachable set, split `A` into
`A.filter (fun e => e.1 ∈ A_set)` and its complement, and observe that the two corresponding unions
of `stepSeg`'s are closed (`isClosed_biUnion_stepSeg`), nonempty, cover `⋃ e ∈ A, stepSeg e`, and are
disjoint: a common point of two distinct unit segments is a common endpoint
(`unitStep_seg_inter_subset` from `Geometry`), which puts the two first endpoints into the same
class.  `isPreconnected_iff_subset_of_disjoint_closed` gives the contradiction.  `A = ∅` is fine:
then `↥(stepVerts A)` is empty and the statement is vacuous. -/
theorem graph_connected (A : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
    (hunit : ∀ e ∈ A, Work.HornSC.CellBoundaryJordan.IsUnitStep e)
    (hconn : IsPreconnected (⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e)) :
    ∀ a b : ↥(Work.HornSC.CellBoundaryJordan.BO.stepVerts A),
      Relation.ReflTransGen (fun x y : ↥(Work.HornSC.CellBoundaryJordan.BO.stepVerts A) =>
        Work.HornSC.CellBoundaryJordan.BO.StepAdj A (x : ℤ × ℤ) (y : ℤ × ℤ)) a b := by
  classical
  -- Suppose the graph is disconnected: some `a₀` is unreachable from `a₁`.
  by_contra h
  push_neg at h
  obtain ⟨a₀, a₁, ha₁⟩ := h
  set adj : ↥(stepVerts A) → ↥(stepVerts A) → Prop :=
    fun x y => StepAdj A (x : ℤ × ℤ) (y : ℤ × ℤ) with hadj
  -- The set of reachable vertices, as lattice points.
  set R : Set (ℤ × ℤ) := {v | ∃ hv : v ∈ stepVerts A,
      Relation.ReflTransGen adj a₀ (⟨v, hv⟩ : ↥(stepVerts A))} with hR
  have hcongr : ∀ {v : ℤ × ℤ} (h₁ h₂ : v ∈ stepVerts A),
      Relation.ReflTransGen adj a₀ (⟨v, h₁⟩ : ↥(stepVerts A)) ↔
        Relation.ReflTransGen adj a₀ (⟨v, h₂⟩ : ↥(stepVerts A)) := by
    intro v h₁ h₂
    rw [show (⟨v, h₁⟩ : ↥(stepVerts A)) = ⟨v, h₂⟩ from Subtype.ext rfl]
  have hRmem : ∀ {v : ℤ × ℤ} (hv : v ∈ stepVerts A),
      v ∈ R ↔ Relation.ReflTransGen adj a₀ (⟨v, hv⟩ : ↥(stepVerts A)) := by
    intro v hv
    rw [hR]
    constructor
    · rintro ⟨h', hrt⟩
      exact (hcongr h' hv).mp hrt
    · intro hrt
      exact ⟨hv, hrt⟩
  -- A step of `A` has both endpoints on the same side.
  have hstep : ∀ e ∈ A, (e.1 ∈ R ↔ e.2 ∈ R) := by
    intro e he
    have h₁ : e.1 ∈ stepVerts A := stepVerts_mem_fst he
    have h₂ : e.2 ∈ stepVerts A := stepVerts_mem_snd he
    have hadje : adj ⟨e.1, h₁⟩ ⟨e.2, h₂⟩ := by
      rw [hadj]
      exact stepAdj_of_mem he
    constructor
    · intro hx
      exact (hRmem h₂).mpr (Relation.ReflTransGen.tail ((hRmem h₁).mp hx) hadje)
    · intro hy
      refine (hRmem h₁).mpr ?_
      exact Relation.ReflTransGen.tail ((hRmem h₂).mp hy) (by
        rw [hadj]
        exact stepAdj_symm (stepAdj_of_mem he))
  have ha₀R : a₀.1 ∈ R := by
    refine (hRmem a₀.2).mpr ?_
    show Relation.ReflTransGen adj a₀ a₀
    exact Relation.ReflTransGen.refl
  have ha₁R : a₁.1 ∉ R := by
    intro hcon
    exact ha₁ ((hRmem a₁.2).mp hcon)
  -- Split `A` into the steps whose first endpoint is reachable and the rest.
  set A₁ : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := A.filter (fun e => e.1 ∈ R) with hA₁
  set A₂ : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := A.filter (fun e => ¬ e.1 ∈ R) with hA₂
  have hA₁ne : A₁.Nonempty := by
    obtain ⟨e, he, hcase⟩ := mem_stepVerts.mp a₀.2
    refine ⟨e, ?_⟩
    rw [hA₁, Finset.mem_filter]
    refine ⟨he, ?_⟩
    rcases hcase with hc | hc
    · rw [← hc]; exact ha₀R
    · exact (hstep e he).mpr (by rw [← hc]; exact ha₀R)
  have hA₂ne : A₂.Nonempty := by
    obtain ⟨e, he, hcase⟩ := mem_stepVerts.mp a₁.2
    refine ⟨e, ?_⟩
    rw [hA₂, Finset.mem_filter]
    refine ⟨he, ?_⟩
    rcases hcase with hc | hc
    · intro hcon
      rw [← hc] at hcon
      exact ha₁R hcon
    · intro hcon
      have hcon2 : e.2 ∈ R := (hstep e he).mp hcon
      rw [← hc] at hcon2
      exact ha₁R hcon2
  -- The two unions of segments.
  set UA : Set ℂ := ⋃ e ∈ A₁, Work.HornSC.CellBoundaryJordan.stepSeg e with hUA
  set UB : Set ℂ := ⋃ e ∈ A₂, Work.HornSC.CellBoundaryJordan.stepSeg e with hUB
  have hUAcl : IsClosed UA := by
    rw [hUA]
    exact isClosed_biUnion_stepSeg A₁
  have hUBcl : IsClosed UB := by
    rw [hUB]
    exact isClosed_biUnion_stepSeg A₂
  have hcover : (⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) ⊆ UA ∪ UB := by
    intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨e, hz⟩ := hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨he, hze⟩ := hz
    by_cases heR : e.1 ∈ R
    · left
      rw [hUA]
      exact Set.mem_iUnion₂.mpr ⟨e, by rw [hA₁, Finset.mem_filter]; exact ⟨he, heR⟩, hze⟩
    · right
      rw [hUB]
      exact Set.mem_iUnion₂.mpr ⟨e, by rw [hA₂, Finset.mem_filter]; exact ⟨he, heR⟩, hze⟩
  have hneUA : ((⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) ∩ UA).Nonempty := by
    obtain ⟨e, heA₁⟩ := hA₁ne
    rw [hA₁, Finset.mem_filter] at heA₁
    obtain ⟨he, heR⟩ := heA₁
    obtain ⟨z, hz⟩ := stepSeg_nonempty e
    refine ⟨z, Set.mem_iUnion₂.mpr ⟨e, he, hz⟩, ?_⟩
    rw [hUA]
    exact Set.mem_iUnion₂.mpr ⟨e, by rw [hA₁, Finset.mem_filter]; exact ⟨he, heR⟩, hz⟩
  have hneUB : ((⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) ∩ UB).Nonempty := by
    obtain ⟨e, heA₂⟩ := hA₂ne
    rw [hA₂, Finset.mem_filter] at heA₂
    obtain ⟨he, heR⟩ := heA₂
    obtain ⟨z, hz⟩ := stepSeg_nonempty e
    refine ⟨z, Set.mem_iUnion₂.mpr ⟨e, he, hz⟩, ?_⟩
    rw [hUB]
    exact Set.mem_iUnion₂.mpr ⟨e, by rw [hA₂, Finset.mem_filter]; exact ⟨he, heR⟩, hz⟩
  -- The two pieces are disjoint: a common point is a common endpoint.
  have hdisj : UA ∩ UB = ∅ := by
    rw [← Set.subset_empty_iff]
    rintro z ⟨hzA, hzB⟩
    rw [hUA, Set.mem_iUnion₂] at hzA
    rw [hUB, Set.mem_iUnion₂] at hzB
    obtain ⟨e, heA₁, hze⟩ := hzA
    obtain ⟨e', heA₂, hze'⟩ := hzB
    rw [hA₁, Finset.mem_filter] at heA₁
    rw [hA₂, Finset.mem_filter] at heA₂
    obtain ⟨he, heR⟩ := heA₁
    obtain ⟨he', heR'⟩ := heA₂
    have hne : e ≠ e' := by
      rintro rfl
      exact heR' heR
    have hz' : z ∈ Work.HornSC.CellBoundaryJordan.stepSeg e ∩
        Work.HornSC.CellBoundaryJordan.stepSeg e' := ⟨hze, hze'⟩
    have hsub := unitStep_seg_inter_subset (hunit e he) (hunit e' he') hne hz'
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hsub
    obtain ⟨hz1, hz2⟩ := hsub
    -- A common endpoint `q` of the two segments lies in `R` (via `e`) and outside `R` (via `e'`).
    have hq : ∃ q : ℤ × ℤ, (q = e.1 ∨ q = e.2) ∧ (q = e'.1 ∨ q = e'.2) := by
      rcases hz1 with h1 | h1
      · refine ⟨e.1, Or.inl rfl, ?_⟩
        rcases hz2 with h2 | h2
        · exact Or.inl (Work.HornSC.CellBoundaryJordan.lpt_injective (h1.symm.trans h2))
        · exact Or.inr (Work.HornSC.CellBoundaryJordan.lpt_injective (h1.symm.trans h2))
      · refine ⟨e.2, Or.inr rfl, ?_⟩
        rcases hz2 with h2 | h2
        · exact Or.inl (Work.HornSC.CellBoundaryJordan.lpt_injective (h1.symm.trans h2))
        · exact Or.inr (Work.HornSC.CellBoundaryJordan.lpt_injective (h1.symm.trans h2))
    obtain ⟨q, hq1, hq2⟩ := hq
    have hqR : q ∈ R := by
      rcases hq1 with hq1 | hq1
      · rw [hq1]; exact heR
      · rw [hq1]; exact (hstep e he).mp heR
    rcases hq2 with hq2 | hq2
    · rw [hq2] at hqR
      exact heR' hqR
    · rw [hq2] at hqR
      exact heR' ((hstep e' he').mpr hqR)
  -- Preconnectedness forbids this separation.
  have hsep : (⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) ⊆ UA ∨
      (⋃ e ∈ A, Work.HornSC.CellBoundaryJordan.stepSeg e) ⊆ UB :=
    (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) UA UB hUAcl hUBcl hcover
      (by rw [hdisj, Set.inter_empty])
  rcases hsep with hsub | hsub
  · obtain ⟨z, hzs, hzB⟩ := hneUB
    have hzA : z ∈ UA := hsub hzs
    have hmem : z ∈ UA ∩ UB := ⟨hzA, hzB⟩
    rw [hdisj] at hmem
    exact hmem
  · obtain ⟨z, hzs, hzA⟩ := hneUA
    have hzB : z ∈ UB := hsub hzs
    have hmem : z ∈ UA ∩ UB := ⟨hzA, hzB⟩
    rw [hdisj] at hmem
    exact hmem

end Work.PlanarSC.BO
