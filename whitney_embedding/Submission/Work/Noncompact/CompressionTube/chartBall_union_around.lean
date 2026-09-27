import Mathlib
import Submission.Work.Noncompact.CompressionTube.chartBall_union_between

/-!
# A compact chart-ball union *around* a compact set, inside an open set and avoiding a locally
finite set

`chartBall_union_between` (`chartBall_union_between.lean`) produces a compact finite union `S` of
chart balls with `A ⊆ S ⊆ interior N` avoiding the locally finite set `B`.  The interleaving of the
flat exhaustion needs the logically stronger statement with `A ⊆ interior S` — which the proof of
`chartBall_union_between` already provides, because the finite subcover it extracts consists of the
*interiors* of the chart balls.  This file records that strengthening (reusing the auxiliary lemmas
of `chartBall_union_between.lean`).
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Noncompact.CompressionTube

open Set Topology Metric

theorem chartBall_union_around {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    {A N : Set M} (hA : IsCompact A) (hAN : A ⊆ interior N)
    {B : Set M} (hAfinB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (hAB : ∀ b : M, b ∈ B → b ∈ interior N → b ∉ A) :
    ∃ S : Set M, IsCompact S ∧ A ⊆ interior S ∧ S ⊆ interior N ∧
      Work.Noncompact.CompressionTube.IsChartBallUnion n M S ∧
      ∀ b : M, b ∈ B → b ∈ interior N → b ∉ S := by
  classical
  -- a chart ball around every point of `A`, inside `interior N` and avoiding `B`
  have hpt : ∀ a : {a : M // a ∈ A}, ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      closedBall c r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a.1).target ∧
      a.1 ∈ interior (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r) ∧
      homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r ⊆ interior N ∧
      Disjoint (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r) B := by
    intro a
    refine exists_chartBall_interior_avoiding_B hAfinB (hAN a.2) ?_
    intro hb
    exact hAB a.1 hb (hAN a.2) a.2
  choose c r hc using hpt
  let F : {a : M // a ∈ A} → Set M := fun a => chartBall a.1 (c a) (r a)
  let U : {a : M // a ∈ A} → Set M := fun a => interior (F a)
  have hUo : ∀ a, IsOpen (U a) := fun a => isOpen_interior
  have hcover : A ⊆ ⋃ a, U a := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hc ⟨x, hx⟩).2.1⟩
  -- finitely many of the open chart balls cover `A`
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hUo hcover
  have hFc : ∀ a, IsCompact (F a) := fun a => isCompact_homeoBall (hc a).1
  have hFN : ∀ a, F a ⊆ interior N := fun a => (hc a).2.2.1
  have hFB : ∀ a, Disjoint (F a) B := fun a => (hc a).2.2.2
  refine ⟨⋃ a ∈ (t : Set {a : M // a ∈ A}), F a, ?_, ?_, ?_, ?_, ?_⟩
  · -- compact
    exact t.finite_toSet.isCompact_biUnion (fun a _ => hFc a)
  · -- `A ⊆ interior S`
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion, exists_prop] at hxt
    obtain ⟨a, hat, hxa⟩ := hxt
    exact interior_mono (fun y hy => Set.mem_iUnion.mpr
      ⟨a, Set.mem_iUnion.mpr ⟨Finset.mem_coe.mpr hat, hy⟩⟩) hxa
  · -- `S ⊆ interior N`
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨a, -, hxa⟩ := hx
    exact hFN a hxa
  · -- `S` is a finite union of chart balls
    let I := {a : {a : M // a ∈ A} // a ∈ t}
    haveI : Fintype I := inferInstance
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    refine ⟨Fin (Fintype.card I), inferInstance, fun i => (e.symm i).1.1,
      fun i => c (e.symm i).1, fun i => r (e.symm i).1, ?_, ?_⟩
    · intro i
      exact (hc (e.symm i).1).1
    · apply le_antisymm
      · intro y hy
        simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe] at hy
        obtain ⟨a, ha, hya⟩ := hy
        refine Set.mem_iUnion.mpr ⟨e ⟨a, ha⟩, ?_⟩
        have he : e.symm (e ⟨a, ha⟩) = ⟨a, ha⟩ := Equiv.symm_apply_apply e _
        show y ∈ F (e.symm (e ⟨a, ha⟩)).1
        rw [he]
        exact hya
      · intro y hy
        simp only [Set.mem_iUnion] at hy
        obtain ⟨i, hi⟩ := hy
        exact Set.mem_iUnion.mpr ⟨(e.symm i).1,
          Set.mem_iUnion.mpr ⟨Finset.mem_coe.mpr (e.symm i).2, hi⟩⟩
  · -- `S` misses `B`
    intro b hbB _ hbS
    simp only [Set.mem_iUnion, exists_prop] at hbS
    obtain ⟨a, -, hba⟩ := hbS
    exact Set.disjoint_left.mp (hFB a) hba hbB


end Work.Noncompact.CompressionTube
