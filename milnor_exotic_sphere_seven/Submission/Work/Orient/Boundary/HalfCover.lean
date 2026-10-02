import Mathlib
import Submission.Work.Orient.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cover of a compact set by coordinate half-balls

This is the half-space analogue of `Work.ThomBordism.exists_ball_cover_avoiding`
(`Submission/Work/Orient/Port/Hatcher.lean`): a compact set `A` of a space charted in the half-space
model is covered by finitely many coordinate half-balls centred at points of `A` and avoiding a
closed set disjoint from `A`.  It is one of the ingredients of the half-space port
(`Work.Orient.HalfCoverProp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **Shrinking a neighbourhood of a point of the half-space to a ball.**  The half-space
`EuclideanHalfSpace (n+1)` carries no metric of its own; the ball is taken in the ambient space
through `Work.Orient.halfIncl` (the closed embedding `𝓡∂ (n + 1)`). -/
theorem exists_ball_subset_of_mem {n : ℕ} {V : Set (EuclideanHalfSpace (n + 1))}
    (hV : IsOpen V) {c : EuclideanHalfSpace (n + 1)} (hc : c ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧ halfIncl (n + 1) ⁻¹' Metric.ball (halfIncl (n + 1) c) ρ ⊆ V := by
  obtain ⟨V', hV'open, hV'eq⟩ := isOpen_induced_iff.mp hV
  have hc' : (Subtype.val c : EuclideanSpace ℝ (Fin (n + 1))) ∈ V' := by
    have h := hc
    rw [← hV'eq] at h
    exact h
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hV'open _ hc'
  exact ⟨ρ, hρ, fun y hy => by rw [← hV'eq]; exact hρsub hy⟩

/-- **A point of an open set is contained in a coordinate half-ball inside it.**  The half-space
analogue of `Work.Orient.Port.exists_coordBall_subset`. -/
theorem exists_halfBall_subset (n : ℕ) {W : TopCat} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {U : Set W} (hU : IsOpen U) {a : W}
    (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ halfBallGood (n + 1) W a r ∧ halfBallPiece (n + 1) W a r ⊆ U := by
  set e := chartAt (EuclideanHalfSpace (n + 1)) a with he
  have hae : a ∈ e.source := mem_chart_source _ a
  have himg : IsOpen (e '' (e.source ∩ U)) := e.isOpen_image_source_inter hU
  obtain ⟨ρ, hρ, hρsub⟩ :=
    exists_ball_subset_of_mem (n := n) himg ⟨a, ⟨hae, ha⟩, rfl⟩
  obtain ⟨ρ', hρ', hρ'sub⟩ :=
    exists_ball_subset_of_mem (n := n) e.open_target (e.map_source hae)
  refine ⟨min ρ ρ', lt_min hρ hρ', ?_, ?_⟩
  · exact fun y hy => hρ'sub ((Metric.ball_subset_ball (min_le_right _ _)) hy)
  · intro y hy
    obtain ⟨hyb, hys⟩ := hy
    have hb : halfIncl (n + 1) (e y) ∈ Metric.ball (halfIncl (n + 1) (e a)) ρ := by
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.mp hyb
      have h2 : min ρ ρ' / 2 < ρ := by linarith [min_le_left ρ ρ', hρ]
      linarith
    obtain ⟨x, hx, hxe⟩ := hρsub hb
    have hxya : x = y := by
      calc x = e.symm (e x) := (e.left_inv hx.1).symm
        _ = e.symm (e y) := by rw [hxe]
        _ = y := e.left_inv hys
    rw [← hxya]
    exact hx.2

/-- **A compact set is covered by finitely many coordinate half-balls centred at its points,
avoiding a disjoint closed set** — the half-space analogue of
`Work.Orient.Port.exists_ball_cover_avoiding` (`Work.ThomBordism.exists_ball_cover_avoiding`). -/
theorem HalfCover (n : ℕ) (W : TopCat.{0}) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {A S : Set W}
    (hA : IsCompact A) (hAS : Disjoint A S) (hS : IsClosed S) :
    ∃ (m : ℕ) (z : Fin m → W) (r : Fin m → ℝ),
      (∀ i, 0 < r i) ∧ (∀ i, halfBallGood (n + 1) W (z i) (r i)) ∧
      (∀ i, z i ∈ A) ∧
      A ⊆ ⋃ i, halfBallPiece (n + 1) W (z i) (r i) ∧
      Disjoint S (⋃ i, halfBallPiece (n + 1) W (z i) (r i)) := by
  classical
  have key : ∀ a : W, a ∈ A → ∃ r : ℝ, 0 < r ∧ halfBallGood (n + 1) W a r ∧
      halfBallPiece (n + 1) W a r ⊆ Sᶜ :=
    fun a ha => exists_halfBall_subset n hS.isOpen_compl (Set.disjoint_left.mp hAS ha)
  choose! r hr hgood hsub using key
  let K : W → Set W := fun a => halfBallPiece (n + 1) W a (r a)
  let U : W → Set W := fun a => (chartAt (EuclideanHalfSpace (n + 1)) a) ⁻¹'
      (halfIncl (n + 1) ⁻¹'
        Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)) (r a / 2)) ∩
      (chartAt (EuclideanHalfSpace (n + 1)) a).source
  have hUopen : ∀ a, IsOpen (U a) := by
    intro a
    show IsOpen ((chartAt (EuclideanHalfSpace (n + 1)) a) ⁻¹'
      (halfIncl (n + 1) ⁻¹'
        Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a))
          (r a / 2)) ∩ (chartAt (EuclideanHalfSpace (n + 1)) a).source)
    rw [Set.inter_comm]
    exact (chartAt (EuclideanHalfSpace (n + 1)) a).isOpen_inter_preimage
      (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hUL : ∀ a, U a ⊆ K a := by
    intro a y hy
    exact ⟨Metric.ball_subset_closedBall hy.1, hy.2⟩
  have hUmem : ∀ a ∈ A, a ∈ U a := by
    intro a ha
    refine ⟨?_, mem_chart_source _ a⟩
    show halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a) ∈
      Metric.ball (halfIncl (n + 1) ((chartAt (EuclideanHalfSpace (n + 1)) a) a)) (r a / 2)
    exact Metric.mem_ball_self (by linarith [hr a ha])
  have hcov : A ⊆ ⋃ a, (if a ∈ A then U a else (∅ : Set W)) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨y, by rw [if_pos hy]; exact hUmem y hy⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover
    (fun a => if a ∈ A then U a else (∅ : Set W))
    (fun a => by split <;> simp [hUopen]) hcov
  let t' : Finset W := t.filter (fun a => a ∈ A)
  let z : Fin t'.card → W := fun k => ((t'.equivFin.symm k : ↥t') : W)
  have hz_mem : ∀ i, z i ∈ A := fun i => (Finset.mem_filter.mp (t'.equivFin.symm i).2).2
  have hz_apply : ∀ (a : W) (ha : a ∈ t'), z (t'.equivFin ⟨a, ha⟩) = a := by
    intro a ha
    show (((t'.equivFin.symm (t'.equivFin ⟨a, ha⟩)) : ↥t') : W) = a
    rw [Equiv.symm_apply_apply]
  refine ⟨t'.card, z, fun i => r (z i), fun i => hr (z i) (hz_mem i),
    fun i => hgood (z i) (hz_mem i), hz_mem, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    by_cases haA : a ∈ A
    · have ha' : a ∈ t' := Finset.mem_filter.mpr ⟨ha, haA⟩
      rw [if_pos haA] at hxa
      refine Set.mem_iUnion.mpr ⟨t'.equivFin ⟨a, ha'⟩, ?_⟩
      simp only [hz_apply a ha']
      exact (hUL a) hxa
    · rw [if_neg haA] at hxa
      exact absurd hxa (Set.notMem_empty x)
  · rw [Set.disjoint_left]
    intro y hy hyU
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyU
    exact hsub (z i) (hz_mem i) hyi hy

end

end Work.Orient.Boundary
