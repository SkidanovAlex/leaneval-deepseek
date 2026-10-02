import Mathlib
import Submission.Work.Whitney.chartNormDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# A local lower bound for the chartwise norm

`Work.Whitney.chartNorm Z φ i` is the fibrewise norm `fibNorm Z φ` read in the chart `i`.  The
purpose of this file is `Work.Whitney.chartNormBound`: near a point `b` of the base set of the
chart `i`, the chartwise norm dominates `δ * ‖v‖` for a constant `δ > 0`, uniformly in the fibre
coordinate `v`.

The proof is a uniform-positivity argument: `chartNorm Z φ i` is continuous on the (open) set
`Z.baseSet i ×ˢ univ` and strictly positive on nonzero fibre vectors there; the unit sphere of `F`
is compact (`ProperSpace F`), so a finite cover of it by product neighbourhoods with positive lower
bounds produces a neighbourhood of `b` and a common positive lower bound.  Positive homogeneity of
`chartNorm` in the fibre coordinate finishes the job.  No local compactness of the base is needed.
-/

namespace Work.Whitney

open Bundle Work.TangentClasses Filter Set
open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-- **Uniform positivity on a compact slice.**  If `g : B × F → ℝ` is continuous at every point
`(b, u)` with `u ∈ S`, where `S ⊆ F` is compact, and positive there, then `g` is bounded below by a
positive constant on a neighbourhood of `b`, uniformly in `u ∈ S`.  (No local compactness of `B` is
used: the compact slice `S` is covered by finitely many product neighbourhoods.) -/
theorem exists_uniform_pos_on_compact {g : B × F → ℝ} {b : B} {S : Set F} (hS : IsCompact S)
    (hg : ∀ u ∈ S, ContinuousAt g (b, u)) (hpos : ∀ u ∈ S, 0 < g (b, u)) :
    ∃ W ∈ nhds b, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ W, ∀ u ∈ S, δ ≤ g (x, u) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨univ, univ_mem, 1, one_pos, fun x _ u hu => (notMem_empty u hu).elim⟩
  have key : ∀ u : ↥S, ∃ (P : Set B) (Q : Set F) (ε : ℝ),
      IsOpen P ∧ IsOpen Q ∧ b ∈ P ∧ (u : F) ∈ Q ∧ 0 < ε ∧
        ∀ x ∈ P, ∀ w ∈ Q, ε ≤ g (x, w) := by
    intro u
    have hu : (u : F) ∈ S := u.2
    have hposu : 0 < g (b, (u : F)) := hpos _ hu
    have hmem : g ⁻¹' (Ioi (g (b, (u : F)) / 2)) ∈ nhds (b, (u : F)) :=
      (hg _ hu).preimage_mem_nhds (isOpen_Ioi.mem_nhds (mem_Ioi.mpr (by linarith)))
    rw [nhds_prod_eq] at hmem
    obtain ⟨P₀, hP₀, Q₀, hQ₀, hPQ⟩ := mem_prod_iff.mp hmem
    obtain ⟨P, hPsub, hPopen, hbP⟩ := mem_nhds_iff.mp hP₀
    obtain ⟨Q, hQsub, hQopen, huQ⟩ := mem_nhds_iff.mp hQ₀
    exact ⟨P, Q, g (b, (u : F)) / 2, hPopen, hQopen, hbP, huQ, by linarith,
      fun x hx w hw => le_of_lt (hPQ ⟨hPsub hx, hQsub hw⟩)⟩
  choose P Q ε hPopen hQopen hbP huQ hε hbound using key
  have hcov : S ⊆ ⋃ u : ↥S, Q u := fun u hu => mem_iUnion.mpr ⟨⟨u, hu⟩, huQ ⟨u, hu⟩⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover Q hQopen hcov
  have htne : t.Nonempty := by
    obtain ⟨u, hu⟩ := hSne
    have h := ht hu
    simp only [mem_iUnion] at h
    obtain ⟨i, hi, -⟩ := h
    exact ⟨i, hi⟩
  refine ⟨⋂ i ∈ t, P i, ?_, (t.image ε).min' (htne.image ε), ?_, ?_⟩
  · rw [mem_nhds_iff]
    exact ⟨_, subset_rfl, isOpen_biInter_finset fun i _ => hPopen i,
      (mem_iInter₂).mpr fun i hi => hbP i⟩
  · rw [Finset.lt_min'_iff]
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact hε i
  · intro x hx u hu
    have hcover := ht hu
    simp only [mem_iUnion] at hcover
    obtain ⟨i, hi, hiu⟩ := hcover
    have hxP : x ∈ P i := (mem_iInter₂.mp hx) i hi
    exact le_trans (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)) (hbound i x hxP u hiu)

theorem chartNormBound {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [ProperSpace F] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℝ B F ι) {φ : PartitionOfUnity ι B Set.univ}
    (hφ : φ.IsSubordinate Z.baseSet) (i : ι) {b : B} (hb : b ∈ Z.baseSet i) :
    ∃ W ∈ nhds b, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ W, ∀ v : F,
      δ * ‖v‖ ≤ chartNorm Z φ i (x, v) := by
  classical
  have hg : ∀ u ∈ Metric.sphere (0 : F) 1, ContinuousAt (chartNorm Z φ i) (b, u) := by
    intro u hu
    refine (continuousOn_chartNorm Z φ i hφ).continuousAt ?_
    exact ((Z.isOpen_baseSet i).prod isOpen_univ).mem_nhds ⟨hb, mem_univ u⟩
  have hpos : ∀ u ∈ Metric.sphere (0 : F) 1, 0 < chartNorm Z φ i (b, u) := by
    intro u hu
    refine (chartNorm_pos_iff Z φ hφ i hb u).mpr ?_
    intro h0
    have h1 := Metric.mem_sphere.mp hu
    rw [h0, dist_self] at h1
    exact one_ne_zero h1.symm
  obtain ⟨W, hW, δ, hδpos, hδ⟩ :=
    exists_uniform_pos_on_compact (isCompact_sphere (0 : F) 1) hg hpos
  refine ⟨W, hW, δ, hδpos, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · rw [hv, chartNorm_zero, norm_zero, mul_zero]
  · have hsphere : (‖v‖⁻¹) • v ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact norm_smul_inv_norm hv
    have hbnd : δ ≤ chartNorm Z φ i (x, (‖v‖⁻¹) • v) := hδ x hx _ hsphere
    have hsmul : ‖v‖ • ((‖v‖⁻¹) • v) = v := by
      rw [← mul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    calc δ * ‖v‖ = ‖v‖ * δ := mul_comm _ _
      _ ≤ ‖v‖ * chartNorm Z φ i (x, (‖v‖⁻¹) • v) :=
          mul_le_mul_of_nonneg_left hbnd (norm_nonneg v)
      _ = chartNorm Z φ i (x, v) := by
          rw [← chartNorm_smul Z φ i x (norm_nonneg v) ((‖v‖⁻¹) • v), hsmul]

end

end Work.Whitney
