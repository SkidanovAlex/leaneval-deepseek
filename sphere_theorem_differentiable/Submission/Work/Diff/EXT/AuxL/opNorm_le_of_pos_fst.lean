import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Filter Set

namespace Work.Diff.EXT.AuxL

/-- If a continuous linear map `L : ℝ × E →L[ℝ] W` satisfies `‖L v‖ ≤ M * ‖v‖` for every `v` whose
first coordinate is positive, then `‖L‖ ≤ M`. -/
theorem opNorm_le_of_pos_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : ℝ × E →L[ℝ] W) {M : ℝ} (h : ∀ v : ℝ × E, 0 < v.1 → ‖L v‖ ≤ M * ‖v‖) :
    ‖L‖ ≤ M := by
  have hM : 0 ≤ M := by
    have h1 := h ((1 : ℝ), 0) (by norm_num)
    have h2 : ‖((1 : ℝ), (0 : E))‖ = 1 := by simp
    rw [h2, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  refine ContinuousLinearMap.opNorm_le_bound L hM fun v => ?_
  by_cases hv1 : 0 < v.1
  · exact h v hv1
  · push_neg at hv1
    rcases lt_or_eq_of_le hv1 with hlt | heq
    · have h1 := h (-v) (by
        rw [Prod.fst_neg]
        linarith)
      rw [map_neg, norm_neg, norm_neg] at h1
      exact h1
    · have hv2 : ‖v‖ = ‖v.2‖ := by
        rw [Prod.norm_def, heq]
        simp
      rw [hv2]
      refine le_of_forall_pos_le_add fun η hη => ?_
      set δ : ℝ := η / (2 * (M + 1)) with hδdef
      have hδpos : 0 < δ := by
        rw [hδdef]
        positivity
      have hw : 0 < (v + (δ, 0)).1 := by
        simp only [Prod.fst_add, heq, zero_add]
        exact hδpos
      have hu : 0 < ((δ, 0) : ℝ × E).1 := hδpos
      have hb1 := h (v + (δ, 0)) hw
      have hb2 := h ((δ, 0) : ℝ × E) hu
      have hnorm1 : ‖v + (δ, 0)‖ = max δ ‖v.2‖ := by
        rw [Prod.norm_def]
        simp only [Prod.fst_add, Prod.snd_add, heq, zero_add]
        rw [add_zero, Real.norm_of_nonneg hδpos.le]
      have hnorm2 : ‖((δ, 0) : ℝ × E)‖ = δ := by
        rw [Prod.norm_mk, norm_zero, Real.norm_of_nonneg hδpos.le, max_eq_left hδpos.le]
      rw [hnorm1] at hb1
      rw [hnorm2] at hb2
      have hdecomp : L v = L (v + (δ, 0)) - L ((δ, 0) : ℝ × E) := by
        rw [← map_sub]
        congr 1
        ext <;> simp
      calc ‖L v‖ = ‖L (v + (δ, 0)) - L ((δ, 0) : ℝ × E)‖ := by rw [hdecomp]
        _ ≤ ‖L (v + (δ, 0))‖ + ‖L ((δ, 0) : ℝ × E)‖ := norm_sub_le _ _
        _ ≤ M * max δ ‖v.2‖ + M * δ := add_le_add hb1 hb2
        _ ≤ M * ‖v.2‖ + η := by
              have h1 : max δ ‖v.2‖ ≤ ‖v.2‖ + δ :=
                max_le (by linarith [norm_nonneg v.2]) (by linarith [hδpos.le])
              have h2 : 2 * M * δ ≤ η := by
                rw [hδdef]
                have hpos : (0 : ℝ) < 2 * (M + 1) := by linarith
                rw [show 2 * M * (η / (2 * (M + 1))) = (2 * M * η) / (2 * (M + 1)) by ring]
                rw [div_le_iff₀ hpos]
                nlinarith [hM, hη]
              nlinarith [h1, h2, hM]

end Work.Diff.EXT.AuxL

namespace Work.Diff.EXT.AuxL

end Work.Diff.EXT.AuxL
