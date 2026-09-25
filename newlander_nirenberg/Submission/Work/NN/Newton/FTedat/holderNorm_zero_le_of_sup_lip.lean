import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.NN.Newton.FTedat

open scoped ENNReal NNReal

/-- If `g` is bounded by `M` and `L`-Lipschitz, then its `C^{0,α}` norm (for `0 < α < 1`) on all of
`X` is bounded by `M + max L (2 * M)`: the sup bound gives `M`, the Lipschitz bound gives `L` on
the small scales (`‖x - y‖ ≤ 1`, where `‖x - y‖ ≤ ‖x - y‖ ^ α`) and `2 * M` on the large scales
(`‖x - y‖ ≥ 1`, where `1 ≤ ‖x - y‖ ^ α`). -/
lemma holderNorm_zero_le_of_sup_lip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {g : X → ℂ} {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (h0 : ∀ x, ‖g x‖ ≤ M) (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    Work.CR.Flat.holderNorm 0 α g Set.univ ≤ ENNReal.ofReal (M + max L (2 * M)) := by
  have hmax : 0 ≤ max L (2 * M) := le_trans hL (le_max_left L (2 * M))
  -- The sup-norm part.
  have hstep1 : Work.CR.Flat.iterDerivNorm 0 g Set.univ ≤ ENNReal.ofReal M := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal (h0 x)
  -- The Hölder seminorm part.
  have hstep2 : Work.CR.Flat.holderSeminorm 0 α g Set.univ ≤
      ENNReal.ofReal (max L (2 * M)) := by
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    have hdiff : ‖iteratedFDerivWithin ℝ 0 g Set.univ x - iteratedFDerivWithin ℝ 0 g Set.univ y‖
        = ‖g x - g y‖ := by
      simpa [dist_eq_norm] using dist_iteratedFDerivWithin_zero (𝕜 := ℝ) g Set.univ x g Set.univ y
    rw [hdiff]
    refine ENNReal.ofReal_le_ofReal ?_
    have ht : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have htp : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos ht α
    rw [div_le_iff₀ htp]
    by_cases hle : ‖x - y‖ ≤ 1
    · -- small scales: `‖x - y‖ ≤ ‖x - y‖ ^ α`, so the Lipschitz bound `L` suffices
      have h1 : ‖x - y‖ ^ (1 : ℝ) ≤ ‖x - y‖ ^ α :=
        Real.rpow_le_rpow_of_exponent_ge ht hle (by linarith)
      rw [Real.rpow_one] at h1
      calc ‖g x - g y‖ ≤ L * ‖x - y‖ := hlip x y
        _ ≤ L * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left h1 hL
        _ ≤ max L (2 * M) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left L (2 * M)) htp.le
    · -- large scales: `1 ≤ ‖x - y‖ ^ α`, so the trivial bound `2 * M` suffices
      have hge : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hle)
      have h1 : (1 : ℝ) ≤ ‖x - y‖ ^ α := Real.one_le_rpow hge hα0.le
      have h2 : ‖g x - g y‖ ≤ 2 * M := by
        calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (h0 x) (h0 y)
          _ = 2 * M := by ring
      calc ‖g x - g y‖ ≤ 2 * M := h2
        _ ≤ 2 * M * ‖x - y‖ ^ α := by
            have h3 : 2 * M * 1 ≤ 2 * M * ‖x - y‖ ^ α :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
            simpa using h3
        _ ≤ max L (2 * M) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right L (2 * M)) htp.le
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ENNReal.ofReal_add hM hmax]
  exact add_le_add hstep1 hstep2

end Work.NN.Newton.FTedat
