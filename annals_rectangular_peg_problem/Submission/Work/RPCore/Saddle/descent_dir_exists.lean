import Mathlib
import Submission.Work.RPCore.Saddle.descent_defs
import Submission.Work.RPCore.Saddle.descent_identity
import Submission.Work.RPCore.Saddle.descent_opnorm_le
import Submission.Work.RPCore.Saddle.descent_data_continuous

/-!
# A continuous field of descent directions

Given `F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ` of class `C^1` whose
gradient is nowhere smaller than `δ > 0`, we build a continuous map `u` with `‖u z‖ ≤ 1` and
`(fderiv ℝ F z) (u z) ≤ -δ/2` for all `z`.

The construction is a *soft* normalisation.  Writing the continuous linear functional
`L = fderiv ℝ F z` in the block coordinates of `descent_defs.lean` as
`L (a, (x, y)) = cval L * a + ⟪g1 L, x⟫ + ⟪g2 L, y⟫`, and writing `uvec β L` for the vector obtained by
normalising each of the three blocks at scale `β`, the descent estimate is

`L (uvec β L) = -(hnorm β ‖cval L‖ + hnorm β ‖g1 L‖ + hnorm β ‖g2 L‖)`

with `hnorm β t = t^2 / max t β ≥ t - β`.  Since `‖L‖ ≤ ‖cval L‖ + ‖g1 L‖ + ‖g2 L‖` and
`‖L‖ ≥ δ`, taking `β = δ/6` gives `L (uvec (δ/6) L) ≤ -(δ - 3β) = -δ/2`.
-/

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

noncomputable section

variable {k l : ℕ}

/-- Scalar inequality: `hnorm β t ≥ t - β` for `β > 0` (and every real `t`). -/
theorem hnorm_ge {β : ℝ} (hβ : 0 < β) (t : ℝ) : t - β ≤ hnorm β t := by
  rcases le_total β t with h | h
  · rw [hnorm, max_eq_left h, pow_two]
    rw [mul_div_cancel_left₀ _ (ne_of_gt (lt_of_lt_of_le hβ h))]
    linarith
  · rw [hnorm, max_eq_right h]
    have : 0 ≤ t ^ 2 / β := div_nonneg (sq_nonneg t) (le_of_lt hβ)
    linarith

/-- The descent vector has norm at most one. -/
theorem uvec_norm_le {β : ℝ} (hβ : 0 < β) (L : D k l →L[ℝ] ℝ) : ‖uvec β L‖ ≤ 1 := by
  rw [uvec, Prod.norm_mk, Prod.norm_mk]
  have hM : 0 < max |cval L| β := lt_of_lt_of_le hβ (le_max_right _ _)
  refine max_le ?_ (max_le ?_ ?_)
  · have h1 : ‖(-(cval L)) / max |cval L| β‖ = |cval L| / max |cval L| β := by
      rw [norm_div, norm_neg]
      simp only [Real.norm_eq_abs, abs_of_pos hM]
    rw [h1]
    exact (div_le_one hM).mpr (le_max_left _ _)
  · have hg : 0 < max ‖g1 L‖ β := lt_of_lt_of_le hβ (le_max_right _ _)
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr (le_of_lt hg))]
    calc (max ‖g1 L‖ β)⁻¹ * ‖g1 L‖
        ≤ (max ‖g1 L‖ β)⁻¹ * max ‖g1 L‖ β :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt (inv_pos.mpr hg))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hg)
  · have hg : 0 < max ‖g2 L‖ β := lt_of_lt_of_le hβ (le_max_right _ _)
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr (le_of_lt hg))]
    calc (max ‖g2 L‖ β)⁻¹ * ‖g2 L‖
        ≤ (max ‖g2 L‖ β)⁻¹ * max ‖g2 L‖ β :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt (inv_pos.mpr hg))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hg)

/-- The core descent estimate: if `‖L‖ ≥ δ > 0` then `L (uvec (δ/6) L) ≤ -δ/2`. -/
theorem descent_core (δ : ℝ) (hδ : 0 < δ) (L : D k l →L[ℝ] ℝ) (hL : δ ≤ ‖L‖) :
    L (uvec (δ/6) L) ≤ -δ/2 := by
  have hβ : 0 < δ/6 := by positivity
  rw [descent_identity]
  simp only [uvec]
  have hc : cval L * (-(cval L) / max |cval L| (δ/6)) = -hnorm (δ/6) |cval L| := by
    rw [hnorm, sq_abs]
    ring
  have hX : inner ℝ (g1 L) (-(max ‖g1 L‖ (δ/6))⁻¹ • g1 L) = -hnorm (δ/6) ‖g1 L‖ := by
    rw [hnorm, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hY : inner ℝ (g2 L) (-(max ‖g2 L‖ (δ/6))⁻¹ • g2 L) = -hnorm (δ/6) ‖g2 L‖ := by
    rw [hnorm, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  rw [hc, hX, hY]
  have e1 : |cval L| - δ/6 ≤ hnorm (δ/6) |cval L| := hnorm_ge hβ _
  have e2 : ‖g1 L‖ - δ/6 ≤ hnorm (δ/6) ‖g1 L‖ := hnorm_ge hβ _
  have e3 : ‖g2 L‖ - δ/6 ≤ hnorm (δ/6) ‖g2 L‖ := hnorm_ge hβ _
  have hs : δ ≤ |cval L| + ‖g1 L‖ + ‖g2 L‖ := le_trans hL (descent_opnorm_le L)
  linarith

/-- Continuity of the field `z ↦ uvec β (fderiv ℝ F z)`. -/
theorem uvec_continuous {k l : ℕ} (F : D k l → ℝ) (hF : ContDiff ℝ 1 F) {β : ℝ}
    (hβ : 0 < β) : Continuous fun z => uvec β (fderiv ℝ F z) := by
  have h := descent_data_continuous F hF
  have hc : Continuous fun z => cval (fderiv ℝ F z) := continuous_fst.comp h
  have hX : Continuous fun z => g1 (fderiv ℝ F z) := continuous_fst.comp (continuous_snd.comp h)
  have hY : Continuous fun z => g2 (fderiv ℝ F z) := continuous_snd.comp (continuous_snd.comp h)
  have habs : Continuous fun z => |cval (fderiv ℝ F z)| := by
    simpa only [Real.norm_eq_abs] using hc.norm
  have h1 : Continuous fun z => -(cval (fderiv ℝ F z)) / max |cval (fderiv ℝ F z)| β := by
    apply Continuous.div
    · exact hc.neg
    · exact habs.max continuous_const
    · intro z
      exact ne_of_gt (lt_of_lt_of_le hβ (le_max_right _ _))
  have h2 : Continuous fun z => -(max ‖g1 (fderiv ℝ F z)‖ β)⁻¹ • g1 (fderiv ℝ F z) := by
    have hs : Continuous fun z => -(max ‖g1 (fderiv ℝ F z)‖ β)⁻¹ := by
      apply Continuous.neg
      exact (hX.norm.max continuous_const).inv₀
        (fun z => ne_of_gt (lt_of_lt_of_le hβ (le_max_right _ _)))
    exact hs.smul hX
  have h3 : Continuous fun z => -(max ‖g2 (fderiv ℝ F z)‖ β)⁻¹ • g2 (fderiv ℝ F z) := by
    have hs : Continuous fun z => -(max ‖g2 (fderiv ℝ F z)‖ β)⁻¹ := by
      apply Continuous.neg
      exact (hY.norm.max continuous_const).inv₀
        (fun z => ne_of_gt (lt_of_lt_of_le hβ (le_max_right _ _)))
    exact hs.smul hY
  simp only [uvec]
  exact h1.prodMk (h2.prodMk h3)

theorem descent_dir_exists {k l : ℕ}
    (F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ)
    (hF : ContDiff ℝ 1 F) (δ : ℝ) (hδ : 0 < δ)
    (hδF : ∀ z, δ ≤ ‖fderiv ℝ F z‖) :
    ∃ u : (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) →
        (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))),
      Continuous u ∧ (∀ z, ‖u z‖ ≤ 1) ∧
      (∀ z, (fderiv ℝ F z) (u z) ≤ -δ / 2) := by
  refine ⟨fun z => uvec (δ/6) (fderiv ℝ F z), ?_, ?_, ?_⟩
  · exact uvec_continuous F hF (by positivity)
  · intro z
    exact uvec_norm_le (by positivity) (fderiv ℝ F z)
  · intro z
    exact descent_core δ hδ (fderiv ℝ F z) (hδF z)

end

end Work.RPCore.Saddle
