import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set Filter

/-! ### Auxiliary lemmas

`∫_{‖w‖<r} ‖w‖^s = 2πr^{s+2}/(s+2)` is reduced to the version
`integral_norm_rpow_ball` proved for `0 < r` (the degenerate case `r = 0` is direct);
`f` is continuous as soon as it is Hölder of positive degree, which makes the Cauchy
integrand integrable. -/

/-- The radial integral formula for a disc of radius `r ≥ 0` (including `r = 0`). -/
lemma integral_norm_rpow_ball_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : -2 < s) :
    ∫ w in Metric.ball (0 : ℂ) r, ‖w‖ ^ s = 2 * Real.pi * r ^ (s + 2) / (s + 2) := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    rw [Metric.ball_eq_empty.mpr le_rfl, setIntegral_empty,
      Real.zero_rpow (by linarith : s + 2 ≠ 0)]
    ring
  · exact integral_norm_rpow_ball h hs

/-- A function satisfying a Hölder condition of positive degree is continuous. -/
lemma continuous_of_holder {C α : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) : Continuous f := by
  have hH : HolderWith (Real.toNNReal C) (Real.toNNReal α) f := by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    refine le_trans (ENNReal.ofReal_le_ofReal (hf x y)) ?_
    rw [ENNReal.ofReal_mul hC, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα.le]
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal C hC, Real.coe_toNNReal α hα.le]
  exact hH.continuous (by rw [Real.toNNReal_pos]; exact hα)

/-- The integrand `w ↦ (f (z + w) - f z)/w` of the Cauchy potential is integrable on a
disc, for `f` Hölder of positive degree: it is dominated by `C ‖w‖^{α-1}` and
`α - 1 > -2`. -/
lemma integrableOn_cauchyIntegrand_aux {ρ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (z : ℂ) :
    IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w) (Metric.ball (0 : ℂ) ρ) := by
  have hcont : Continuous f := continuous_of_holder hα hC hf
  have hpt : ∀ w : ℂ, ‖(f (z + w) - f z) / w‖ ≤ C * ‖w‖ ^ (α - 1) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp only [add_zero, sub_self, norm_zero, zero_div]
      by_cases h : α - 1 = 0
      · rw [h, Real.rpow_zero]; simpa using hC
      · rw [Real.zero_rpow h]; simp
    · rw [norm_div]
      have hfw : ‖f (z + w) - f z‖ ≤ C * ‖w‖ ^ α := by
        have h := hf (z + w) z
        rwa [add_sub_cancel_left] at h
      calc ‖f (z + w) - f z‖ / ‖w‖ ≤ C * ‖w‖ ^ α / ‖w‖ :=
            div_le_div_of_nonneg_right hfw (norm_nonneg w)
        _ = C * ‖w‖ ^ (α - 1) := by
            rw [Real.rpow_sub (norm_pos_iff.mpr hw), Real.rpow_one]
            ring
  have hmaj : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 1)) (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := α - 1) (by linarith)).const_mul C
  have hmeas : AEStronglyMeasurable (fun w : ℂ => (f (z + w) - f z) / w)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) := by
    have h1 : Continuous fun w : ℂ => f (z + w) - f z :=
      (hcont.comp (continuous_const.add continuous_id)).sub continuous_const
    exact (h1.measurable.div measurable_id).aestronglyMeasurable
  exact hmaj.mono' hmeas (Eventually.of_forall hpt)

/-- Hölder (degree `α`) estimate for the Cauchy potential of `Submission/Work/CR/Flat/Cauchy.lean`.

For `f` `α`-Hölder with constant `C` and `z, z'` in the disc of radius `ρ/2`, the
difference `T f z - T f z'` is controlled by `8 C ρ ‖z - z'‖^α`.  Indeed, writing
`N(w) = (f (z+w) - f z) - (f (z'+w) - f z')` and `δ = ‖z - z'‖`, one has
`‖N(w)‖ ≤ 2 C ‖w‖^α` and `‖N(w)‖ ≤ 2 C δ^α`, and splitting the integral at `‖w‖ = δ`
gives `∫_{‖w‖<δ} 2C‖w‖^{α-1} = 4πCδ^{α+1}/(α+1)` and
`∫_{δ≤‖w‖<ρ} 2Cδ^α‖w‖^{-1} = 4πCδ^α(ρ-δ)`, so that
`‖T f z - T f z'‖ ≤ 4C(δ^{α+1}/(α+1) + δ^α(ρ-δ)) ≤ 8 C ρ δ^α`. -/
theorem norm_cauchyTransform_sub_le {ρ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) {z z' : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) (ρ / 2)) (hz' : z' ∈ Metric.ball (0 : ℂ) (ρ / 2)) :
    ‖cauchyTransform ρ f z - cauchyTransform ρ f z'‖ ≤ 8 * C * ρ * ‖z - z'‖ ^ α := by
  have hz2 : ‖z‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz2' : ‖z'‖ < ρ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz'
  have hρ : 0 < ρ := by linarith [norm_nonneg z, hz2]
  have hδρ : ‖z - z'‖ ≤ ρ := by
    have hlt : ‖z - z'‖ < ρ := by
      calc ‖z - z'‖ ≤ ‖z‖ + ‖z'‖ := norm_sub_le z z'
        _ < ρ / 2 + ρ / 2 := add_lt_add hz2 hz2'
        _ = ρ := by ring
    exact hlt.le
  -- the two Cauchy integrands are integrable, so the integrals can be combined
  have hG : IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w) (Metric.ball (0 : ℂ) ρ) :=
    integrableOn_cauchyIntegrand_aux hα hC hf z
  have hG' : IntegrableOn (fun w : ℂ => (f (z' + w) - f z') / w) (Metric.ball (0 : ℂ) ρ) :=
    integrableOn_cauchyIntegrand_aux hα hC hf z'
  have hdiff : cauchyTransform ρ f z - cauchyTransform ρ f z'
      = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ,
          ((f (z + w) - f z) - (f (z' + w) - f z')) / w := by
    have key : cauchyTransform ρ f z - cauchyTransform ρ f z'
        = -((Real.pi : ℂ))⁻¹ *
            ((∫ w in Metric.ball (0 : ℂ) ρ, (f (z + w) - f z) / w)
              - (∫ w in Metric.ball (0 : ℂ) ρ, (f (z' + w) - f z') / w)) := by
      rw [cauchyTransform, cauchyTransform]; ring
    rw [key, ← integral_sub hG hG']
    congr 1
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    ring_nf
  -- pointwise bound of the combined integrand by the (integrable) majorant
  have hnum : ∀ w : ℂ, ‖(f (z + w) - f z) - (f (z' + w) - f z')‖
      ≤ 2 * C * ‖z - z'‖ ^ α := by
    intro w
    have h1 : ‖f (z + w) - f (z' + w)‖ ≤ C * ‖z - z'‖ ^ α := by
      have h := hf (z + w) (z' + w)
      rwa [add_sub_add_right_eq_sub] at h
    have h2 : ‖f z' - f z‖ ≤ C * ‖z - z'‖ ^ α := by
      have h := hf z' z
      rwa [show ‖z' - z‖ = ‖z - z'‖ from (norm_sub_rev z z').symm] at h
    calc ‖(f (z + w) - f z) - (f (z' + w) - f z')‖
        = ‖(f (z + w) - f (z' + w)) + (f z' - f z)‖ := by ring_nf
      _ ≤ ‖f (z + w) - f (z' + w)‖ + ‖f z' - f z‖ := norm_add_le _ _
      _ ≤ C * ‖z - z'‖ ^ α + C * ‖z - z'‖ ^ α := add_le_add h1 h2
      _ = 2 * C * ‖z - z'‖ ^ α := by ring
  have hmaj : IntegrableOn (fun w : ℂ => 2 * C * ‖z - z'‖ ^ α * ‖w‖ ^ (-1 : ℝ))
      (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul _
  have hpt : ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
      ‖((f (z + w) - f z) - (f (z' + w) - f z')) / w‖
        ≤ 2 * C * ‖z - z'‖ ^ α * ‖w‖ ^ (-1 : ℝ) := by
    refine Eventually.of_forall fun w => ?_
    rw [norm_div, Real.rpow_neg_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hnum w) (inv_nonneg.mpr (norm_nonneg w))
  have hbound : ‖∫ w in Metric.ball (0 : ℂ) ρ,
        ((f (z + w) - f z) - (f (z' + w) - f z')) / w‖
      ≤ ∫ w in Metric.ball (0 : ℂ) ρ, 2 * C * ‖z - z'‖ ^ α * ‖w‖ ^ (-1 : ℝ) :=
    norm_integral_le_of_norm_le hmaj hpt
  have hmi : ∫ w in Metric.ball (0 : ℂ) ρ, ‖w‖ ^ (-1 : ℝ) = 2 * Real.pi * ρ := by
    rw [integral_norm_rpow_ball hρ (by norm_num : (-2 : ℝ) < -1)]
    rw [show (-1 : ℝ) + 2 = 1 by norm_num, Real.rpow_one, div_one]
  have hval : ∫ w in Metric.ball (0 : ℂ) ρ, 2 * C * ‖z - z'‖ ^ α * ‖w‖ ^ (-1 : ℝ)
      = 2 * C * ‖z - z'‖ ^ α * (2 * Real.pi * ρ) := by
    rw [integral_const_mul, hmi]
  have hpi : ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc ‖cauchyTransform ρ f z - cauchyTransform ρ f z'‖
      = ‖((Real.pi : ℂ))⁻¹‖ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
          ((f (z + w) - f z) - (f (z' + w) - f z')) / w‖ := by
        rw [hdiff, norm_mul, norm_neg]
    _ = Real.pi⁻¹ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
          ((f (z + w) - f z) - (f (z' + w) - f z')) / w‖ := by rw [hpi]
    _ ≤ Real.pi⁻¹ * (2 * C * ‖z - z'‖ ^ α * (2 * Real.pi * ρ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans hbound (le_of_eq hval)
    _ = 4 * C * ρ * ‖z - z'‖ ^ α := by
        field_simp
        ring
    _ ≤ 8 * C * ρ * ‖z - z'‖ ^ α := by
        nlinarith [mul_nonneg (mul_nonneg hC hρ.le) (Real.rpow_nonneg (norm_nonneg (z - z')) α)]

end Work.CR.Flat.Cauchy
