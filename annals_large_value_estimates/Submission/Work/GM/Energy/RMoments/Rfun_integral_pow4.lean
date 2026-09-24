import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.RMoments.FejerDefs
import Submission.Work.GM.Energy.RMoments.fejerK_transform
import Submission.Work.GM.Energy.RMoments.expSum_pow4_expansion
import Submission.Work.GM.Energy.RMoments.integral_Rfun_eq

/-!
# The fourth moment of `R` over `[1,2]` and the additive energy

`Rfun W v = Σ_{t∈W} |v|^{it}`.  This file proves `∫_1^2 ‖Rfun W v‖⁴ dv ≪ E(W)` for a
`1`-separated set `W`, i.e. the standard "`L⁴` of the exponential sum = additive energy" bound
localised to `v ∈ [1,2]`.

The proof: substitute `v = e^u` (`u ∈ [0, log 2]`, `dv = e^u du`), majorise the interval by the
Fejér kernel `fejerK u = (2π)⁻¹ sinc(u/2)²`, which is nonnegative and `≥ 1/(4π)` on `[0, log 2]`
while its Fourier transform is the triangle function `tri` supported in `[-1,1]`.  Expanding
`‖Σ_{t∈W} e^{itu}‖⁴ = Σ_{q ∈ W⁴} e^{i q_s u}` and integrating termwise gives
`∫ fejerK u ‖Σ‖⁴ du = Σ_{q ∈ W⁴} tri(q_s) ≤ #{q : |q_s| ≤ 1} = E(W)`.
-/

namespace Work.GM.Energy.RMoments

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

/-- `u ↦ fejerK u * ‖expSum W u‖⁴` is integrable (it is dominated by `fejerK u * |W|⁴`). -/
lemma integrable_fejerK_mul_pow4 (W : Finset ℝ) :
    Integrable (fun u : ℝ => fejerK u * ‖expSum W u‖ ^ 4) := by
  refine Integrable.mono' (g := fun u : ℝ => fejerK u * (W.card : ℝ) ^ 4)
    (fejerK_integrable.mul_const _) ?_ ?_
  · exact (fejerK_continuous.mul ((continuous_expSum W).norm.pow 4)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fejerK_nonneg u) (by positivity))]
    have h2 : ‖expSum W u‖ ^ 4 ≤ (W.card : ℝ) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le_card W u) 4
    nlinarith [fejerK_nonneg u]

/-- The triangle function is at most `1` on `|x| ≤ 1` and vanishes for `|x| ≥ 1`, so the sum of
`tri (sumdiff q)` over the quadruples is at most the number of quadruples with
`|q₁ + q₂ - q₃ - q₄| ≤ 1`, i.e. the additive energy `E(W)`. -/
lemma sum_tri_sumdiff_le_energy (W : Finset ℝ) :
    (∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W : Finset (ℝ × ℝ × ℝ × ℝ)),
        Commons.Analysis.Fourier.tri (sumdiff q)) ≤ (Submission.GM.energy W : ℝ) := by
  classical
  set Q : Finset (ℝ × ℝ × ℝ × ℝ) := W ×ˢ W ×ˢ W ×ˢ W with hQ
  have h1 : ∀ q ∈ Q, Commons.Analysis.Fourier.tri (sumdiff q)
      ≤ if |sumdiff q| ≤ 1 then (1:ℝ) else 0 := by
    intro q _
    by_cases h : |sumdiff q| ≤ 1
    · rw [if_pos h, Commons.Analysis.Fourier.tri]
      exact max_le (by linarith [abs_nonneg (sumdiff q)]) (by norm_num)
    · rw [if_neg h,
        Commons.Analysis.Fourier.tri_eq_zero_of_one_le_abs (by linarith [not_le.mp h])]
  calc ∑ q ∈ Q, Commons.Analysis.Fourier.tri (sumdiff q)
      ≤ ∑ q ∈ Q, (if |sumdiff q| ≤ 1 then (1:ℝ) else 0) := Finset.sum_le_sum h1
    _ = ((Q.filter (fun q => |sumdiff q| ≤ 1)).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
    _ = (Submission.GM.energy W : ℝ) := by
        unfold Submission.GM.energy
        rw [hQ]
        simp only [sumdiff]
        rfl

/-- The integral of `fejerK` against `‖expSum W ·‖⁴` is the sum of the triangle function over the
quadruple sum-differences: expand the fourth power and integrate termwise, using that the Fourier
transform of `fejerK` is `tri`. -/
lemma integral_fejerK_expSum_pow4 (W : Finset ℝ) :
    (∫ u : ℝ, fejerK u * ‖expSum W u‖ ^ 4)
      = ∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W : Finset (ℝ × ℝ × ℝ × ℝ)),
          Commons.Analysis.Fourier.tri (sumdiff q) := by
  classical
  set Q : Finset (ℝ × ℝ × ℝ × ℝ) := W ×ˢ W ×ˢ W ×ˢ W with hQ
  have hexpQ : ∀ u : ℝ, ((‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ Q, cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) := by
    intro u; rw [expSum_pow4_expansion W u, hQ]
  have hF : ∀ q ∈ Q, Integrable (fun u : ℝ =>
      ((fejerK u : ℝ) : ℂ) * cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ))) := by
    intro q _
    refine Integrable.mono' (g := fejerK) fejerK_integrable ?_ ?_
    · exact ((Complex.continuous_ofReal.comp fejerK_continuous).mul
        (by fun_prop : Continuous fun u : ℝ =>
          cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)))).aestronglyMeasurable
    · filter_upwards with u
      rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one,
        show ‖((fejerK u : ℝ) : ℂ)‖ = |fejerK u| from RCLike.norm_ofReal _,
        abs_of_nonneg (fejerK_nonneg u)]
  have hpoint : ∀ u : ℝ, ((fejerK u * ‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ Q, ((fejerK u : ℝ) : ℂ)
          * cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) := by
    intro u
    rw [Complex.ofReal_mul, hexpQ u, Finset.mul_sum]
  have hpointc : ∀ u : ℝ, ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ Q, ((fejerK u : ℝ) : ℂ)
          * cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) := by
    intro u
    rw [← Complex.ofReal_mul]; exact hpoint u
  have hintL : Integrable (fun u : ℝ =>
      ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ)) := by
    rw [show (fun u : ℝ => ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ))
        = fun u : ℝ => ∑ q ∈ Q, ((fejerK u : ℝ) : ℂ)
            * cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) from funext hpointc]
    exact Commons.Analysis.Fourier.integrable_finset_sum Q hF
  have hmain : (∫ u : ℝ, ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ))
      = ∑ q ∈ Q, ((Commons.Analysis.Fourier.tri (sumdiff q) : ℝ) : ℂ) := by
    rw [show (∫ u : ℝ, ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ))
        = ∫ u : ℝ, ∑ q ∈ Q, ((fejerK u : ℝ) : ℂ)
            * cexp (Complex.I * ((sumdiff q * u : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall hpointc)]
    rw [integral_finsetSum Q hF]
    exact Finset.sum_congr rfl (fun q _ => fejerK_transform (sumdiff q))
  have hreal : ((∫ u : ℝ, fejerK u * ‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ∫ u : ℝ, ((fejerK u : ℝ) : ℂ) * ((‖expSum W u‖ ^ 4 : ℝ) : ℂ) := by
    have h1 := Complex.ofRealCLM.integral_comp_comm (integrable_fejerK_mul_pow4 W)
    simp only [Complex.ofRealCLM_apply] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
  have hfn : ((∫ u : ℝ, fejerK u * ‖expSum W u‖ ^ 4 : ℝ) : ℂ)
      = ((∑ q ∈ Q, Commons.Analysis.Fourier.tri (sumdiff q) : ℝ) : ℂ) := by
    rw [hreal, hmain]
    exact (Complex.ofReal_sum Q (fun q => Commons.Analysis.Fourier.tri (sumdiff q))).symm
  exact Complex.ofReal_inj.mp (by rw [hfn, hQ])

/-- The fourth moment of `R` over `v ∈ [1,2]` is `≪ E(W)` (used in GM Lemma 11.8): this is the
standard "`L⁴` of the exponential sum = additive energy" bound, localised to `v ≍ 1`.

Proof: substitute `v = e^u` (`u ∈ [0, log 2]`, `dv = e^u du`), majorise the interval by the Fejér
kernel `fejerK u = (2π)⁻¹ sinc(u/2)²`, which is nonnegative and `≥ 1/(4π)` on `[0, log 2]` while
its Fourier transform is the triangle function `tri` supported in `[-1,1]`.  Expanding
`‖Σ_{t∈W} e^{itu}‖⁴ = Σ_{q ∈ W⁴} e^{i q_s u}` and integrating termwise gives
`∫ fejerK u ‖Σ‖⁴ du = Σ_{q ∈ W⁴} tri(q_s) ≤ #{q : |q_s| ≤ 1} = E(W)`. -/
theorem Rfun_integral_pow4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℝ) (T : ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4) ≤ C * (Submission.GM.energy W : ℝ) := by
  refine ⟨8 * Real.pi, by positivity, ?_⟩
  intro W T _ _
  have ha0 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcont : Continuous (fun u : ℝ => ‖expSum W u‖ ^ 4) :=
    (continuous_expSum W).norm.pow 4
  have hgt : Continuous (fun u : ℝ => fejerK u * ‖expSum W u‖ ^ 4) :=
    fejerK_continuous.mul hcont
  calc (∫ v in (1:ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4)
      = ∫ u in (0:ℝ)..Real.log 2, ‖expSum W u‖ ^ 4 * Real.exp u := integral_Rfun_eq W
    _ ≤ ∫ u in (0:ℝ)..Real.log 2, ‖expSum W u‖ ^ 4 * 2 := by
        refine intervalIntegral.integral_mono_on ha0
          ((hcont.mul Real.continuous_exp).intervalIntegrable _ _)
          ((hcont.mul continuous_const).intervalIntegrable _ _) ?_
        intro u hu
        have hue : Real.exp u ≤ 2 := by
          have h := Real.exp_le_exp.mpr hu.2
          rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
        have hnn : 0 ≤ ‖expSum W u‖ ^ 4 := by positivity
        nlinarith [hue, hnn]
    _ ≤ ∫ u in (0:ℝ)..Real.log 2, 8 * Real.pi * (fejerK u * ‖expSum W u‖ ^ 4) := by
        refine intervalIntegral.integral_mono_on ha0
          ((hcont.mul continuous_const).intervalIntegrable _ _)
          ((continuous_const.mul hgt).intervalIntegrable _ _) ?_
        intro u hu
        have hlow : (4 * Real.pi)⁻¹ ≤ fejerK u := fejerK_lower ⟨hu.1, hu.2⟩
        have hnn : 0 ≤ ‖expSum W u‖ ^ 4 := by positivity
        have h4 : (0:ℝ) < 4 * Real.pi := by positivity
        have h1 : (1:ℝ) ≤ 4 * Real.pi * fejerK u := by
          rw [mul_comm]
          exact (inv_le_iff_one_le_mul₀ h4).mp hlow
        have h2 : (2:ℝ) ≤ 8 * Real.pi * fejerK u := by nlinarith [h1, h4]
        calc ‖expSum W u‖ ^ 4 * 2 ≤ ‖expSum W u‖ ^ 4 * (8 * Real.pi * fejerK u) :=
              mul_le_mul_of_nonneg_left h2 hnn
          _ = 8 * Real.pi * (fejerK u * ‖expSum W u‖ ^ 4) := by ring
    _ = 8 * Real.pi * ∫ u in (0:ℝ)..Real.log 2, fejerK u * ‖expSum W u‖ ^ 4 := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ 8 * Real.pi * ∫ u : ℝ, fejerK u * ‖expSum W u‖ ^ 4 := by
        have hmono : (∫ u in (0:ℝ)..Real.log 2, fejerK u * ‖expSum W u‖ ^ 4)
            ≤ ∫ u : ℝ, fejerK u * ‖expSum W u‖ ^ 4 := by
          rw [intervalIntegral.integral_of_le ha0]
          refine MeasureTheory.setIntegral_le_integral (integrable_fejerK_mul_pow4 W) ?_
          filter_upwards with u
          exact mul_nonneg (fejerK_nonneg u) (by positivity)
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 8 * Real.pi * (∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W : Finset (ℝ × ℝ × ℝ × ℝ)),
          Commons.Analysis.Fourier.tri (sumdiff q)) := by
        rw [integral_fejerK_expSum_pow4 W]
    _ ≤ 8 * Real.pi * (Submission.GM.energy W : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_tri_sumdiff_le_energy W) (by positivity)

end Work.GM.Energy.RMoments
