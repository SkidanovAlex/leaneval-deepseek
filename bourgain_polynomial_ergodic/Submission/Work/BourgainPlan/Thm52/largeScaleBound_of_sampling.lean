import Mathlib
import Submission.Work.BourgainPlan.Thm52.Finsupp
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation

open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Thm52

noncomputable section

/-- For a complex number, `‖z‖ₑ = ofReal ‖z‖`. -/
private lemma enorm_complex_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by simp

/-- For a finitely supported complex sequence, the `p`-th power of the `ℓᵖ` norm is the sum over
the support of `‖a j‖^p` (for `p > 0`; the identity fails at `p ≤ 0`, where `0^p ≠ 0`). -/
theorem lpPow_finsupp_eq_sum {p : ℝ} (hp : 0 < p) (f : ℤ →₀ ℂ) :
    lpPow p (⇑f) = ∑ j ∈ f.support, ENNReal.ofReal ‖(⇑f) j‖ ^ p := by
  rw [lpPow, MeasureTheory.lintegral_count,
    tsum_eq_sum (s := f.support) (fun b hb => ?_)]
  · exact Finset.sum_congr rfl fun j _ => by rw [enorm_complex_eq_ofReal_norm']
  · have h0 : f b = 0 := by
      by_contra h
      exact hb (Finsupp.mem_support_iff.mpr h)
    rw [h0, enorm_complex_eq_ofReal_norm', norm_zero, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos hp]

/-- **From a bound on `∫⁻ ‖F‖^p` to a bound on the `eLpNorm`.**  If `∫⁻ F^p ≤ ofReal (B^p) · lpPow`
with `B ≥ 0`, then `eLpNorm F (ofReal p) ≤ ofReal B · lpNorm`, by taking `(·)^(1/p)` and using
`x^(p·(1/p)) = x`. -/
theorem eLpNorm_le_of_lpPow_le {p : ℝ} (hp : 0 < p) {F : ℤ → ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    {g : ℤ → ℂ}
    (h : ∫⁻ y : ℤ, F y ^ p ∂Measure.count ≤ ENNReal.ofReal (B ^ p) * lpPow p g) :
    eLpNorm F (ENNReal.ofReal p) Measure.count ≤ ENNReal.ofReal B * lpNorm p g := by
  have hg : lpNorm p g = (lpPow p g) ^ (1 / p) := by
    rw [lpNorm, lpPow, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete]
    rw [ENNReal.toReal_ofReal hp.le]
  rw [eLpNorm_ennreal_eq p hp F, hg]
  refine (ENNReal.rpow_le_rpow h (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_rpow_of_nonneg hB hp.le, ← ENNReal.rpow_mul,
    show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]

-- This is a packaging corollary of
-- `Work.BourgainPlan.IonescuWainger.sampling_principle_variation`
-- (`Submission/Work/BourgainPlan/IonescuWainger/sampling_principle_variation.lean`), which gives
-- `∫⁻_k (V²_{n≥κ}(Σ_{j∈s} (∫_{-1/2}^{1/2} m_n ξ e^{2πi(k-j)ξ} dξ) a_j))^p d# ≤ ofReal ((C·A)^p) Σ_{j∈s} ofReal ‖a_j‖^p`
-- for `a` supported in `s`; the conversion is `MeasureTheory.lintegral_count` +
-- `tsum_eq_sum` on the right and the definition of `eLpNorm` (`(eLpNorm z q) ^ q = ∫⁻ ‖z‖ₑ ^ q`,
-- `ENNReal.mul_rpow_of_nonneg`, `ENNReal.ofReal_rpow_of_nonneg`) with `q = ofReal p` on the left.
theorem largeScaleBound_of_sampling {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℕ) (m : ℕ → ℝ → ℂ) (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n ξ * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume),
      Work.BourgainPlan.Thm52.LargeScaleBoundF p
        (fun n (f : ℤ →₀ ℂ) (y : ℤ) => ∑ j ∈ f.support,
          (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
            Complex.exp (2 * Real.pi * Complex.I * ((y - j : ℤ) : ℂ) * (ξ : ℂ))) * f j)
        κ (C * A) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.BourgainPlan.IonescuWainger.sampling_principle_variation (p := p) hp
  refine ⟨C₀, hC₀pos, ?_⟩
  intro κ m hm hsupp A hA hOp f
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  have hA0 : (0:ℝ) ≤ C₀ * A := mul_nonneg hC₀pos.le hA
  have ha0 : ∀ k, k ∉ f.support → (⇑f : ℤ → ℂ) k = 0 := by
    intro k hk
    by_contra h
    exact hk (Finsupp.mem_support_iff.mpr h)
  -- the sampling principle, applied with `s = f.support` and `a = ⇑f`
  have hS := hC₀ κ m hm hsupp A hA hOp f.support (⇑f) ha0
  -- convert its right-hand side `Σ_{j∈s} ofReal ‖f j‖^p` into `lpPow p ⇑f`
  have hpow : ∫⁻ y : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
      (fun n => ∑ j ∈ f.support, (∫ ξ in (-(1/2):ℝ)..(1/2), m n ξ *
        Complex.exp (2 * Real.pi * Complex.I * ((y - j : ℤ) : ℂ) * (ξ : ℂ))) * (⇑f) j)) ^ p
      ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C₀ * A) ^ p) * lpPow p (⇑f) := by
    rw [lpPow_finsupp_eq_sum hp0 f]
    exact hS
  -- and take the `(1/p)`-th power of both sides
  exact eLpNorm_le_of_lpPow_le hp0 hA0 hpow

end

end Work.BourgainPlan.Thm52
