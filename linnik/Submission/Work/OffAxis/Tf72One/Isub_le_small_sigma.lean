import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.G72SmallS
import Submission.Work.OffAxis.Tf72One.exp_bounds

noncomputable section

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-! ## Pieces of the proof of HB (10.8) for small `σ` -/

/-- `∫₀² y² g72 y dy = 16/45`. -/
private lemma integral_y_sq_g72_aux :
    ∫ y in (0:ℝ)..2, y ^ 2 * g72 y = 16/45 := by
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => (1/30) * ((32/3)*z^3 - 8*z^5 + (10/3)*z^6 - z^8/8))
      (y ^ 2 * g72 y) y := by
    intro y
    have h3 : HasDerivAt (fun z : ℝ => (32/3)*z^3) ((32/3)*(3*y^2)) y := by
      simpa using (hasDerivAt_pow 3 y).const_mul ((32:ℝ)/3)
    have h5 : HasDerivAt (fun z : ℝ => 8*z^5) (8*(5*y^4)) y := by
      simpa using (hasDerivAt_pow 5 y).const_mul (8:ℝ)
    have h6 : HasDerivAt (fun z : ℝ => (10/3)*z^6) ((10/3)*(6*y^5)) y := by
      simpa using (hasDerivAt_pow 6 y).const_mul ((10:ℝ)/3)
    have h8 : HasDerivAt (fun z : ℝ => z^8/8) (8*y^7/8) y := (hasDerivAt_pow 8 y).div_const 8
    have hsum := (((h3.sub h5).add h6).sub h8).const_mul ((1:ℝ)/30)
    refine hsum.congr_deriv ?_
    simp only [g72]
    ring
  have hint : IntervalIntegrable (fun y : ℝ => y ^ 2 * g72 y) MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  norm_num

/-- The half-angle identity `cos x = 1 - 2 sin²(x/2)`. -/
private lemma cos_eq_one_sub_two_sin_sq (x : ℝ) :
    Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.sin_sq_eq_half_sub (x / 2)
  have h2 : 2 * (x / 2) = x := by ring
  rw [h2] at h
  linarith

/-- **Decomposition of `Isub` in the `σ` variable.**  With `cos(σy) = 1 - 2 sin²(σy/2)`,
`Isub s σ = Isub s 0 + 2∫₀² (2 - e^{sy}) sin²(σy/2) g72 y dy`. -/
private lemma Isub_cos_decomp_aux (s σ : ℝ) :
    Isub s σ = Isub s 0
      + 2 * ∫ y in (0:ℝ)..2, (2 - Real.exp (s * y)) * Real.sin (σ * y / 2) ^ 2 * g72 y := by
  have hI1 : IntervalIntegrable
      (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hI2 : IntervalIntegrable
      (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hI3 : IntervalIntegrable
      (fun y : ℝ => (-2) * ((Real.exp (s*y) - 2) * Real.sin (σ*y/2)^2 * g72 y))
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hkey : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y)
      = (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y)
        + 2 * ∫ y in (0:ℝ)..2, (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y := by
    have hF : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y)
        = (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y)
          + ∫ y in (0:ℝ)..2, (-2) * ((Real.exp (s*y) - 2) * Real.sin (σ*y/2)^2 * g72 y) := by
      rw [← intervalIntegral.integral_add hI2 hI3]
      apply intervalIntegral.integral_congr
      intro y _
      show (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y
          = (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y
            + -2 * ((Real.exp (s*y) - 2) * Real.sin (σ*y/2)^2 * g72 y)
      rw [cos_eq_one_sub_two_sin_sq (σ*y)]
      simp only [zero_mul, Real.cos_zero]
      ring
    have hH : (∫ y in (0:ℝ)..2,
          (-2) * ((Real.exp (s*y) - 2) * Real.sin (σ*y/2)^2 * g72 y))
        = 2 * ∫ y in (0:ℝ)..2, (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y := by
      rw [intervalIntegral.integral_const_mul]
      have heq : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.sin (σ*y/2)^2 * g72 y)
          = - ∫ y in (0:ℝ)..2, (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro y _
        ring
      rw [heq]; ring
    rw [hF, hH]
  rw [Isub_eq_integral s σ, Isub_eq_integral s 0]
  exact hkey

/-- **The second term is at most `1/10`.**  On `[0,2]` one has `2 - e^{sy} ≤ 1` and
`sin²(σy/2) ≤ (σy/2)²`, so the integrand is at most `(σ²/4)y²g72`; integrating gives
`2∫ ≤ (σ²/2)(16/45) ≤ (9/32)(16/45) = 1/10`. -/
private lemma Isub_sigma_term_le_aux (s σ : ℝ) (hs : 0 ≤ s) (hσ : |σ| ≤ 3/4) :
    2 * ∫ y in (0:ℝ)..2, (2 - Real.exp (s * y)) * Real.sin (σ * y / 2) ^ 2 * g72 y ≤ 1/10 := by
  have hI1 : IntervalIntegrable
      (fun y : ℝ => (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hI2 : IntervalIntegrable
      (fun y : ℝ => (σ^2/4) * (y^2 * g72 y)) MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y ≤ (σ^2/4) * (y^2 * g72 y) := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hg : 0 ≤ g72 y := g72_nonneg hy0 hy.2
    have hsiny : 0 ≤ Real.sin (σ*y/2)^2 := sq_nonneg _
    have htwo : 2 - Real.exp (s*y) ≤ 1 := by
      have h1 : 1 ≤ Real.exp (s*y) := Real.one_le_exp (mul_nonneg hs hy0)
      linarith
    have hstep : (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 ≤ (σ*y/2)^2 := by
      calc (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2
          ≤ 1 * Real.sin (σ*y/2)^2 := mul_le_mul_of_nonneg_right htwo hsiny
        _ = Real.sin (σ*y/2)^2 := one_mul _
        _ ≤ (σ*y/2)^2 := Real.sin_sq_le_sq
    calc (2 - Real.exp (s*y)) * Real.sin (σ*y/2)^2 * g72 y
        ≤ (σ*y/2)^2 * g72 y := mul_le_mul_of_nonneg_right hstep hg
      _ = (σ^2/4) * (y^2 * g72 y) := by ring
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hI1 hI2 hpt
  have hval : (∫ y in (0:ℝ)..2, (σ^2/4) * (y^2 * g72 y)) = (σ^2/4) * (16/45) := by
    rw [intervalIntegral.integral_const_mul, integral_y_sq_g72_aux]
  have hσ2 : σ^2 ≤ 9/16 := by
    have h := abs_le.mp hσ
    nlinarith
  have hfin : 2 * ((σ^2/4) * (16/45)) ≤ 1/10 := by nlinarith [hσ2]
  linarith [hmono, hval, hfin]

/-- **Monotonicity of `s ↦ Isub s 0`.** -/
private lemma Isub_zero_le_of_le_aux (s t : ℝ) (_hs : 0 ≤ s) (hst : s ≤ t) :
    Isub s 0 ≤ Isub t 0 := by
  have hI1 : IntervalIntegrable
      (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hI2 : IntervalIntegrable
      (fun y : ℝ => (Real.exp (t*y) - 2) * Real.cos (0*y) * g72 y)
      MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [g72]
    fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (0*y) * g72 y
        ≤ (Real.exp (t*y) - 2) * Real.cos (0*y) * g72 y := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hg : 0 ≤ g72 y := g72_nonneg hy0 hy.2
    have hcos : Real.cos (0*y) = 1 := by simp
    have he : Real.exp (s*y) ≤ Real.exp (t*y) := Real.exp_le_exp.mpr (by nlinarith)
    rw [hcos]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hg
  rw [Isub_eq_integral s 0, Isub_eq_integral t 0]
  exact intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hI1 hI2 hpt

/-- **The value at `s = 17/16`, `σ = 0`.**  From the closed form `G72_real_closed` and
`Real.exp (17/8) ≤ 83729/10000`. -/
private lemma Isub_at_17_16_zero_le_aux : Isub (17/16) 0 ≤ -109/1000 := by
  have hI : Isub (17/16) 0 = (G72 (-((17/16 : ℝ) : ℂ))).re - 2 * (G72 (0 : ℂ)).re := by
    simp only [Isub]
    push_cast
    simp
  have h1 : (G72 (-((17/16 : ℝ) : ℂ))).re
      = (1/30)*(-32/(17/16) + 80/(17/16)^3 + 120/(17/16)^4 - 120/(17/16)^6)
        + Real.exp (17/8) * (4*(1-17/16)^2/(17/16)^6) := by
    rw [G72_real_closed (17/16) (by norm_num)]
    norm_num
  have h2 : (G72 (0 : ℂ)).re = 8/9 := by
    rw [G72_re_eq_integral]
    have h3 : (∫ y in (0:ℝ)..2,
          Real.exp (-((0:ℂ).re * y)) * Real.cos ((0:ℂ).im * y) * g72 y)
        = ∫ y in (0:ℝ)..2, g72 y := by
      apply intervalIntegral.integral_congr
      intro y _
      simp
    rw [h3, integral_g72]
  rw [hI, h1, h2]
  have h17 : Real.exp (17/8) ≤ (83729/10000 : ℝ) := by
    obtain ⟨_,_,_,_,_,_,_,_,h⟩ := exp_bounds
    exact h
  have hcoef : (0:ℝ) ≤ 4*(1-17/16)^2/(17/16)^6 := by norm_num
  have hmul : (4*(1-17/16)^2/(17/16)^6) * Real.exp (17/8)
      ≤ (4*(1-17/16)^2/(17/16)^6) * (83729/10000) :=
    mul_le_mul_of_nonneg_left h17 hcoef
  have hmain : (1/30 : ℝ)*(-32/(17/16 : ℝ) + 80/(17/16 : ℝ)^3 + 120/(17/16 : ℝ)^4
        - 120/(17/16 : ℝ)^6)
      + (83729/10000 : ℝ) * (4*(1-17/16 : ℝ)^2/(17/16 : ℝ)^6) - 2 * (8/9 : ℝ)
        ≤ (-109/1000 : ℝ) := by norm_num
  nlinarith [hmul, hmain]

/-- **HB (10.8) for small `σ`.**  For `|σ| ≤ 3/4` one has `Isub s σ ≤ 1/100`.  Proof route:
`cos(σy) = 1 - 2 sin²(σy/2)` gives the identity
`Isub s σ = Isub s 0 + 2∫₀² (2-e^{sy})sin²(σy/2) g72 y dy`, and since `(2-e^{sy})_+ ≤ 1` on `[0,2]`
and `sin² x ≤ x²`, the second term is at most `(σ²/2)·∫₀²y²g72 = (σ²/2)(16/45)`.  Finally
`Isub s 0 = ∫₀²(e^{sy}-2)g72 ≤ Isub (17/16) 0 ≤ -109/1000` (monotonicity in `s`, then the closed form
`G72_real_closed` at `b = 17/16` together with `Real.exp (17/8) ≤ 83729/10000`), and
`-109/1000 + (9/32)(16/45) = -0.009 < 1/100`. -/
theorem Isub_le_small_sigma (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) (hσ : |σ| ≤ 3/4) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ 1/100 := by
  rw [Isub_cos_decomp_aux s σ]
  have h1 : Isub s 0 ≤ -109/1000 :=
    (Isub_zero_le_of_le_aux s (17/16) hs0 hs1).trans Isub_at_17_16_zero_le_aux
  have h2 := Isub_sigma_term_le_aux s σ hs0 hσ
  linarith

end Work.OffAxis.Tf72One
