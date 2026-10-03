import Mathlib
import Submission.Work.FIArea7.FourierDefs

namespace Work.FIArea7

open MeasureTheory intervalIntegral Real Complex Filter
open scoped Topology FourierTransform

noncomputable section

/-!
# Bounds for the cosine transform `cRho` of the flat-topped density

`cRho s = ∫ u, cos (2πus) · ρ(u)` with `ρ = sepRho` the smooth flat-topped density of
`SepBump`, `∫ ρ = 1`, `∫ |ρ'| = 16/15`.  We prove

* `|cRho s| ≤ 1` (trivial, from `|cos| ≤ 1` and `∫ρ = 1`), and
* `|cRho s| ≤ 8/(15·π·|s|)` for `s ≠ 0`, which is the integration-by-parts estimate
  `cRho s = -(1/(2πs)) ∫ u, sin(2πus)·ρ'(u)`, together with `∫|ρ'| ≤ 16/15`.

The boundary terms in the integration by parts vanish because `ρ` is supported in `[-1,1]`.
-/

/-! ## Integrability of the ingredients -/

lemma integrable_sepRho : Integrable sepRho := by
  simpa using integrable_sepRho_comp 0 1 (by norm_num : (0 : ℝ) < 1)

lemma integrable_deriv_sepRho : Integrable (deriv sepRho) := by
  apply Continuous.integrable_of_hasCompactSupport continuous_deriv_sepRho
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · exact deriv_sepRho_eq_zero_of_le (le_of_lt h)
  · exact deriv_sepRho_eq_zero_of_one_le (le_of_lt h)

lemma integrable_cos_mul_sepRho (s : ℝ) :
    Integrable (fun u : ℝ => Real.cos (2 * Real.pi * u * s) * sepRho u) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_cos.comp (by fun_prop)).mul sepRho_continuous
  · refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [sepRho_eq_zero_of_le (le_of_lt h), mul_zero]
    · rw [sepRho_eq_zero_of_one_le (le_of_lt h), mul_zero]

lemma integrable_sin_mul_deriv_sepRho (s : ℝ) :
    Integrable (fun u : ℝ => Real.sin (2 * Real.pi * u * s) * deriv sepRho u) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_sin.comp (by fun_prop)).mul continuous_deriv_sepRho
  · refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [deriv_sepRho_eq_zero_of_le (le_of_lt h), mul_zero]
    · rw [deriv_sepRho_eq_zero_of_one_le (le_of_lt h), mul_zero]

/-! ## The integration-by-parts identity -/

/-- Integration by parts for the cosine transform: for `s ≠ 0`,
`cRho s = -(1/(2πs)) ∫ u, sin(2πus)·ρ'(u)`. -/
lemma cRho_eq_neg_integral (s : ℝ) (hs : s ≠ 0) :
    cRho s
      = -(1 / (2 * Real.pi * s)) * ∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u := by
  have hzero1 : ∀ x ∉ Set.Ioc (-1 : ℝ) 1, Real.cos (2 * Real.pi * x * s) * sepRho x = 0 := by
    intro x hx
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · rw [sepRho_eq_zero_of_le h, mul_zero]
    · rw [sepRho_eq_zero_of_one_le (le_of_lt h), mul_zero]
  have hzero2 : ∀ x ∉ Set.Ioc (-1 : ℝ) 1,
      Real.sin (2 * Real.pi * x * s) * deriv sepRho x = 0 := by
    intro x hx
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · rw [deriv_sepRho_eq_zero_of_le h, mul_zero]
    · rw [deriv_sepRho_eq_zero_of_one_le (le_of_lt h), mul_zero]
  have hI1 : (∫ x in (-1 : ℝ)..1, Real.cos (2 * Real.pi * x * s) * sepRho x) = cRho s := by
    rw [cRho, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero1]
  have hI2 : (∫ x in (-1 : ℝ)..1, Real.sin (2 * Real.pi * x * s) * deriv sepRho x)
      = ∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  have hcont1 : Continuous
      (fun x : ℝ => 2 * Real.pi * s * (Real.cos (2 * Real.pi * x * s) * sepRho x)) :=
    ((Real.continuous_cos.comp (by fun_prop)).mul sepRho_continuous).const_mul _
  have hcont2 : Continuous (fun x : ℝ => Real.sin (2 * Real.pi * x * s) * deriv sepRho x) :=
    (Real.continuous_sin.comp (by fun_prop)).mul continuous_deriv_sepRho
  have hint1 : IntervalIntegrable
      (fun x : ℝ => 2 * Real.pi * s * (Real.cos (2 * Real.pi * x * s) * sepRho x))
      volume (-1) 1 :=
    hcont1.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun x : ℝ => Real.sin (2 * Real.pi * x * s) * deriv sepRho x) volume (-1) 1 :=
    hcont2.intervalIntegrable _ _
  have hderiv : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.sin (2 * Real.pi * u * s) * sepRho u)
        (2 * Real.pi * s * (Real.cos (2 * Real.pi * x * s) * sepRho x)
          + Real.sin (2 * Real.pi * x * s) * deriv sepRho x) x := by
    intro x _
    have hbase : HasDerivAt (fun u : ℝ => 2 * Real.pi * u * s) (2 * Real.pi * s) x := by
      have h : HasDerivAt (fun u : ℝ => (2 * Real.pi * s) * u) (2 * Real.pi * s) x := by
        simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * s)
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => by ring)
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (2 * Real.pi * u * s))
        (Real.cos (2 * Real.pi * x * s) * (2 * Real.pi * s)) x :=
      (Real.hasDerivAt_sin _).comp x hbase
    have hrho : HasDerivAt sepRho (deriv sepRho x) x :=
      (sepRho_hasDerivAt x).congr_deriv (deriv_sepRho_eq x).symm
    exact (hsin.mul hrho).congr_deriv (by ring)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul] at hmain
  rw [sepRho_eq_zero_of_one_le le_rfl, sepRho_eq_zero_of_le le_rfl, mul_zero, mul_zero,
    sub_zero] at hmain
  rw [hI1, hI2] at hmain
  have hne : (2 * Real.pi * s) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hs
  have h1 : cRho s * (2 * Real.pi * s)
      = -(∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u) := by
    linarith
  rw [show -(1 / (2 * Real.pi * s)) * (∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u)
      = -(∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u) / (2 * Real.pi * s) by ring]
  rw [eq_div_iff hne]
  exact h1

/-! ## The two bounds -/

/-- The trivial bound `|cRho s| ≤ ∫ ρ = 1`. -/
lemma abs_cRho_le_one (s : ℝ) : |cRho s| ≤ 1 := by
  rw [cRho]
  calc |∫ u : ℝ, Real.cos (2 * Real.pi * u * s) * sepRho u|
      ≤ ∫ u : ℝ, |Real.cos (2 * Real.pi * u * s) * sepRho u| := by
        simpa using MeasureTheory.norm_integral_le_integral_norm
          (fun u : ℝ => Real.cos (2 * Real.pi * u * s) * sepRho u)
    _ ≤ ∫ u : ℝ, sepRho u := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with u; exact abs_nonneg _
        · exact integrable_sepRho
        · filter_upwards with u
          rw [abs_mul, abs_of_nonneg (sepRho_nonneg u)]
          nlinarith [Real.abs_cos_le_one (2 * Real.pi * u * s), sepRho_nonneg u]
    _ = 1 := integral_sepRho_univ

/-- The integration-by-parts bound `|cRho s| ≤ 8/(15π|s|)` for `s ≠ 0`. -/
lemma abs_cRho_le_inv (s : ℝ) (hs : s ≠ 0) : |cRho s| ≤ 8 / (15 * Real.pi * |s|) := by
  rw [cRho_eq_neg_integral s hs, abs_mul]
  have h1 : |-(1 / (2 * Real.pi * s))| = 1 / (2 * Real.pi * |s|) := by
    rw [abs_neg, abs_div, abs_one, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have h2 : |∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u| ≤ 16 / 15 := by
    calc |∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u|
        ≤ ∫ u : ℝ, |Real.sin (2 * Real.pi * u * s) * deriv sepRho u| := by
          simpa using MeasureTheory.norm_integral_le_integral_norm
            (fun u : ℝ => Real.sin (2 * Real.pi * u * s) * deriv sepRho u)
      _ ≤ ∫ u : ℝ, |deriv sepRho u| := by
          apply MeasureTheory.integral_mono_of_nonneg
          · filter_upwards with u; exact abs_nonneg _
          · exact integrable_deriv_sepRho.abs
          · filter_upwards with u
            rw [abs_mul]
            nlinarith [Real.abs_sin_le_one (2 * Real.pi * u * s), abs_nonneg (deriv sepRho u)]
      _ ≤ 16 / 15 := integral_abs_deriv_sepRho_le
  rw [h1]
  calc 1 / (2 * Real.pi * |s|) * |∫ u : ℝ, Real.sin (2 * Real.pi * u * s) * deriv sepRho u|
      ≤ 1 / (2 * Real.pi * |s|) * (16 / 15) := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = 8 / (15 * Real.pi * |s|) := by
        field_simp
        ring

/-- The cosine transform `cRho s = ∫ u, cos(2πus)ρ(u)` of the flat-topped density `ρ = sepRho`
(`∫ρ = 1`, `∫|ρ'| = 16/15`) satisfies `|cRho s| ≤ 1` and `|cRho s| ≤ 8/(15π|s|)` for `s ≠ 0`.

For the first bound use `|cos| ≤ 1` and `integral_sepRho_univ`. For the second use integration by
parts (`ρ = sepRho` is `C^∞` and vanishes for `|y| ≥ 1`, so the boundary terms vanish):
`cRho s = -(1/(2πs)) ∫ u, sin(2πus) * deriv sepRho u`, whence
`|cRho s| ≤ (1/(2π|s|)) ∫ |deriv sepRho| ≤ (1/(2π|s|))*(16/15) = 8/(15π|s|)` by
`integral_abs_deriv_sepRho_le`. -/
lemma CRhoBounds (s : ℝ) (hs : s ≠ 0) :
    |cRho s| ≤ min 1 (8 / (15 * Real.pi * |s|)) :=
  le_min (abs_cRho_le_one s) (abs_cRho_le_inv s hs)

end

end Work.FIArea7
