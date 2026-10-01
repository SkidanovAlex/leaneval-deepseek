import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The integral bound `∫ (log (2+|t|) + 1) / (1 + t²) ≤ 40`

We bound the integrand pointwise by `8 / ((1+|t|) √(1+|t|)) = 8 (1+|t|)^{-3/2}`
and evaluate the resulting integral explicitly.

The elementary pointwise estimate is

`log (2+s) + 1 ≤ 4 √(1+s)   (s ≥ 0)`,

obtained from `log x ≤ 2 √x` (`Real.log_le_rpow_div` with `ε = 1/2`).
-/

noncomputable section

open MeasureTheory Filter Real
open scoped Topology

namespace Commons.Analysis.Integral

/-- Pointwise logarithmic estimate: `log (2 + s) + 1 ≤ 4 √(1 + s)` for `s ≥ 0`. -/
private lemma log_two_add_one_le {s : ℝ} (hs : 0 ≤ s) :
    Real.log (2 + s) + 1 ≤ 4 * Real.sqrt (1 + s) := by
  have h2s : 0 < 2 + s := by linarith
  have h1 : Real.log (2 + s) ≤ (2 + s) ^ ((1:ℝ)/2) / ((1:ℝ)/2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2 : (2 + s) ^ ((1:ℝ)/2) / ((1:ℝ)/2) = 2 * Real.sqrt (2 + s) := by
    rw [Real.sqrt_eq_rpow]; ring
  rw [h2] at h1
  have hsq : Real.sqrt (2 + s) ≤ Real.sqrt 2 * Real.sqrt (1 + s) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have h3 : (2:ℝ) * Real.sqrt 2 ≤ 3 := by
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 1)]
  have hsqrt1s : (1:ℝ) ≤ Real.sqrt (1 + s) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hs1nn : 0 ≤ Real.sqrt (1 + s) := Real.sqrt_nonneg _
  calc Real.log (2 + s) + 1 ≤ 2 * Real.sqrt (2 + s) + 1 := by linarith
    _ ≤ 2 * (Real.sqrt 2 * Real.sqrt (1 + s)) + 1 := by nlinarith [hsq]
    _ = (2 * Real.sqrt 2) * Real.sqrt (1 + s) + 1 := by ring
    _ ≤ 3 * Real.sqrt (1 + s) + 1 := by nlinarith [h3, hs1nn]
    _ ≤ 4 * Real.sqrt (1 + s) := by linarith

/-- `u * √u = u ^ (3/2)` for `u > 0`. -/
private lemma mul_sqrt_eq_rpow (u : ℝ) (hu : 0 < u) : u * Real.sqrt u = u ^ ((3:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hu 1 (1/2),
    Real.rpow_one]

/-- `(u √u)^{-1} = u ^ (-3/2)` for `u > 0`. -/
private lemma inv_mul_sqrt_eq_rpow (u : ℝ) (hu : 0 < u) :
    (u * Real.sqrt u)⁻¹ = u ^ (-((3:ℝ)/2)) := by
  rw [mul_sqrt_eq_rpow u hu, Real.rpow_neg hu.le (3/2)]

/-- Pointwise domination of the integrand. -/
private lemma integrand_le (t : ℝ) :
    (Real.log (2 + |t|) + 1) / (1 + t ^ 2) ≤ 8 * (1 + |t|) ^ (-((3:ℝ)/2)) := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hlog := log_two_add_one_le ht
  have hden : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hu : (0:ℝ) < 1 + |t| := by positivity
  have hkey : 4 * Real.sqrt (1 + |t|) / (1 + t ^ 2) ≤
      8 / ((1 + |t|) * Real.sqrt (1 + |t|)) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hsu : Real.sqrt (1 + |t|) ^ 2 = 1 + |t| := Real.sq_sqrt hu.le
    have habs : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [sq_nonneg (|t| - 1), hsu, Real.sqrt_nonneg (1 + |t|), habs]
  calc (Real.log (2 + |t|) + 1) / (1 + t ^ 2)
      ≤ 4 * Real.sqrt (1 + |t|) / (1 + t ^ 2) :=
        div_le_div_of_nonneg_right hlog hden.le
    _ ≤ 8 / ((1 + |t|) * Real.sqrt (1 + |t|)) := hkey
    _ = 8 * (1 + |t|) ^ (-((3:ℝ)/2)) := by
          rw [div_eq_mul_inv, inv_mul_sqrt_eq_rpow (1 + |t|) hu]

/-- The helper integral `∫_0^∞ (1+x)^{-3/2} dx = 2`. -/
private lemma integral_one_add_rpow_Ioi :
    (∫ x in Set.Ioi (0:ℝ), (1 + x) ^ (-((3:ℝ)/2))) = 2 := by
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun x : ℝ => -2 * (1 + x) ^ (-((1:ℝ)/2))) ((1 + x) ^ (-((3:ℝ)/2))) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx
    have hpos : (0:ℝ) < 1 + x := by linarith
    have hbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hrp : HasDerivAt (fun y : ℝ => (1 + y) ^ (-((1:ℝ)/2)))
        (1 * (-((1:ℝ)/2)) * (1 + x) ^ (-((1:ℝ)/2) - 1)) x :=
      hbase.rpow_const (Or.inl hpos.ne')
    have h3 : HasDerivAt (fun y : ℝ => -2 * (1 + y) ^ (-((1:ℝ)/2)))
        (-2 * (1 * (-((1:ℝ)/2)) * (1 + x) ^ (-((1:ℝ)/2) - 1))) x :=
      hrp.const_mul (-2)
    convert h3 using 1
    rw [show -((1:ℝ)/2) - 1 = -((3:ℝ)/2) by norm_num]
    ring
  have hint : IntegrableOn (fun x : ℝ => (1 + x) ^ (-((3:ℝ)/2))) (Set.Ioi (0:ℝ)) volume := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := -((3:ℝ)/2)) (c := (0:ℝ)) (m := (1:ℝ))
      (by norm_num) (by norm_num)
    simpa [add_comm] using h
  have hlim : Tendsto (fun x : ℝ => -2 * (1 + x) ^ (-((1:ℝ)/2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (1 + x) ^ (-((1:ℝ)/2))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < (1:ℝ)/2)).comp
        (Filter.tendsto_atTop_add_const_right _ (1:ℝ) tendsto_id)
      simpa [Function.comp_def, add_comm] using h
    simpa using h1.const_mul (-2)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hval]
  norm_num

/-- The dominating function `t ↦ 8 (1+|t|)^{-3/2}` is integrable. -/
private lemma integrable_dom :
    Integrable (fun t : ℝ => 8 * (1 + |t|) ^ (-((3:ℝ)/2))) volume := by
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (-((3:ℝ)/2))) volume := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3:ℝ)/2)
      (by rw [Module.finrank_self]; norm_num)
    simpa [Real.norm_eq_abs] using h
  simpa using hbase.const_mul 8

/-- Evaluation of the dominating integral. -/
private lemma integral_dom :
    (∫ t : ℝ, 8 * (1 + |t|) ^ (-((3:ℝ)/2))) = 32 := by
  rw [MeasureTheory.integral_const_mul]
  have hB : (∫ t : ℝ, (1 + |t|) ^ (-((3:ℝ)/2))) =
      2 * ∫ x in Set.Ioi (0:ℝ), (1 + x) ^ (-((3:ℝ)/2)) :=
    integral_comp_abs (f := fun x : ℝ => (1 + x) ^ (-((3:ℝ)/2)))
  rw [hB, integral_one_add_rpow_Ioi]
  norm_num

theorem integral_log_weight_le :
    (∫ t : ℝ, (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) ≤ 40 := by
  have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) :=
    Filter.Eventually.of_forall fun t => by
      have h1 : (0:ℝ) ≤ Real.log (2 + |t|) := Real.log_nonneg (by nlinarith [abs_nonneg t])
      have h2 : (0:ℝ) < 1 + t ^ 2 := by positivity
      exact div_nonneg (by linarith) h2.le
  have hle := MeasureTheory.integral_mono_of_nonneg hnn integrable_dom
    (Filter.Eventually.of_forall integrand_le)
  rw [integral_dom] at hle
  linarith

end Commons.Analysis.Integral