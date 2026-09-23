import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory
open scoped Interval

namespace Commons.MeasureTheory.IntervalIntegral

/-- Cauchy–Schwarz (equivalently, Hölder with exponents `2, 2`) for the interval integral:
the square of the integral of `f` over `[a, b]` is at most the length of the interval times the
integral of `f ^ 2`.  This is the classical inequality
`(∫ f)² ≤ (b - a) ∫ f²`, obtained by applying Cauchy–Schwarz in `L²([a,b])` to the constant
function `1` and `f`. -/
theorem sq_integral_le_mul_integral_sq {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hf2 : IntervalIntegrable (fun t : ℝ => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  -- Reduce the interval integrals over `a..b` to set integrals over `Set.Ioc a b`.
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  -- `IntervalIntegrable f volume a b` is a conjunction, whose first component is exactly
  -- `Integrable f μ`.
  have hf_int : Integrable f μ := hf.1
  have hf2_int : Integrable (fun t : ℝ => f t ^ 2) μ := hf2.1
  -- The total mass of `μ` is `b - a`.
  have h_one : (∫ t, (1:ℝ) ∂μ) = b - a := by
    rw [hμ, ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
    simp
  -- `f` is in `L²(μ)`.
  have hmemf : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq hf_int.aestronglyMeasurable]
    exact hf2_int
  have hmem_abs : MemLp (fun t => |f t|) 2 μ := by
    simpa [Real.norm_eq_abs] using hmemf.norm
  have hmem1 : MemLp (fun _ : ℝ => (1:ℝ)) 2 μ := memLp_const 1
  -- Cauchy–Schwarz / Hölder with `p = q = 2` for the functions `|f|` and `1`.
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (by simpa using hmem_abs) (by simpa using hmem1)
  have e1 : (∫ t, |f t| * 1 ∂μ) = ∫ t, |f t| ∂μ := by simp
  have e2 : (∫ t, |f t| ^ (2:ℝ) ∂μ) = ∫ t, f t ^ 2 ∂μ := by
    congr 1 with t
    simp [sq_abs]
  have e3 : (∫ t, (1:ℝ) ^ (2:ℝ) ∂μ) = b - a := by
    have h1 : (1:ℝ) ^ (2:ℝ) = 1 := by norm_num
    rw [h1, h_one]
  rw [e1, e2, e3] at hcs
  -- Now `hcs : ∫ |f| ≤ (∫ f²)^(1/2) * (b - a)^(1/2)`, and we square it.
  have h_abs : |∫ t, f t ∂μ| ≤ ∫ t, |f t| ∂μ := abs_integral_le_integral_abs
  have h_nonneg_abs : 0 ≤ ∫ t, |f t| ∂μ := integral_nonneg (fun t => abs_nonneg _)
  have h_int_sq_nonneg : 0 ≤ ∫ t, f t ^ 2 ∂μ := integral_nonneg (fun t => sq_nonneg _)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  calc (∫ t, f t ∂μ) ^ 2
      = |∫ t, f t ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ t, |f t| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
    _ ≤ ((∫ t, f t ^ 2 ∂μ) ^ ((1:ℝ)/2) * (b - a) ^ ((1:ℝ)/2)) ^ 2 :=
          pow_le_pow_left₀ h_nonneg_abs hcs 2
    _ = (b - a) * ∫ t, f t ^ 2 ∂μ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt h_int_sq_nonneg,
            Real.sq_sqrt hba]
        ring

end Commons.MeasureTheory.IntervalIntegral