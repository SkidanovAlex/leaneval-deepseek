import Mathlib.MeasureTheory.Function.L2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- Cauchy–Schwarz for the Bochner integral, unweighted and with no finiteness or boundedness
assumption on the measure: if `f²` and `g²` are integrable and `f`, `g` are a.e. strongly
measurable then `(∫ f·g)² ≤ (∫ f²)·(∫ g²)`.

Proof: `|f|` and `|g|` lie in `L²` (their squares are `f²`, `g²`), so Hölder with conjugate
exponents `2, 2` gives `∫ |f|·|g| ≤ √(∫ f²) · √(∫ g²)`; squaring and using
`|∫ f·g| ≤ ∫ |f|·|g|` yields the claim. -/
theorem csIntegralSqLe {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hfi : MeasureTheory.Integrable (fun x => f x ^ 2) μ)
    (hgi : MeasureTheory.Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hmf : AEStronglyMeasurable (fun x => |f x|) μ := hf.norm
  have hmg : AEStronglyMeasurable (fun x => |g x|) μ := hg.norm
  have hmemf : MemLp (fun x => |f x|) (2 : ENNReal) μ := by
    rw [memLp_two_iff_integrable_sq hmf]
    exact hfi.congr (ae_of_all _ fun x => (sq_abs (f x)).symm)
  have hmemg : MemLp (fun x => |g x|) (2 : ENNReal) μ := by
    rw [memLp_two_iff_integrable_sq hmg]
    exact hgi.congr (ae_of_all _ fun x => (sq_abs (g x)).symm)
  have hmemf' : MemLp (fun x => |f x|) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hmemf
  have hmemg' : MemLp (fun x => |g x|) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hmemg
  have hmain : ∫ x, |f x| * |g x| ∂μ
      ≤ (∫ x, |f x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        * (∫ x, |g x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
      Real.HolderConjugate.two_two (ae_of_all _ (fun _ => abs_nonneg _))
      (ae_of_all _ (fun _ => abs_nonneg _)) hmemf' hmemg'
  have hsqf : (∫ x, |f x| ^ (2 : ℝ) ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two, sq_abs]
  have hsqg : (∫ x, |g x| ^ (2 : ℝ) ∂μ) = ∫ x, g x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two, sq_abs]
  rw [hsqf, hsqg] at hmain
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hmain' : ∫ x, |f x| * |g x| ∂μ
      ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hmain
    exact hmain
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
    calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |f x| * |g x| ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul]
  have h0 : 0 ≤ ∫ x, |f x| * |g x| ∂μ :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hstep : (∫ x, |f x| * |g x| ∂μ) ^ 2
      ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
    have h1 : (∫ x, |f x| * |g x| ∂μ) ^ 2
        ≤ (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ h0 hmain' 2
    rwa [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB] at h1
  calc (∫ x, f x * g x ∂μ) ^ 2
      = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := hstep

end Work.BoseFixB1S
