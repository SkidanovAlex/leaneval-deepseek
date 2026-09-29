import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bochner tsum-interchange for interval integrals on `[0,1]` (a.e. any E).
If every `f k : ℝ → E` is interval-integrable on `0..1` and the integrals of
the pointwise norms are summable, then the sum of the integrals equals the
integral of the pointwise sum:

  (∑' k, ∫ x in 0..1, f k x) = ∫ x in 0..1, (∑' k, f k x)

Proof route: reduce both sides to Bochner integrals over the restricted
Lebesgue measure `volume.restrict (Ioc (0:ℝ) 1)` via
`intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)` (the integral
over the empty `Ioc 1 0` vanishes, `simp`), convert `IntegrableOn` to
`Integrable` with `simpa [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), IntegrableOn]`
(simp does not unfold the reducible `IntegrableOn` by itself), and apply
`MeasureTheory.integral_tsum_of_summable_integral_norm`. -/

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval

/-- An integral over `0..1` (interval integral, Lebesgue measure) equals the
Bochner integral of the same function against Lebesgue measure restricted to
`Ioc 0 1`. -/
lemma intervalIntegral_zero_one_eq_integral_restrict {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) :
    (∫ x in (0 : ℝ)..1, g x) = ∫ x, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- Interval integrability on `0..1` is the same as Bochner integrability
against Lebesgue measure restricted to `Ioc 0 1`. -/
lemma integrable_restrict_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : IntervalIntegrable f volume (0 : ℝ) 1) :
    Integrable f (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  exact hf.1

/-- Bochner tsum-interchange for interval integrals on `[0,1]`. -/
theorem integral_tsum_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → ℝ → E}
    (hf : ∀ k : ℕ, IntervalIntegrable (f k) volume (0 : ℝ) 1)
    (hsum : Summable fun k : ℕ => ∫ x in (0 : ℝ)..1, ‖f k x‖) :
    (∑' k : ℕ, ∫ x in (0 : ℝ)..1, f k x) =
      ∫ x in (0 : ℝ)..1, ∑' k : ℕ, f k x := by
  calc
    (∑' k : ℕ, ∫ x in (0 : ℝ)..1, f k x)
        = ∑' k : ℕ, ∫ x, f k x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          refine tsum_congr ?_
          intro k
          exact intervalIntegral_zero_one_eq_integral_restrict (f k)
    _ = ∫ x, (∑' k : ℕ, f k x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          refine MeasureTheory.integral_tsum_of_summable_integral_norm
            (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := f) ?_ ?_
          · intro k
            exact integrable_restrict_of_intervalIntegrable (hf k)
          · have hterm :
                (fun k : ℕ => ∫ x in (0 : ℝ)..1, ‖f k x‖) =
                  fun k : ℕ => ∫ x, ‖f k x‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
              funext k
              exact intervalIntegral_zero_one_eq_integral_restrict (fun x : ℝ => ‖f k x‖)
            simpa [hterm] using hsum
    _ = ∫ x in (0 : ℝ)..1, ∑' k : ℕ, f k x := by
          exact (intervalIntegral_zero_one_eq_integral_restrict (fun x : ℝ => ∑' k : ℕ, f k x)).symm

end Commons.Analysis.Integral
