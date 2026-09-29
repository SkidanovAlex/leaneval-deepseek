import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval

/-- product of two interval integrals over `[0,1]` equals the iterated
double integral: `(∫₀¹ f)(∫₀¹ g) = ∫₀¹ ∫₀¹ f x·g y`.
Needed to write a product of integrals as a box integral.
Hypotheses: `f`, `g` integrable on `[0,1]` (interval integrals over volume). -/
lemma integral_mul_integral_interval (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x * g y := by
  -- For each fixed x the inner integral is f x times a constant in y, and the
  -- resulting integral in x is the product of the two one-dimensional integrals.
  calc
    (∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y)
        = ∫ x in (0 : ℝ)..1, f x * (∫ y in (0 : ℝ)..1, g y) := by
          exact (intervalIntegral.integral_mul_const (f := f)
            (r := (∫ y in (0 : ℝ)..1, g y))).symm
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x * g y := by
          apply congrArg (fun h : ℝ → ℝ => ∫ x in (0 : ℝ)..1, h x)
          funext x
          exact (intervalIntegral.integral_const_mul (r := f x) (f := g)).symm

end Commons.Analysis.Integral
