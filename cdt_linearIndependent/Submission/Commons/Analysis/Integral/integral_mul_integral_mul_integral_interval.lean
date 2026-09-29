import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

set_option linter.unusedVariables false

namespace Commons.Analysis.Integral

/-- product of three interval integrals over `[0,1]` equals the iterated
triple integral: `(∫₀¹ f)(∫₀¹ g)(∫₀¹ h) = ∫₀¹∫₀¹∫₀¹ f x·g y·h z`.
Hypotheses: `f`, `g`, `h` integrable on `[0,1]`. -/
lemma integral_mul_integral_mul_integral_interval (f g h : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1)
    (hh : IntervalIntegrable h MeasureTheory.volume 0 1) :
    ((∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y)) * (∫ z in (0 : ℝ)..1, h z) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f x * g y * h z := by
  -- Each layer of the iterated integral is rewritten by pulling the factors
  -- that do not depend on the innermost integration variable out of the
  -- interval integral (`intervalIntegral.integral_const_mul` /
  -- `intervalIntegral.integral_mul_const`, both unconditional), leaving an
  -- algebraic identity in the three scalar interval integrals.
  simp

end Commons.Analysis.Integral