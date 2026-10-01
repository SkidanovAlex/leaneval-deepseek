import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Integral

/-- Integral sandwich on an interval: pointwise `c ≤ g ≤ d` on the open interval
`(u, v)` (with `u ≤ v`) implies `c·(v−u) ≤ ∫_u^v g ≤ d·(v−u)`. -/
theorem interval_integral_between_consts {g : ℝ → ℝ} {c d u v : ℝ}
    (huv : u ≤ v) (hcd : c ≤ d)
    (hg : ∀ x : ℝ, x ∈ Set.Ioo u v → c ≤ g x ∧ g x ≤ d)
    (hgi : IntervalIntegrable g MeasureTheory.volume u v) :
    c * (v - u) ≤ ∫ x in u..v, g x ∧ ∫ x in u..v, g x ≤ d * (v - u) := by
  constructor
  · have hmono : (∫ x in u..v, (fun _ : ℝ => c) x) ≤ ∫ x in u..v, g x := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo
        (f := fun _ : ℝ => c) (g := g) (μ := MeasureTheory.volume) huv
        (intervalIntegrable_const (μ := MeasureTheory.volume) (E := ℝ))
        hgi (fun x hx => (hg x hx).1)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmono
  · have hmono : (∫ x in u..v, g x) ≤ ∫ x in u..v, (fun _ : ℝ => d) x := by
      exact intervalIntegral.integral_mono_on_of_le_Ioo
        (f := g) (g := fun _ : ℝ => d) (μ := MeasureTheory.volume) huv
        hgi (intervalIntegrable_const (μ := MeasureTheory.volume) (E := ℝ))
        (fun x hx => (hg x hx).2)
    simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmono

end Commons.Analysis.Integral