import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.MeasureTheory.Integral

/-- **Scaling a weighted integral over the half line.**  For `c > 0` the substitution
`t ↦ t / c` in `∫_0^∞ f(t v) t^{-2} dt` gives a factor `c`:

`∫_{t>0} f(t · (c v)) t^{-2} dt = c ∫_{t>0} f(t · v) t^{-2} dt`.

(The scalar multiplication is the one on `EuclideanSpace ℝ (Fin n)`.) -/
theorem interval_half_line_scaling {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), f (t • (c • v)) * (t ^ 2)⁻¹)
      = c * ∫ t in Set.Ioi (0 : ℝ), f (t • v) * (t ^ 2)⁻¹ := by
  have hc0 : c ≠ 0 := hc.ne'
  have hX : ∀ t : ℝ, c ^ 2 * ((c * t) ^ 2)⁻¹ = (t ^ 2)⁻¹ := by
    intro t
    rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc0), one_mul]
  have hpoint : ∀ t : ℝ, f (t • (c • v)) * (t ^ 2)⁻¹
      = c ^ 2 * (f ((c * t) • v) * ((c * t) ^ 2)⁻¹) := by
    intro t
    rw [smul_smul, mul_comm t c, ← hX t, mul_left_comm]
  have h1 : c ^ 2 * c⁻¹ = c := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
  calc
    (∫ t in Set.Ioi (0 : ℝ), f (t • (c • v)) * (t ^ 2)⁻¹)
        = ∫ t in Set.Ioi (0 : ℝ), c ^ 2 * (f ((c * t) • v) * ((c * t) ^ 2)⁻¹) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpoint t)
    _ = c ^ 2 * ∫ t in Set.Ioi (0 : ℝ), f ((c * t) • v) * ((c * t) ^ 2)⁻¹ := by
          rw [MeasureTheory.integral_const_mul]
    _ = c ^ 2 * (c⁻¹ * ∫ t in Set.Ioi (0 : ℝ), f (t • v) * (t ^ 2)⁻¹) := by
          rw [MeasureTheory.integral_comp_mul_left_Ioi (fun x : ℝ => f (x • v) * (x ^ 2)⁻¹) 0 hc]
          simp only [mul_zero, smul_eq_mul]
    _ = c * ∫ t in Set.Ioi (0 : ℝ), f (t • v) * (t ^ 2)⁻¹ := by
          rw [← mul_assoc, h1]

end Commons.MeasureTheory.Integral