import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Calculus

open scoped Topology
open Set MeasureTheory intervalIntegral

/-- **Cauchy–Schwarz for interval integrals.**  For a nonnegative continuous function `f` on
`[a,b]` (`a ≤ b`), the square of the integral is at most `(b - a)` times the integral of `f ^ 2`. -/
theorem sq_intervalIntegral_le_length_mul_intervalIntegral_sq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (uIcc a b))
    (hnonneg : ∀ x ∈ uIcc a b, 0 ≤ f x) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  -- Cauchy–Schwarz: `(∫ f)² ≤ (∫ f²) · (∫ 1)`, via the nonnegativity of `∫ (f - t)²`.
  rcases lt_or_eq_of_le hab with hablt | rfl
  · have hf_int : IntervalIntegrable f volume a b := hf.intervalIntegrable
    have hfsq_int : IntervalIntegrable (fun x => (f x) ^ 2) volume a b :=
      (hf.pow 2).intervalIntegrable
    -- Expansion of `∫ (f - t)²` as a quadratic in `t`.
    have h_expand : ∀ t : ℝ, ∫ x in a..b, (f x - t) ^ 2
        = (∫ x in a..b, (f x) ^ 2) - 2 * t * (∫ x in a..b, f x) + t ^ 2 * (b - a) := by
      intro t
      have h1 : ∫ x in a..b, (f x - t) ^ 2
          = ∫ x in a..b, ((f x) ^ 2 - 2 * t * f x + t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      rw [h1]
      rw [intervalIntegral.integral_add (hfsq_int.sub (hf_int.const_mul (2 * t)))
        intervalIntegrable_const]
      rw [intervalIntegral.integral_sub hfsq_int (hf_int.const_mul (2 * t))]
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const]
      ring
    set I : ℝ := ∫ x in a..b, f x with hI
    set J : ℝ := ∫ x in a..b, (f x) ^ 2 with hJ
    have hden : (0 : ℝ) < b - a := by linarith
    -- `∫ (f - c)² ≥ 0` for the mean `c = I / (b - a)` yields `J - I²/(b - a) ≥ 0`.
    have hkey : 0 ≤ J - I ^ 2 / (b - a) := by
      have hnn : 0 ≤ ∫ x in a..b, (f x - I / (b - a)) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
      rw [h_expand (I / (b - a))] at hnn
      have heq : (∫ x in a..b, (f x) ^ 2) - 2 * (I / (b - a)) * (∫ x in a..b, f x)
            + (I / (b - a)) ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
        rw [← hI, ← hJ]
        field_simp
        ring
      rwa [heq] at hnn
    have h2 : I ^ 2 ≤ J * (b - a) := by
      have : I ^ 2 / (b - a) ≤ J := by linarith [hkey]
      exact (div_le_iff₀ hden).mp this
    linarith [h2]
  · -- Degenerate case `a = b`: both sides vanish.
    simp

end Commons.Analysis.Calculus