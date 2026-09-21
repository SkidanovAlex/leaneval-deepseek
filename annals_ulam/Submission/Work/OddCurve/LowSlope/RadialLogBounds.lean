import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogDefs

/-!
# The derivative bounds for the normalised radial system
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-- The Titu / Cauchy–Schwarz inequality `(x+y)^2 ≤ (1+λ)(x^2 + y^2/λ)` for `λ > 0`. -/
lemma titu (x y : ℝ) {q : ℝ} (hq : 0 < q) : (x + y) ^ 2 ≤ (1 + q) * (x ^ 2 + y ^ 2 / q) := by
  have h : 0 ≤ (x * q - y) ^ 2 := sq_nonneg _
  have hq' : (0 : ℝ) < q := hq
  have h2 : (x + y) ^ 2 * q ≤ (1 + q) * (x ^ 2 + y ^ 2 / q) * q := by
    field_simp
    nlinarith [h]
  exact (mul_le_mul_iff_of_pos_right hq).mp h2

/-- `(3/2)√δ ≤ 1 + δ`. -/
lemma three_halves_sqrt_le (δ : ℝ) (hδ : 0 ≤ δ) : 3 / 2 * Real.sqrt δ ≤ 1 + δ := by
  have h : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ
  have h2 : (0 : ℝ) ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  nlinarith [sq_nonneg (Real.sqrt δ - 3 / 4), h, h2, sq_nonneg (Real.sqrt δ)]
  all_goals nlinarith [sq_nonneg (Real.sqrt δ - 1)]

variable {n : ℕ}

/-- `(x^m)^{1/m} = x` for `x ≥ 0`. -/
lemma rpow_pow_inv (x : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : m ≠ 0) :
    (x ^ m) ^ (((m : ℕ) : ℝ)⁻¹) = x := by
  rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx]
  rw [show (((m : ℕ) : ℝ)) * (((m : ℕ) : ℝ))⁻¹ = 1 by
    rw [mul_inv_cancel₀ (by positivity)], Real.rpow_one]

/-- `(R^m)^θ = R^k`. -/
lemma pow_rpow_radTh (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (R ^ (2 * n + 2)) ^ (radTh n) = R ^ (2 * n + 1) := by
  rw [← Real.rpow_natCast R (2 * n + 2), ← Real.rpow_mul hR,
    show (((2 * n + 2 : ℕ) : ℝ)) * radTh n = ((2 * n + 1 : ℕ) : ℝ) by
      rw [radTh]
      field_simp,
    Real.rpow_natCast]

end Work.OddCurve.LowSlope
