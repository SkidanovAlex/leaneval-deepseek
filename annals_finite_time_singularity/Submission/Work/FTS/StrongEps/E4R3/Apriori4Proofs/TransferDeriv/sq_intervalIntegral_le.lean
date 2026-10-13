import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- *Cauchy–Schwarz for interval integrals.*
For `a ≤ b` and `f` interval-integrable together with `f ^ 2` on `[a,b]`,
`(∫_a^b f)² ≤ (b - a) · ∫_a^b f²`.

The proof does not use the Cauchy–Schwarz inequality itself: it is the classical
"discriminant" argument.  For every `c : ℝ`, the interval integral of the nonnegative
function `t ↦ (f t - c)²` is nonnegative, and expanding it gives the quadratic
`c² (b - a) - 2 c (∫f) + ∫f² ≥ 0`.  Evaluating at the minimiser `c = (∫f)/(b - a)`
(available because `b - a > 0` when `a < b`) yields the claim; the degenerate case
`a = b` is immediate since both sides vanish. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hfsq : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp [intervalIntegral.integral_same]
  · set A : ℝ := ∫ t in a..b, f t with hA
    set B : ℝ := ∫ t in a..b, f t ^ 2 with hB
    have hbd : (0 : ℝ) < b - a := sub_pos.mpr h
    -- the shifted square has nonnegative integral, for every shift
    have key : ∀ c : ℝ, 0 ≤ c ^ 2 * (b - a) - 2 * c * A + B := by
      intro c
      have h1 : (∫ t in a..b, (f t - c) ^ 2)
          = ∫ t in a..b, (f t ^ 2 - 2 * c * f t + c ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      have hE : (∫ t in a..b, (f t - c) ^ 2) = c ^ 2 * (b - a) - 2 * c * A + B := by
        rw [h1]
        rw [intervalIntegral.integral_add (hfsq.sub (hfi.const_mul (2 * c)))
          intervalIntegrable_const]
        rw [intervalIntegral.integral_sub hfsq (hfi.const_mul (2 * c))]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        rw [← hA, ← hB]
        ring
      have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg (f u - c))
      rwa [hE] at hnn
    -- evaluate the quadratic at its vertex
    have hzA := key (A / (b - a))
    have hexp : (b - a) * ((A / (b - a)) ^ 2 * (b - a) - 2 * (A / (b - a)) * A + B)
        = B * (b - a) - A ^ 2 := by
      field_simp [ne_of_gt hbd]
      ring
    have hle : A ^ 2 ≤ B * (b - a) := by
      have hh : 0 ≤ B * (b - a) - A ^ 2 := by
        rw [← hexp]
        exact mul_nonneg hbd.le hzA
      linarith
    rw [mul_comm (b - a) B]
    exact hle

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
