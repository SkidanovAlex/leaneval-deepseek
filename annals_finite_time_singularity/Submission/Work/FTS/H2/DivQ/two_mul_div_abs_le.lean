import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

/-- Elementary AM-GM in the exact shape needed for the weighted Hardy inequality: for
nonnegative `A`, `B`, `cross` with `cross² ≤ A·B`, any nonzero real `s` satisfies
`2·cross/|s| ≤ A/2 + 2·B/s²`.  (This is `2ab ≤ λa² + b²/λ` with `λ = |s|/2`, written in
terms of the products `A = a²`, `B = b²`, `cross = ab` so that no square root appears.) -/
lemma two_mul_div_abs_le (A B cross s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ cross)
    (hsq : cross ^ 2 ≤ A * B) (hs : s ≠ 0) :
    2 * cross / |s| ≤ A / 2 + 2 * B / s ^ 2 := by
  have habs : 0 < |s| := abs_pos.mpr hs
  -- Key inequality: the whole content, with all denominators cleared and squares
  -- of `|s|` (rather than of `s`) so that the algebraic identity is exact.
  have hkey : 4 * cross * |s| ≤ A * |s| ^ 2 + 4 * B := by
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · -- `A = 0`: then `cross² ≤ 0`, so `cross = 0`, and the claim is trivial.
      have hc0 : cross = 0 := by nlinarith [sq_nonneg cross, hsq, hA0]
      rw [← hA0, hc0]
      nlinarith [hB, sq_nonneg |s|]
    · -- `A > 0`: `A·(A|s|² - 4·cross·|s| + 4B) = (A|s| - 2·cross)² + 4·(AB - cross²) ≥ 0`.
      have hpoly : 0 ≤ A * (A * |s| ^ 2 - 4 * cross * |s| + 4 * B) := by
        nlinarith [sq_nonneg (A * |s| - 2 * cross), hsq]
      have h := (mul_nonneg_iff_of_pos_left hApos).mp hpoly
      linarith
  -- Multiply the target by the positive factor `2·|s|²` and clear denominators.
  have h1 : (2 * cross / |s|) * (2 * |s| ^ 2) = 4 * cross * |s| := by
    field_simp
    ring
  have h2 : (A / 2 + 2 * B / s ^ 2) * (2 * |s| ^ 2) = A * s ^ 2 + 4 * B := by
    rw [sq_abs]
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 * |s| ^ 2)
  rw [h1, h2]
  simpa [sq_abs] using hkey

end Work.FTS.H2.DivQ
