import Mathlib

namespace Work.Peluse.LadderA

/-- **Level raising for `rpow` on the two factors.**  From the single datum
`c * X ^ (2 ^ tt) ≤ Y` (`X, c ≥ 0`, `β = mm + tt`) one may distribute the `2^β`-nd roots over
the product: `c ^ (1/2^β) * X ^ (1/2^mm) ≤ Y ^ (1/2^β)`.

The point is the exponent bookkeeping: `1/2^β = (1/2^mm) * (1/2^tt)`, so with `P = 2^β`,
`Q = 2^mm`, `R = 2^tt` and `P = Q * R` one has
`X ^ (1/Q) = X ^ (R * (1/P)) = (X ^ R) ^ (1/P)`, and the hypothesis says exactly
`(c * X ^ R) ≤ Y`, so the claim is `(c * X^R)^(1/P) ≤ Y^(1/P)` with
`(c * X^R)^(1/P) = c^(1/P) * (X^R)^(1/P)` (`Real.mul_rpow`) — monotonicity of `·^(1/P)`
on the nonnegative reals finishes. -/
theorem rpowLevelRaise {X Y c : ℝ} {mm tt β : ℕ}
    (hX : 0 ≤ X) (hc : 0 ≤ c) (hβ : β = mm + tt)
    (h : c * X ^ (2 ^ tt) ≤ Y) :
    c ^ (1 / (2 : ℝ) ^ β) * X ^ (1 / (2 : ℝ) ^ mm) ≤ Y ^ (1 / (2 : ℝ) ^ β) := by
  -- rewrite the natural power `2 ^ tt` as a real power
  have hcast : (((2:ℕ)^tt : ℕ) : ℝ) = (2:ℝ)^tt := by push_cast; ring
  -- `X ^ (1/2^mm) = (X ^ (2^tt)) ^ (1/2^β)`, because `1/2^mm = 2^tt * (1/2^β)`
  have hkey : (X ^ (2^tt)) ^ (1/(2:ℝ)^β) = X ^ (1/(2:ℝ)^mm) := by
    rw [← Real.rpow_natCast X (2^tt)]
    rw [← Real.rpow_mul hX]
    congr 1
    rw [hcast, hβ, pow_add]
    field_simp
  have hbase : 0 ≤ c * X ^ (2^tt) := mul_nonneg hc (pow_nonneg hX _)
  calc c ^ (1 / (2 : ℝ) ^ β) * X ^ (1 / (2 : ℝ) ^ mm)
      = c ^ (1/(2:ℝ)^β) * (X ^ (2^tt)) ^ (1/(2:ℝ)^β) := by rw [hkey]
    _ = (c * X ^ (2^tt)) ^ (1/(2:ℝ)^β) := by rw [Real.mul_rpow hc (pow_nonneg hX _)]
    _ ≤ Y ^ (1/(2:ℝ)^β) := Real.rpow_le_rpow hbase h (by positivity)

end Work.Peluse.LadderA
