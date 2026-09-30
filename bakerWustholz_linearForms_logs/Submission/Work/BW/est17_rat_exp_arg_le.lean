import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `(J+1)·2h(λ₋₁+1) ≤ 2(J+1)h(D₀+1)` for `λ₋₁ ≤ D₀`: the exponent comparison which converts the
2-adic Kummer integrability bound `(2^{J+1})^{2h(λ₀+1)}·u(h)^{t₀}·Θ ∈ ℤ` into BW's
`2hJ(D₀+1) log 2`-type term. -/
theorem est17_rat_exp_arg_le {J h D0 l : ℕ} (hl : l ≤ D0) :
    (((J + 1) * (2 * h * (l + 1)) : ℕ) : ℝ)
      ≤ 2 * ((J : ℝ) + 1) * (h : ℝ) * ((D0 : ℝ) + 1) := by
  have h1 : (J + 1) * (2 * h * (l + 1)) ≤ (J + 1) * (2 * h * (D0 + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ hl))
  have h2 : (((J + 1) * (2 * h * (l + 1)) : ℕ) : ℝ)
      ≤ (((J + 1) * (2 * h * (D0 + 1)) : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : (((J + 1) * (2 * h * (D0 + 1)) : ℕ) : ℝ)
      = 2 * ((J : ℝ) + 1) * (h : ℝ) * ((D0 : ℝ) + 1) := by push_cast; ring
  linarith

end Work.BW
