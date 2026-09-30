import Mathlib
import Submission.Work.BW.split_E23_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Exponent bookkeeping for the `ξ`/`2` factors of the §23 split: since `ξ = pxi r > 0`,
`ξ^{-J} · ξ^{r(J+1)} · 2^J = ξ^r · (2 ξ^{r-1})^J` with `J = r · pI r d`. -/
theorem split_E23_zpow1 {r d : ℕ} (hr : 2 ≤ r) :
    (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^(r * (r * pI r d + 1)) * (2:ℝ)^(r * pI r d)
      = (pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d) := by
  -- Natural-number exponent identity `r * (J + 1) = J + (r + (r-1) * J)`, `J = r * pI r d`.
  have h1 : r * (r * pI r d + 1) = (r * pI r d) + (r + (r - 1) * (r * pI r d)) := by
    have hr1 : 1 ≤ r := by omega
    have key : r * (r * pI r d) = (r - 1) * (r * pI r d) + (r * pI r d) := by
      nth_rewrite 1 [← Nat.sub_add_cancel hr1]
      rw [Nat.add_mul, one_mul]
    rw [Nat.mul_add, Nat.mul_one, key]
    omega
  have hx : (pxi r) ≠ 0 := ne_of_gt (pxi_pos hr)
  have hxJ : (pxi r) ^ (r * pI r d) ≠ 0 := pow_ne_zero _ hx
  have hL : (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^(r * (r * pI r d + 1)) * (2:ℝ)^(r * pI r d)
      = (pxi r)^(r + (r-1)*(r*pI r d)) * (2:ℝ)^(r*pI r d) := by
    rw [zpow_neg, zpow_natCast, h1, pow_add]
    rw [show (pxi r ^ (r*pI r d))⁻¹ * (pxi r ^ (r*pI r d) * pxi r ^ (r + (r-1)*(r*pI r d))) * 2^(r*pI r d)
        = ((pxi r^(r*pI r d))⁻¹ * pxi r^(r*pI r d)) * (pxi r^(r+(r-1)*(r*pI r d)) * 2^(r*pI r d)) by ring]
    rw [inv_mul_cancel₀ hxJ, one_mul]
  have hR : (pxi r)^r * (2 * (pxi r)^(r-1))^(r * pI r d)
      = (pxi r)^(r + (r-1)*(r*pI r d)) * (2:ℝ)^(r*pI r d) := by
    rw [mul_pow, ← pow_mul]
    rw [show (pxi r)^r * (2^(r*pI r d) * pxi r^((r-1)*(r*pI r d)))
        = (pxi r)^r * pxi r^((r-1)*(r*pI r d)) * 2^(r*pI r d) by ring]
    rw [← pow_add]
  rw [hL, hR]

end Work.BW
