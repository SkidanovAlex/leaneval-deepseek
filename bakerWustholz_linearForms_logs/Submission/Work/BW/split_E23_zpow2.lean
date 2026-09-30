import Mathlib
import Submission.Work.BW.split_E23_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pure power-law identity in an arbitrary field: for `ξ ≠ 0`, `r ≥ 2` and any `N`,
`ξ^{-N} · ξ^{(N+1)(r-1)} · 2^N = ξ^{r-1} · (2ξ^{r-2})^N`.
This is the algebraic content of `split_E23_zpow2`. -/
lemma zpow_split_identity {K : Type*} [Field K] (ξ : K) (hξ : ξ ≠ 0) {r N : ℕ} (hr : 2 ≤ r) :
    ξ^(-(N:ℤ)) * ξ^((N+1)*(r-1)) * (2:K)^N = ξ^(r-1) * (2*ξ^(r-2))^N := by
  have h1 : r - 2 + 1 = r - 1 := by omega
  have hξr2 : ξ⁻¹ * ξ^(r-1) = ξ^(r-2) := by
    rw [← h1, pow_succ, ← mul_assoc, mul_comm (ξ⁻¹) (ξ^(r-2)), mul_assoc,
      inv_mul_cancel₀ hξ, mul_one]
  have hA : ξ^(-(N:ℤ)) = (ξ^N)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hB : ξ^((N+1)*(r-1)) = (ξ^(r-1))^N * ξ^(r-1) := by
    rw [Nat.add_mul, Nat.one_mul, pow_add, pow_mul']
  rw [hA, hB]
  rw [show (ξ^N)⁻¹ * ((ξ^(r-1))^N * ξ^(r-1)) * (2:K)^N
      = ((ξ^N)⁻¹ * (ξ^(r-1))^N) * (ξ^(r-1) * (2:K)^N) by ring]
  rw [show (ξ^N)⁻¹ * (ξ^(r-1))^N = (ξ^(r-2))^N by rw [← inv_pow, ← mul_pow, hξr2]]
  rw [mul_pow]
  ring

theorem split_E23_zpow2 {r d : ℕ} (hr : 2 ≤ r) :
    (pxi r)^(-(((r * pI r d) : ℕ) : ℤ)) * (pxi r)^((r * pI r d + 1) * (r-1)) * (2:ℝ)^(r * pI r d)
      = (pxi r)^(r-1) * (2 * (pxi r)^(r-2))^(r * pI r d) := by
  exact zpow_split_identity (pxi r) (ne_of_gt (pxi_pos hr)) (N := r * pI r d) hr

end Work.BW
