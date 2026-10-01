import Mathlib

namespace Work.BGTZ

/-- Pointwise telescoping bound: the `n`-th term `1/√(n+1)` is at most twice the
increment `√(n+1) - √n` of `√·`.  Indeed, multiplying by `√(n+1) > 0`, the
inequality is `1 ≤ 2(√(n+1) - √n)√(n+1)`, i.e. `2·√(n+1)·√n ≤ 2n+1`, which
follows from `2√(n+1)√n ≤ (√(n+1))² + (√n)² = 2n+1`. -/
private lemma inv_sqrt_succ_le (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hpos]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) + 1 by positivity),
             Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ) by positivity),
             sq_nonneg (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ))]

/-- `∑_{m=1}^{M} 1/√m ≤ 2√M`.  Telescoping the pointwise bound `inv_sqrt_succ_le`
gives the claim by induction on `M`. -/
theorem sum_inv_sqrt_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1:ℝ) / Real.sqrt (m:ℝ)) ≤ 2 * Real.sqrt (M:ℝ) := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega)]
    have hk := inv_sqrt_succ_le k
    simp only [Nat.cast_add, Nat.cast_one] at hk ih ⊢
    linarith

end Work.BGTZ
