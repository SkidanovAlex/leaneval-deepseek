import Mathlib
import Submission.Work.BMF.liouville.geom_sum_Icc_two_inv_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Telescoping bound: `∑_{p=2}^{M} 1/(p(p-1)) ≤ 1`.

Since `1/(p(p-1)) = 1/(p-1) - 1/p`, the sum is `1 - 1/M`. -/
theorem sum_inv_mul_pred_le_one (M : ℕ) :
    ∑ p ∈ Finset.Icc 2 M, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  rcases (show M < 2 ∨ 2 ≤ M by omega) with hM | hM
  · rw [Finset.Icc_eq_empty (by omega : ¬ 2 ≤ M)]
    simp
  · have hterm : ∀ p ∈ Finset.Icc 2 M,
        (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
          = (-1 / (((p + 1 : ℕ) : ℝ) - 1)) - (-1 / ((p : ℝ) - 1)) := by
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
      have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
      have hpne : (p : ℝ) ≠ 0 := by linarith
      have hcast : (((p + 1 : ℕ) : ℝ) - 1) = (p : ℝ) := by push_cast; ring
      rw [hcast]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm,
      Finset.sum_Icc_sub hM (fun i : ℕ => -1 / ((i : ℝ) - 1))]
    have hcast : (((M + 1 : ℕ) : ℝ) - 1) = (M : ℝ) := by push_cast; ring
    have htwo : (((2 : ℕ) : ℝ) - 1) = (1 : ℝ) := by norm_num
    rw [hcast, htwo, div_one]
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
    have hp : (0 : ℝ) ≤ 1 / (M : ℝ) := div_nonneg zero_le_one hM0
    have hneg : -1 / (M : ℝ) = -(1 / (M : ℝ)) := by ring
    rw [hneg]
    linarith

/-- The rectangle sum `∑_{p=2}^{M} ∑_{k=2}^{M} p^{-k}` is at most `1`.

Route: the inner sum over `k` is bounded by the geometric tail `1/(p(p-1))
(the companion lemma `Work.BMF.liouville.geom_sum_Icc_two_inv_pow_le`, module
`Submission.Work.BMF.liouville.geom_sum_Icc_two_inv_pow_le`, states exactly this for any upper
limit `K`), and the telescoping sum `∑_{p=2}^{M} (1/(p-1) - 1/p) = 1 - 1/M ≤ 1`
(`Finset.sum_Icc_sub` with `f p = 1/(p-1)`). -/
theorem rect_inv_pow_sum_le_one (M : ℕ) :
    ∑ p ∈ Finset.Icc 2 M, ∑ k ∈ Finset.Icc 2 M, (1 : ℝ) / (p : ℝ) ^ k ≤ 1 := by
  refine le_trans (Finset.sum_le_sum (fun p hp =>
    geom_sum_Icc_two_inv_pow_le p M (Finset.mem_Icc.mp hp).1)) ?_
  exact sum_inv_mul_pred_le_one M

end Work.BMF.liouville
