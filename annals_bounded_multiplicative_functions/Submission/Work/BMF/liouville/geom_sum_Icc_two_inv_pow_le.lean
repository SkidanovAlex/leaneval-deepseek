import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- Namespace `Work.BMF.liouville`. Import: `Mathlib`.

Geometric tail bound: for `2 ≤ p`, `∑_{k=2}^{K} p^{-k} ≤ 1/(p(p-1))`. -/
theorem geom_sum_Icc_two_inv_pow_le (p K : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ k ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hx : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hx1 : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one hp_pos]; exact hp_gt1
  have hsum : ∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / (p : ℝ) ^ k
      = ∑ k ∈ Finset.Ico 2 (K + 1), ((1 : ℝ) / (p : ℝ)) ^ k := by
    rw [← Finset.Ico_add_one_right_eq_Icc (2 : ℕ) K]
    exact Finset.sum_congr rfl (fun k _ => (one_div_pow (p : ℝ) k).symm)
  rw [hsum]
  calc ∑ k ∈ Finset.Ico 2 (K + 1), ((1 : ℝ) / (p : ℝ)) ^ k
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 / (1 - (1 : ℝ) / (p : ℝ)) :=
        geom_sum_Ico_le_of_lt_one hx hx1
    _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
        have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

end Work.BMF.liouville
