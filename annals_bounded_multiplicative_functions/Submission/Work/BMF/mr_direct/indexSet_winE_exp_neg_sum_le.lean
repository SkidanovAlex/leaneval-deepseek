import Mathlib
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The per-index bound: for every `j`, the weighted coefficient energy
`e^{-2αj/K} · winE_j` is at most `(2 e^{1/K}/X₁) · e^{(1-2α)j/K}`. -/
private lemma winE_exp_factor (b : ℕ → ℂ) (K P Q X₁ X₂ α : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) (hK : K ≠ 0) (j : ℕ) :
    Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j
      ≤ (2 * Real.exp (1 / K) / X₁) * Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by
  have h1 : Real.exp (-(2 * α * (j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X₁)
      = (2 * Real.exp (1 / K) / X₁) * Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by
    have hexp : Real.exp (-(2 * α * (j : ℝ) / K)) * Real.exp (((j : ℝ) + 1) / K)
        = Real.exp (1 / K) * Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      field_simp
      ring
    calc Real.exp (-(2 * α * (j : ℝ) / K)) * (2 * Real.exp (((j : ℝ) + 1) / K) / X₁)
        = (2 / X₁) * (Real.exp (-(2 * α * (j : ℝ) / K)) *
            Real.exp (((j : ℝ) + 1) / K)) := by ring
      _ = (2 / X₁) * (Real.exp (1 / K) * Real.exp ((1 - 2 * α) * (j : ℝ) / K)) := by
          rw [hexp]
      _ = (2 * Real.exp (1 / K) / X₁) * Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left
    (winE_le_exp b P Q K X₁ X₂ j hb hX) (Real.exp_pos _).le) ?_
  rw [h1]

theorem indexSet_winE_exp_neg_sum_le (b : ℕ → ℂ) (K P Q X₁ X₂ α : ℝ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 0 < X₁) (hK : 3 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * Work.BMF.mr_direct.winE b P Q K X₁ X₂ j)
      ≤ 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁) := by
  have hKpos : 0 < K := by linarith
  have hQpos : 0 < Q := by linarith
  have hQe : 0 ≤ Q ^ (1 - 2 * α) := (Real.rpow_pos_of_pos hQpos _).le
  have hLq : 0 ≤ Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2) := by
    have hLPQ : 0 ≤ Real.log (Q / P) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith : (0:ℝ) < P)]; linarith)
    exact mul_nonneg hQe (by nlinarith [hLPQ, hKpos])
  have he : 2 * Real.exp (1 / K) * 3 ≤ 20 := by
    have h1 : Real.exp (1 / K) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by rw [div_le_one hKpos]; linarith)
    have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  calc (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j)
      ≤ ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          (2 * Real.exp (1 / K) / X₁) * Real.exp ((1 - 2 * α) * (j : ℝ) / K) :=
        Finset.sum_le_sum fun j _ => winE_exp_factor b K P Q X₁ X₂ α hb hX hKpos.ne' j
    _ = (2 * Real.exp (1 / K) / X₁) *
          ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q, Real.exp ((1 - 2 * α) * (j : ℝ) / K) := by
        rw [Finset.mul_sum]
    _ ≤ (2 * Real.exp (1 / K) / X₁) *
          (3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2)) :=
        mul_le_mul_of_nonneg_left (indexSet_exp_pos_sum_le K P Q α hK hP hPQ hα0 hα1)
          (by positivity)
    _ ≤ 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁) := by
        calc (2 * Real.exp (1 / K) / X₁) * (3 * Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2))
            = (2 * Real.exp (1 / K) * 3) *
                (Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2)) / X₁ := by ring
          _ ≤ 20 * (Q ^ (1 - 2 * α) * (K * Real.log (Q / P) + 2)) / X₁ := by
              apply div_le_div_of_nonneg_right _ hX.le
              exact mul_le_mul_of_nonneg_right he hLq
          _ = 20 * (K * Real.log (Q / P) + 2) * (Q ^ (1 - 2 * α) / X₁) := by ring

end Work.BMF.mr_direct
