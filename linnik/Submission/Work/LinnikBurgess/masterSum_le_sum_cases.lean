import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs

namespace Work.LinnikBurgess

open Classical

/-- The full weight `wtAB m a b` is a product of elementary weights `wg`, each of which is a
square root and hence non-negative. -/
lemma wtAB_nonneg (m : ℕ) (a b : Fin 3 → ℕ) : 0 ≤ wtAB m a b := by
  simp only [wtAB]
  exact mul_nonneg (mul_nonneg (wg_nonneg m (a 0) (a 1)) (wg_nonneg m (a 0) (a 2)))
    (mul_nonneg (mul_nonneg (wg_nonneg m (a 0) (b 0)) (wg_nonneg m (a 0) (b 1)))
      (wg_nonneg m (a 0) (b 2)))

/-- Elementary real fact: if `P → Q1 ∨ Q2 ∨ Q3` and `0 ≤ W`, then the `P`-weighted term is at
most the sum of the three terms weighted by `P ∧ Q1`, `P ∧ Q2`, `P ∧ Q3`.  (At least one of the
three summands equals `W`, and the others are non-negative.) -/
lemma ite_le_sum_three {P : Prop} [Decidable P] {W : ℝ} (hW : 0 ≤ W)
    {Q1 Q2 Q3 : Prop} [Decidable Q1] [Decidable Q2] [Decidable Q3]
    (hcover : P → Q1 ∨ Q2 ∨ Q3) :
    (if P then W else 0)
      ≤ (if P ∧ Q1 then W else 0) + (if P ∧ Q2 then W else 0) + (if P ∧ Q3 then W else 0) := by
  by_cases hP : P
  · rcases hcover hP with h1 | h2 | h3
    · rw [if_pos hP, if_pos (show P ∧ Q1 from ⟨hP, h1⟩)]
      have hn2 : (0 : ℝ) ≤ (if P ∧ Q2 then W else 0) := by split <;> linarith
      have hn3 : (0 : ℝ) ≤ (if P ∧ Q3 then W else 0) := by split <;> linarith
      linarith
    · rw [if_pos hP, if_pos (show P ∧ Q2 from ⟨hP, h2⟩)]
      have hn1 : (0 : ℝ) ≤ (if P ∧ Q1 then W else 0) := by split <;> linarith
      have hn3 : (0 : ℝ) ≤ (if P ∧ Q3 then W else 0) := by split <;> linarith
      linarith
    · rw [if_pos hP, if_pos (show P ∧ Q3 from ⟨hP, h3⟩)]
      have hn1 : (0 : ℝ) ≤ (if P ∧ Q1 then W else 0) := by split <;> linarith
      have hn2 : (0 : ℝ) ≤ (if P ∧ Q2 then W else 0) := by split <;> linarith
      linarith
  · rw [if_neg hP]
    have e1 : (if P ∧ Q1 then W else 0) = 0 := if_neg (fun h => hP h.1)
    have e2 : (if P ∧ Q2 then W else 0) = 0 := if_neg (fun h => hP h.1)
    have e3 : (if P ∧ Q3 then W else 0) = 0 := if_neg (fun h => hP h.1)
    rw [e1, e2, e3]
    simp

/-- The master sum is at most the sum of its three case parts:  every pair satisfies at least one of `CaseI`, `CaseS`, `CaseT` (`case_cover`), and the weight `wtAB` is non-negative. -/
theorem masterSum_le_sum_cases (H m d g : ℕ) :
    masterSum H m d g ≤ sumI H m d g + sumS H m d g + sumT H m d g := by
  simp only [masterSum, sumI, sumS, sumT, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  exact ite_le_sum_three (wtAB_nonneg m a b) (fun _ => case_cover a b)

end Work.LinnikBurgess
