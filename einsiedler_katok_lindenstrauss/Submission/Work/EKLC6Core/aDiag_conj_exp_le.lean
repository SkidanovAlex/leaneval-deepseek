import Mathlib
import Submission.Work.EKLC6Core.InjRadius

namespace Work.EKLC6Core

theorem aDiag_conj_exp_le (t : Fin 3 → ℝ) (n : ℕ) (i j : Fin 3) :
    Real.exp ((n : ℝ) * (t j - t i)) ≤
      Real.exp ((n : ℝ) * max 1 (2 * ∑ k, |t k|)) := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  have hj : |t j| ≤ ∑ k, |t k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (t k)) (Finset.mem_univ j)
  have hi : |t i| ≤ ∑ k, |t k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (t k)) (Finset.mem_univ i)
  have h1 : t j - t i ≤ |t j| + |t i| := by
    have a : t j ≤ |t j| := le_abs_self _
    have b : -t i ≤ |t i| := neg_le_abs _
    linarith
  have h3 : 2 * ∑ k, |t k| ≤ max 1 (2 * ∑ k, |t k|) := le_max_right _ _
  linarith

end Work.EKLC6Core
