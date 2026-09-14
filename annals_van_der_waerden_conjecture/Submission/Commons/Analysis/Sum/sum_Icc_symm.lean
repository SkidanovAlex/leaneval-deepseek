import Mathlib

open scoped BigOperators

namespace Commons.Analysis.Sum

/-- `[-N-1, N+1]` is obtained from `[-N, N]` by adjoining the two new endpoints `-(N+1)` and
`N+1`. -/
private lemma icc_symm_key (N : ℕ) :
    Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
  have h1 := Finset.insert_Icc_left_eq_Icc_sub_one (a := -(N : ℤ)) (b := (N : ℤ) + 1)
    (by omega : -(N : ℤ) - 1 ≤ (N : ℤ) + 1)
  have h2 := Finset.insert_Icc_sub_one_right_eq_Icc (a := -(N : ℤ)) (b := (N : ℤ) + 1)
    (by omega : -(N : ℤ) ≤ (N : ℤ) + 1)
  rw [show -(N : ℤ) - 1 = -((N : ℤ) + 1) by ring] at h1
  rw [show (N : ℤ) + 1 - 1 = (N : ℤ) by ring] at h2
  rw [← h1, ← h2]

/-- Splitting a symmetric sum over `[-N, N]` into the positive and negative halves. -/
theorem sum_Icc_symm (N : ℕ) (f : ℤ → ℝ) :
    (∑ y ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f y)
      = f 0 + ∑ n ∈ Finset.Icc 1 N, (f (n : ℤ) + f (-(n : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hS : (∑ y ∈ Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1), f y)
        = f (-((N : ℤ) + 1))
            + (f ((N : ℤ) + 1) + ∑ y ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f y) := by
      rw [icc_symm_key N]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    push_cast
    rw [hS, Finset.sum_Icc_succ_top (f := fun n : ℕ => f (n : ℤ) + f (-(n : ℤ))) (by omega),
      ih]
    push_cast
    ring

end Commons.Analysis.Sum
