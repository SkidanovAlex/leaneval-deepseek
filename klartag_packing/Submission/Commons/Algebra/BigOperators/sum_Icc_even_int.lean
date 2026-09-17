import Mathlib

namespace Commons.Algebra.BigOperators

open Finset

theorem sum_Icc_even_int (Q : ℤ) (hQ : 0 ≤ Q) (f : ℤ → ℝ) (hf : ∀ j : ℤ, f (-j) = f j) :
    ∑ j ∈ Finset.Icc (-Q) Q, f j
      = 2 * (∑ k ∈ Finset.range Q.toNat, f (k : ℤ)) - f 0 + 2 * f Q := by
  have key : ∀ n : ℕ,
      ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f j
        = 2 * (∑ k ∈ Finset.range n, f (k : ℤ)) - f 0 + 2 * f (n : ℤ) := by
    intro n
    induction n with
    | zero => simp; ring
    | succ n ih =>
      rw [Nat.cast_succ]
      rw [show -(↑n + 1 : ℤ) = -(↑n) - 1 by ring]
      have hm1 : ((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ) - 1) (n : ℤ) := by
        simp only [Finset.mem_Icc]; omega
      have hm2 : (-(n : ℤ) - 1) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
        simp only [Finset.mem_Icc]; omega
      have hIcc1 : Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1)
          = insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ) - 1) (n : ℤ)) := by
        have h := insert_Icc_right_eq_Icc_add_one (a := -(n : ℤ) - 1) (b := (n : ℤ)) (by omega)
        exact h.symm
      have hIcc2 : Finset.Icc (-(n : ℤ) - 1) (n : ℤ)
          = insert (-(n : ℤ) - 1) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
        have h := insert_Icc_add_one_left_eq_Icc (a := -(n : ℤ) - 1) (b := (n : ℤ)) (by omega)
        rw [show (-(n : ℤ) - 1) + 1 = -(n : ℤ) by ring] at h
        exact h.symm
      have hneg : f (-(n : ℤ) - 1) = f ((n : ℤ) + 1) := by
        rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring]
        exact hf _
      rw [hIcc1, Finset.sum_insert hm1, hIcc2, Finset.sum_insert hm2, hneg, ih]
      rw [Finset.sum_range_succ]
      ring
  have hQn : (Q.toNat : ℤ) = Q := Int.toNat_of_nonneg hQ
  have hk := key Q.toNat
  rw [hQn] at hk
  exact hk

end Commons.Algebra.BigOperators
