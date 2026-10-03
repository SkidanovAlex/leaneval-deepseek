import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.NumberTheory.Divisors

open Finset

theorem sum_filter_dvd_reindex {q N : ℕ} (hq : 0 < q) (f : ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n), f n)
      = ∑ m ∈ Finset.Icc 1 (N / q), f (q * m) := by
  have hset : (Finset.Icc 1 N).filter (fun n => q ∣ n)
      = (Finset.Icc 1 (N / q)).image (fun m => q * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, hN⟩, m, hm⟩
      refine ⟨m, ⟨?_, ?_⟩, hm.symm⟩
      · have : 0 < q * m := by rw [← hm]; omega
        exact Nat.pos_of_mul_pos_left this
      · rw [Nat.le_div_iff_mul_le hq, mul_comm, ← hm]
        exact hN
    · rintro ⟨m, ⟨hm1, hmN⟩, hm⟩
      refine ⟨⟨?_, ?_⟩, ⟨m, hm.symm⟩⟩
      · rw [← hm]
        exact Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero hq.ne' (Nat.one_le_iff_ne_zero.mp hm1))
      · rw [← hm, mul_comm]
        exact (Nat.le_div_iff_mul_le hq).mp hmN
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.mul_left_cancel hq hab

end Commons.NumberTheory.Divisors