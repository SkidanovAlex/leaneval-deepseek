import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_intpairs_eq_four_mul_natpairs_sub
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem Aseq_eq_sum_int_sqrt (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard)
      = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), (2 * Nat.sqrt (x - c ^ 4) + 1))
        + (2 * Nat.sqrt x + 1) := by
  classical
  set s := Nat.sqrt (Nat.sqrt x) with hs
  set NZ := ({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}).ncard with hNZdef
  set S1 := ∑ c ∈ Finset.Icc 1 s, Nat.sqrt (x - c ^ 4) with hS1def
  set U := ∑ c ∈ Finset.Icc 1 s, (2 * Nat.sqrt (x - c ^ 4) + 1) with hUdef
  have hrange : Finset.range (s + 1) = insert 0 (Finset.Icc 1 s) := by
    ext c; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 s := by simp [Finset.mem_Icc]
  have hsum2 : (∑ c ∈ Finset.Icc 1 s, (Nat.sqrt (x - c ^ 4) + 1)) = S1 + s := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← hS1def, Nat.card_Icc]
    simp
  have hU : U = 2 * S1 + s := by
    rw [hUdef, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ← hS1def,
      Nat.card_Icc]
    simp
  have hNZ : NZ = (Nat.sqrt x + 1) + (S1 + s) := by
    rw [hNZdef, card_sq_add_pow_four_natpairs, ← hs, hrange, Finset.sum_insert hzero]
    rw [show x - 0 ^ 4 = x by norm_num]
    rw [hsum2]
  have hZ : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard
      = 4 * NZ - 2 * Nat.sqrt x - 2 * s - 3 := by
    rw [card_intpairs_eq_four_mul_natpairs_sub, ← hNZdef, ← hs]
  rw [Aseq_eq_intpairs_ncard, hZ, hNZ, hU]
  omega

end Commons.NumberTheory.FriedlanderIwaniec
