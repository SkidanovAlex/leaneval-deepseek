import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.Harmonic

open scoped BigOperators

private lemma sum_Icc_inv_sq_nat_le (a b : ℕ) (ha : 1 ≤ a) :
    (∑ n ∈ Finset.Icc a b, (1 : ℝ) / ((n : ℝ) ^ 2)) ≤ 2 / (a : ℝ) := by
  have hset : Finset.Icc a b = Finset.Ioo (a - 1) (b + 1) := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  calc
    (∑ n ∈ Finset.Icc a b, (1 : ℝ) / ((n : ℝ) ^ 2))
        = ∑ n ∈ Finset.Ioo (a - 1) (b + 1), (1 : ℝ) / ((n : ℝ) ^ 2) := by
          rw [hset]
    _ = ∑ n ∈ Finset.Ioo (a - 1) (b + 1), (((n : ℝ) ^ 2)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [one_div]
    _ ≤ (2 : ℝ) / (((a - 1 : ℕ) : ℝ) + 1) := by
          simpa using (sum_Ioo_inv_sq_le (α := ℝ) (a - 1) (b + 1))
    _ = 2 / (a : ℝ) := by
          have hnat : ((a - 1 : ℕ) + 1 : ℕ) = a := Nat.sub_add_cancel ha
          have hden : (((a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
            exact_mod_cast hnat
          rw [hden]

theorem sum_inv_sq_primes_tail_le (t : ℝ) (N : ℕ) (ht : 2 ≤ t) :
    (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
        (1 : ℝ) / (q : ℝ) ^ 2) ≤ 4 / t := by
  let m : ℕ := ⌈t⌉₊
  let S : Finset ℕ := (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ))
  let I : Finset ℕ := Finset.Icc m N
  have ht0 : 0 < t := by linarith
  have hmge_t : t ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil t
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by linarith
  have hm2nat : 2 ≤ m := by exact_mod_cast hm2
  have hm1nat : 1 ≤ m := by omega
  have hsubset : S ⊆ I := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rcases hq with ⟨hqmem, hqt⟩
    have hqmb : q ∈ (N + 1).primesBelow := by simpa [Nat.primesLE] using hqmem
    have hqlt : q < N + 1 := (Nat.mem_primesBelow.mp hqmb).1
    have hqle : q ≤ N := by omega
    have hmq : m ≤ q := by
      exact (Nat.ceil_le (a := t) (n := q)).2 hqt
    exact Finset.mem_Icc.mpr ⟨hmq, hqle⟩
  have hsum_le :
      (∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2) ≤ (∑ q ∈ I, (1 : ℝ) / (q : ℝ) ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) hsubset ?_
    intro q hqI hqnotS
    have hmq : m ≤ q := (Finset.mem_Icc.mp (by simpa [I] using hqI)).1
    have hq2 : 2 ≤ q := by omega
    have hqposnat : 0 < q := by omega
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposnat
    positivity
  have htail : (∑ q ∈ I, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 2 / (m : ℝ) := by
    simpa [I] using (sum_Icc_inv_sq_nat_le m N hm1nat)
  have hgoal1 : 2 / (m : ℝ) ≤ 2 / t := by
    exact div_le_div_of_nonneg_left (a := (2 : ℝ)) (b := (m : ℝ)) (c := t) (by norm_num) ht0 hmge_t
  have hgoal2 : (2 : ℝ) / t ≤ 4 / t := by
    rw [div_le_iff₀ ht0]
    field_simp [ne_of_gt ht0]
    norm_num
  calc
    (∑ q ∈ (Nat.primesLE N).filter (fun q : ℕ => t ≤ (q : ℝ)),
        (1 : ℝ) / (q : ℝ) ^ 2)
        = ∑ q ∈ S, (1 : ℝ) / (q : ℝ) ^ 2 := by rfl
    _ ≤ ∑ q ∈ I, (1 : ℝ) / (q : ℝ) ^ 2 := hsum_le
    _ ≤ 2 / (m : ℝ) := htail
    _ ≤ 2 / t := hgoal1
    _ ≤ 4 / t := hgoal2

end Commons.NumberTheory.Harmonic