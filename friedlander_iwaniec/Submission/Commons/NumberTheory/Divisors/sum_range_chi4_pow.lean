import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Pow

namespace Commons.NumberTheory.Divisors

private lemma two_pow_mod_four (b : ℕ) :
    (2:ℕ)^b % 4 = if b = 0 then 1 else if b = 1 then 2 else 0 := by
  induction b using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih0 ih1 =>
    have h2 : (2:ℕ)^(n+2) % 4 = 0 := by
      rw [pow_add, Nat.mul_mod]; norm_num
    rw [h2]
    rw [if_neg (by omega : ¬ (n + 2 = 0)), if_neg (by omega : ¬ (n + 2 = 1))]

private lemma two_pow_mod_four_ne (b : ℕ) (hb : b ≠ 0) :
    (2:ℕ)^b % 4 ≠ 1 ∧ (2:ℕ)^b % 4 ≠ 3 := by
  rw [two_pow_mod_four b, if_neg hb]
  by_cases h1 : b = 1
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]; norm_num

private lemma three_pow_mod_four (j : ℕ) :
    (3:ℕ)^j % 4 = if Even j then 1 else 3 := by
  induction j using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih0 ih1 =>
    have h2 : (3:ℕ)^(n+2) % 4 = 3^n % 4 := by
      rw [pow_add, Nat.mul_mod]; norm_num
    have he : Even (n + 2) ↔ Even n := by
      rw [Nat.add_comm n 2, Nat.even_add]; simp
    rw [h2, ih0]
    by_cases hn : Even n
    · simp [he, hn]
    · simp [he, hn]

private lemma pow_mod_four_eq_of_mod_one (p : ℕ) (h : p % 4 = 1) (j : ℕ) :
    p^j % 4 = 1 := by
  rw [Nat.pow_mod p j 4, h]; norm_num

private lemma pow_mod_four_eq_of_mod_three (p : ℕ) (h : p % 4 = 3) (j : ℕ) :
    p^j % 4 = if Even j then 1 else 3 := by
  rw [Nat.pow_mod p j 4, h]; exact three_pow_mod_four j

theorem sum_range_chi4_pow (p v : ℕ) (hp : p.Prime) :
    (∑ j ∈ Finset.range (v + 1), (if p^j % 4 = 1 then (1:ℤ) else if p^j % 4 = 3 then -1 else 0))
      = (if p = 2 then 1 else if p % 4 = 1 then (v+1 : ℤ) else if Even v then 1 else 0) := by
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have h0 : ∀ b ∈ Finset.range (v + 1), b ≠ 0 →
        (if (2:ℕ)^b % 4 = 1 then (1:ℤ) else if (2:ℕ)^b % 4 = 3 then -1 else 0) = 0 := by
      intro b _ hb
      obtain ⟨h1, h3⟩ := two_pow_mod_four_ne b hb
      rw [if_neg h1, if_neg h3]
    have h1 : (0:ℕ) ∉ Finset.range (v + 1) →
        (if (2:ℕ)^0 % 4 = 1 then (1:ℤ) else if (2:ℕ)^0 % 4 = 3 then -1 else 0) = 0 :=
      fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos v)) h
    rw [Finset.sum_eq_single 0 h0 h1]
    simp
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    rcases eq_or_ne (p % 4) 1 with h1 | h1
    · have hsum : (∑ j ∈ Finset.range (v + 1),
            (if p^j % 4 = 1 then (1:ℤ) else if p^j % 4 = 3 then -1 else 0))
          = ∑ j ∈ Finset.range (v + 1), (1:ℤ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_mod_four_eq_of_mod_one p h1 j]
        simp
      rw [hsum, if_neg hp2, if_pos h1]
      simp
    · have h3 : p % 4 = 3 := by
        have ho : p % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      have hstep : ∀ j, (if p^j % 4 = 1 then (1:ℤ) else if p^j % 4 = 3 then -1 else 0)
          = if Even j then 1 else -1 := by
        intro j
        rw [pow_mod_four_eq_of_mod_three p h3 j]
        by_cases hj : Even j
        · simp [hj]
        · simp [hj]
      have hsum1 : (∑ j ∈ Finset.range (v + 1),
            (if p^j % 4 = 1 then (1:ℤ) else if p^j % 4 = 3 then -1 else 0))
          = ∑ j ∈ Finset.range (v + 1), (if Even j then (1:ℤ) else -1) :=
        Finset.sum_congr rfl (fun j _ => hstep j)
      have hsum2 : (∑ j ∈ Finset.range (v + 1), (if Even j then (1:ℤ) else -1))
          = if Even v then 1 else 0 := by
        have e1 : (∑ j ∈ Finset.range (v + 1), (if Even j then (1:ℤ) else -1))
            = ∑ j ∈ Finset.range (v + 1), (-1:ℤ)^j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [neg_one_pow_eq_ite]
        have e2 : (∑ j ∈ Finset.range (v + 1), (-1:ℤ)^j) = if Even (v+1) then 0 else 1 := by
          rw [← Fin.sum_univ_eq_sum_range (fun j => (-1:ℤ)^j) (v+1)]
          exact Fin.sum_neg_one_pow ℤ (v+1)
        rw [e1, e2]
        by_cases hv : Even v
        · rw [if_neg (fun h => (Nat.even_add_one.mp h) hv), if_pos hv]
        · rw [if_pos (Nat.even_add_one.mpr hv), if_neg hv]
      rw [hsum1, hsum2, if_neg hp2, if_neg h1]

end Commons.NumberTheory.Divisors