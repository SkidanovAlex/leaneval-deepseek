import Mathlib

namespace Commons.NumberTheory.Nat

open Finset

/-- For `m : ℕ`, `1 / (m : ℚ) ≤ 1`. -/
lemma one_div_natCast_le_one (m : ℕ) : (1 : ℚ) / (m : ℚ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; norm_num
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast (Nat.succ_le_of_lt h)

/-- `1 - 1/m ≥ 0` for `m : ℕ`. -/
lemma one_sub_one_div_natCast_nonneg (m : ℕ) : 0 ≤ (1 : ℚ) - 1 / (m : ℚ) :=
  sub_nonneg.mpr (one_div_natCast_le_one m)

/-- For a finite set `S` of primes, the number of primes at most `S.max'` is at least `S.card`. -/
lemma card_le_count_prime_max' (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ x ∈ S, Nat.Prime x) :
    S.card ≤ Nat.count Nat.Prime (S.max' hne + 1) := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((Finset.isGreatest_max' S hne).2 hx), hS x hx⟩

/-- Main auxiliary: the product over the first `n` primes is at most the product over any
`n`-element set of primes. -/
theorem prod_range_nth_prime_le_prod :
    ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ x ∈ S, Nat.Prime x) →
      (∏ i ∈ Finset.range n, (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
        ≤ ∏ x ∈ S, (1 - (1 : ℚ) / (x : ℚ)) := by
  intro n
  induction n with
  | zero =>
    intro S hcard hS
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | succ k ih =>
    intro S hcard hS
    have hne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.succ_pos k)
    have hMmem : S.max' hne ∈ S := Finset.max'_mem S hne
    have hMle : ∀ x ∈ S, x ≤ S.max' hne := (Finset.isGreatest_max' S hne).2
    have hcard' : (S.erase (S.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hMmem, hcard]
      omega
    have hS' : ∀ x ∈ S.erase (S.max' hne), Nat.Prime x :=
      fun x hx => hS x (Finset.mem_of_mem_erase hx)
    have ih' := ih (S.erase (S.max' hne)) hcard' hS'
    have hcount := card_le_count_prime_max' S hne hS
    have hk_lt : k < Nat.count Nat.Prime (S.max' hne + 1) := by
      rw [hcard] at hcount
      omega
    have hpM : (Nat.nth Nat.Prime k : ℕ) ≤ S.max' hne := by
      have := Nat.nth_lt_of_lt_count hk_lt
      omega
    have hstep : (1 : ℚ) - 1 / ((Nat.nth Nat.Prime k : ℕ) : ℚ)
        ≤ 1 - 1 / ((S.max' hne : ℕ) : ℚ) := by
      have hprime : Nat.Prime (Nat.nth Nat.Prime k) :=
        Nat.nth_mem_of_infinite (p := Nat.Prime) Nat.infinite_setOfPred_prime k
      have hpos : (0 : ℚ) < ((Nat.nth Nat.Prime k : ℕ) : ℚ) := by
        have h0 : (0 : ℕ) < Nat.nth Nat.Prime k := by
          have := hprime.two_le; omega
        exact_mod_cast h0
      have hle : ((Nat.nth Nat.Prime k : ℕ) : ℚ) ≤ ((S.max' hne : ℕ) : ℚ) := by
        exact_mod_cast hpM
      have hdiv : 1 / ((S.max' hne : ℕ) : ℚ) ≤ 1 / ((Nat.nth Nat.Prime k : ℕ) : ℚ) :=
        one_div_le_one_div_of_le hpos hle
      linarith
    have hfn_nonneg : (0 : ℚ) ≤ 1 - 1 / ((Nat.nth Nat.Prime k : ℕ) : ℚ) :=
      one_sub_one_div_natCast_nonneg _
    have hprod_nonneg : (0 : ℚ) ≤ ∏ x ∈ S.erase (S.max' hne), (1 - (1 : ℚ) / (x : ℚ)) :=
      Finset.prod_nonneg (fun x _ => one_sub_one_div_natCast_nonneg x)
    calc
      (∏ i ∈ Finset.range (Nat.succ k), (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
          = (∏ i ∈ Finset.range k, (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
              * (1 - (1 : ℚ) / ((Nat.nth Nat.Prime k : ℕ) : ℚ)) :=
            Finset.prod_range_succ _ k
      _ ≤ (∏ x ∈ S.erase (S.max' hne), (1 - (1 : ℚ) / (x : ℚ)))
              * (1 - (1 : ℚ) / ((S.max' hne : ℕ) : ℚ)) :=
            mul_le_mul ih' hstep hfn_nonneg hprod_nonneg
      _ = ∏ x ∈ S, (1 - (1 : ℚ) / (x : ℚ)) := by
            rw [Finset.prod_erase_mul S (fun x => (1 : ℚ) - 1 / (x : ℚ)) hMmem]

theorem prod_one_sub_inv_ge_ithPrime (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) :
    (∏ i ∈ Finset.range S.card, (1 - (1 : ℚ) / ((Nat.nth Nat.Prime i : ℕ) : ℚ)))
      ≤ ∏ x ∈ S, (1 - (1 : ℚ) / (x : ℚ)) :=
  prod_range_nth_prime_le_prod S.card S rfl hS

end Commons.NumberTheory.Nat
