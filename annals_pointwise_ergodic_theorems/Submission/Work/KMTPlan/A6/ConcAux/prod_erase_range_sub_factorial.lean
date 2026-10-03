import Mathlib

namespace Work.KMTPlan.A6.ConcAux

open Finset

/-- The product of `n - j` over `j ∈ {0, …, n-1}` equals `n!`. -/
theorem prod_range_self_sub (n : ℕ) :
    ∏ j ∈ Finset.range n, ((n : ℤ) - (j : ℤ)) = (n.factorial : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ']
    have hprod : (∏ k ∈ Finset.range n, (((n + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)))
        = ∏ k ∈ Finset.range n, ((n : ℤ) - (k : ℤ)) := by
      apply Finset.prod_congr rfl
      intro k _
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hprod, ih, Nat.factorial_succ, Nat.cast_mul]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring

/-- The main identity, with the induction on `d` exposed. -/
theorem prod_erase_aux : ∀ d : ℕ, ∀ i, i ≤ d →
    ∏ j ∈ (Finset.range (d + 1)).erase i, ((i : ℤ) - (j : ℤ))
      = (-1 : ℤ) ^ (d - i) * ((i.factorial : ℤ) * ((d - i).factorial : ℤ)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hiz : i = 0 := Nat.eq_zero_of_le_zero hi
    subst hiz
    simp
  | succ d ih =>
    intro i hi
    by_cases h : i = d + 1
    · subst i
      rw [Finset.range_add_one, Finset.erase_insert (Finset.notMem_range_self)]
      rw [prod_range_self_sub (d + 1)]
      simp
    · have hle : i ≤ d := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (a := d + 1) (b := i) (by omega)]
      rw [Finset.prod_insert (a := d + 1) (s := (Finset.range (d + 1)).erase i)
        (by rw [Finset.mem_erase]; intro hh; exact absurd hh.2 Finset.notMem_range_self)]
      rw [ih i hle]
      have hD : (d + 1) - i = (d - i) + 1 := by omega
      have hsub : (i : ℤ) - ((d + 1 : ℕ) : ℤ) = -(((d - i) + 1 : ℕ) : ℤ) := by
        have h1 : ((d + 1 : ℕ) : ℤ) = (i : ℤ) + (((d - i) + 1 : ℕ) : ℤ) := by
          have h2 : (d + 1 : ℕ) = i + ((d - i) + 1) := by omega
          rw [h2, Nat.cast_add]
        rw [h1]; ring
      rw [hD, hsub, Nat.factorial_succ, pow_succ, Nat.cast_mul]
      ring

theorem prod_erase_range_sub_factorial (d i : ℕ) (hi : i ≤ d) :
    ∏ j ∈ (Finset.range (d + 1)).erase i, ((i : ℤ) - (j : ℤ))
      = (-1 : ℤ) ^ (d - i) * ((i.factorial : ℤ) * ((d - i).factorial : ℤ)) :=
  prod_erase_aux d i hi

end Work.KMTPlan.A6.ConcAux
