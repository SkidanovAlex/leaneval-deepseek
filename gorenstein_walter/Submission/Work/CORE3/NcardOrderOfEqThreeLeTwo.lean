import Mathlib

/-!
# `Work.CORE3.NcardOrderOfEqThreeLeTwo`

A group `A` of order `6` has at most two elements of order `3`.

The argument is elementary.  By Cauchy's theorem there is `a : A` with `orderOf a = 3`; let
`P = ⟨a⟩` be the cyclic subgroup it generates, so `Nat.card P = 3` and, since `Nat.card A = 6`,
`P.index = 2`.  A subgroup of index two satisfies `x * x ∈ P` for every `x`, so for `x` of order
`3` we get `x = (x * x)⁻¹ ∈ P`.  Hence every element of order `3` lies in `P`, while the identity
(which lies in `P`) has order `1 ≠ 3`.  Thus the set of elements of order `3` is a *proper* subset
of the `3`-element group `P`, so it has at most `2` elements.
-/

namespace Work.CORE3

theorem NcardOrderOfEqThreeLeTwo {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A = 6) :
    {x : A | orderOf x = 3}.ncard ≤ 2 := by
  -- Cauchy: there exists an element of order `3`, since `3 ∣ 6 = Nat.card A`.
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hcard]; norm_num)
  set P : Subgroup A := Subgroup.zpowers a with hPdef
  have hPcardNat : Nat.card P = 3 := by rw [hPdef, Nat.card_zpowers, ha]
  -- `P` has index `2` in `A`.
  have hPidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hPcardNat, hcard] at h
    omega
  -- In particular every square lies in `P`.
  have hsq : ∀ x : A, x * x ∈ P := fun x => Subgroup.mul_self_mem_of_index_two hPidx x
  -- Hence every element of order `3` lies in `P`.
  have horder3_mem : ∀ x : A, orderOf x = 3 → x ∈ P := by
    intro x hx
    have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have hxx : (x * x)⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_two, ← pow_succ]
      simpa using hx3
    rw [← hxx]
    exact P.inv_mem (hsq x)
  have hsub : {x : A | orderOf x = 3} ⊆ (P : Set A) := fun x hx => horder3_mem x hx
  -- The identity lies in `P` but is not an element of order `3`, so the inclusion is strict.
  have h1not : (1 : A) ∉ {x : A | orderOf x = 3} := by
    simp [orderOf_one]
  have hproper : {x : A | orderOf x = 3} ⊂ (P : Set A) :=
    ⟨hsub, fun hle => h1not (hle P.one_mem)⟩
  have hlt := Set.ncard_lt_ncard hproper
  have hPcard : (P : Set A).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact hPcardNat
  rw [hPcard] at hlt
  omega

end Work.CORE3
