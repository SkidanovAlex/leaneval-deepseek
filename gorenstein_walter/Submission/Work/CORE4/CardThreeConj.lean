import Mathlib

namespace Work.CORE4

/-- In a finite group whose order divides `3`, any two elements different from `1`
are equal or inverse to each other.  (A group of order `3` is cyclic, so its only
non-identity elements are a generator and its inverse.) -/
lemma eq_or_eq_inv_of_card_dvd_three {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 3) {x y : H} (hx : x ≠ 1) (hy : y ≠ 1) :
    y = x ∨ y = x⁻¹ := by
  have hp3 : Nat.Prime 3 := by norm_num
  -- The group is nontrivial, so its order is exactly `3`.
  have h3 : Nat.card H = 3 := by
    rcases (Nat.dvd_prime hp3).mp h with h1 | h3
    · exfalso
      have hsub : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hx (@Subsingleton.elim H hsub x 1)
    · exact h3
  -- Since `H` has prime order, `x` generates it, so `y` is a power of `x`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x ^ n = y :=
    (Submonoid.mem_powers_iff y x).mp (@mem_powers_of_prime_card H _ 3 ⟨hp3⟩ h3 x y hx)
  rw [← hn] at hy ⊢
  -- `x` has order `3`, so `y = x ^ n = x ^ (n % 3)`.
  have ho : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := dvd_trans (orderOf_dvd_natCard x) h
    rcases (Nat.dvd_prime hp3).mp hd with h1 | h3'
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact h3'
  rw [← pow_mod_orderOf x n, ho]
  have hpow : x ^ (n % 3) = x ^ n := by rw [← ho]; exact pow_mod_orderOf x n
  have hne : x ^ (n % 3) ≠ 1 := by rw [hpow]; exact hy
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · exact absurd (by rw [h0]; exact pow_zero x) hne
  · left; rw [h1, pow_one]
  · right; rw [h2]
    have hx3 : x ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one x
    have hmul : x * x ^ 2 = 1 := by rw [← pow_succ' x 2]; exact hx3
    exact eq_inv_of_mul_eq_one_right hmul

theorem CardThreeConj {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (hcard : Nat.card A ∣ 3) (g : G) (hg : g ∈ Subgroup.normalizer (A : Set G))
    (a : G) (ha : a ∈ A) :
    g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  by_cases ha1 : a = 1
  · subst ha1; simp
  · -- `g` normalizes `A`, so conjugation by `g` sends `a ∈ A` to an element of `A`.
    have hb : g * a * g⁻¹ ∈ A := ((Subgroup.mem_normalizer_iff.mp hg) a).mp ha
    have hb1 : g * a * g⁻¹ ≠ 1 := by
      intro hcon
      apply ha1
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hcon]
        _ = 1 := by group
    -- Both `a` and `g * a * g⁻¹` are non-identity elements of the group `A`,
    -- whose order divides `3`.
    have hxa : (⟨a, ha⟩ : A) ≠ 1 := by simpa using ha1
    have hxb : (⟨g * a * g⁻¹, hb⟩ : A) ≠ 1 := by simpa using hb1
    rcases eq_or_eq_inv_of_card_dvd_three hcard hxa hxb with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h

end Work.CORE4
