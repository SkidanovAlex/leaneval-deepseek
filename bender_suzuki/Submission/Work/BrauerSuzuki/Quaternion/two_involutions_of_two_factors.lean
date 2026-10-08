import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

open Multiplicative

/-- In a product of cyclic groups `ZMod (n i)` with `1 < n i` and `n i` even for every `i`,
and with at least two factors, there are two distinct elements of order `2`.

The element `n i / 2` of `ZMod (n i)` is a nonzero element killed by `2`, hence it gives an
involution in `Multiplicative (ZMod (n i))`.  Placing it in two distinct coordinates yields
two distinct involutions of the product. -/
theorem two_involutions_of_two_factors {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (hn : ∀ i, 1 < n i) (heven : ∀ i, Even (n i)) (h : Nontrivial ι) :
    ∃ x y : ((i : ι) → Multiplicative (ZMod (n i))),
      x ≠ y ∧ orderOf x = 2 ∧ orderOf y = 2 := by
  classical
  obtain ⟨i, j, hij⟩ := h.exists_pair_ne
  have hpos : ∀ k, 0 < n k := fun k => by have := hn k; omega
  have hhalf_pos : ∀ k, 0 < n k / 2 := fun k =>
    Nat.div_pos (by have := hn k; omega) (by norm_num)
  have hhalf_lt : ∀ k, n k / 2 < n k := fun k => Nat.div_lt_self (hpos k) (by norm_num)
  have hnotdvd : ∀ k, ¬ n k ∣ n k / 2 := fun k hd =>
    absurd (Nat.le_of_dvd (hhalf_pos k) hd) (not_le.mpr (hhalf_lt k))
  have hcast_ne : ∀ k, (((n k / 2 : ℕ)) : ZMod (n k)) ≠ 0 := fun k hzero =>
    hnotdvd k ((ZMod.natCast_eq_zero_iff (n k / 2) (n k)).mp hzero)
  have hmul : ∀ k, 2 * (n k / 2) = n k := fun k => Nat.mul_div_cancel' ((heven k).two_dvd)
  have hcast_dbl : ∀ k, (2 : ℕ) • (((n k / 2 : ℕ)) : ZMod (n k)) = 0 := fun k => by
    rw [nsmul_eq_mul, ← Nat.cast_mul, hmul k, ZMod.natCast_self]
  let g : (k : ι) → Multiplicative (ZMod (n k)) := fun k => ofAdd (((n k / 2 : ℕ)) : ZMod (n k))
  have hg_ne : ∀ k, g k ≠ 1 := fun k hk => by
    have hk' : ofAdd (((n k / 2 : ℕ)) : ZMod (n k)) = 1 := hk
    exact hcast_ne k (Multiplicative.ofAdd.injective (hk'.trans (ofAdd_zero).symm))
  have hg_sq : ∀ k, (g k)^2 = 1 := fun k => by
    show ofAdd (((n k / 2 : ℕ)) : ZMod (n k)) ^ 2 = 1
    rw [← ofAdd_nsmul, hcast_dbl k, ofAdd_zero]
  refine ⟨fun k => if k = i then g k else 1, fun k => if k = j then g k else 1, ?_, ?_, ?_⟩
  · intro hxy
    have h1 : (if i = i then g i else 1) = (if i = j then g i else 1) := by
      have := congr_fun hxy i; simpa using this
    have h1' : g i = 1 := by simpa [hij] using h1
    exact hg_ne i h1'
  · apply orderOf_eq_prime
    · funext k
      by_cases hk : k = i
      · simp [hk, hg_sq k]
      · simp [hk]
    · intro h1
      have h2 : g i = 1 := by
        have := congr_fun h1 i; simpa using this
      exact hg_ne i h2
  · apply orderOf_eq_prime
    · funext k
      by_cases hk : k = j
      · simp [hk, hg_sq k]
      · simp [hk]
    · intro h1
      have h2 : g j = 1 := by
        have := congr_fun h1 j; simpa using this
      exact hg_ne j h2

end Work.BrauerSuzuki.Quaternion
