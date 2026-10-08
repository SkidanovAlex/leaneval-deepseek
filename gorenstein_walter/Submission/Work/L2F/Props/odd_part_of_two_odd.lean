import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.sign_regular_involution

/-!
# The odd part of a group of order `2 · odd`

If `G` is a finite group whose order is divisible by `2` but not by `4`, then the elements of
odd order form a normal subgroup `K` of index `2` (`Nat.card K * 2 = Nat.card G`).

## Proof

The argument is the classical "sign of the left regular representation".  Left multiplication
turns `G` into the permutation group `MulAction.toPermHom G G`, the regular action of `G` on
itself.  Composing with the sign `Equiv.Perm.sign : Equiv.Perm G →* ℤˣ` yields a homomorphism
`φ : G →* ℤˣ`, and we show `φ g = 1 ↔ Odd (orderOf g)`:

* `orderOf (φ g)` divides both `orderOf g` (because `φ g ^ orderOf g = φ (g ^ orderOf g) = 1`)
  and `2` (because `ℤˣ = {1, -1}`); hence if `orderOf g` is odd then `φ g = 1`.
* Conversely if `orderOf g = 2 e` is even, then `u = g ^ e` is an involution, so `φ u = -1` and
  `φ g ^ e = -1`, whence `φ g ≠ 1`.

The only non-formal input is that the regular permutation of an involution in a group of order
`2 m` with `m` odd has sign `-1`: it is a fixed-point-free involution, i.e. a product of
`|G| / 2 = m` transpositions.  This is `Work.L2F.Props.sign_regular_involution`, proved in
`Submission.Work.L2F.Props.sign_regular_involution`.

Finally `φ` is surjective (an involution exists by Cauchy's theorem and maps to `-1`), so
`φ.range = ⊤ ≃ ℤˣ` has two elements and `Subgroup.card_ker_mul_card_range` gives
`Nat.card φ.ker * 2 = Nat.card G`.
-/

namespace Work.L2F.Props

theorem odd_part_of_two_odd (G : Type*) [Group G] [Finite G] (h2 : 2 ∣ Nat.card G)
    (h4 : ¬ 4 ∣ Nat.card G) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card K * 2 = Nat.card G ∧
      ∀ g : G, g ∈ K ↔ Odd (orderOf g) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h2c : 2 ∣ Fintype.card G := by rw [Fintype.card_eq_nat_card]; exact h2
  -- Write `Nat.card G = 2 * m` with `m` odd.
  obtain ⟨m, hm⟩ := h2
  have hm_odd : Odd m := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp h
    exact h4 ⟨k, by rw [hm, hk]; ring⟩
  have hcardm : Fintype.card G = 2 * m := by rw [Fintype.card_eq_nat_card]; exact hm
  -- The sign homomorphism of the left regular representation.
  let φ : G →* ℤˣ := (Equiv.Perm.sign).comp (MulAction.toPermHom G G)
  have hinv : ∀ u : G, u ^ 2 = 1 → u ≠ 1 →
      Equiv.Perm.sign (MulAction.toPermHom G G u) = -1 := fun u hu hu1 =>
    sign_regular_involution u hu hu1 m hcardm hm_odd
  -- `φ g ^ orderOf g = 1`
  have hpow : ∀ g : G, φ g ^ orderOf g = 1 := by
    intro g
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hval : ∀ g : G, φ g = 1 ∨ φ g = -1 := fun g => Int.units_eq_one_or (φ g)
  -- Odd order gives `φ g = 1`.
  have hodd_ker : ∀ g : G, Odd (orderOf g) → φ g = 1 := by
    intro g hg
    have hsq : φ g ^ 2 = 1 := by
      rcases hval g with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hd2 : orderOf (φ g) ∣ orderOf g := orderOf_dvd_of_pow_eq_one (hpow g)
    have hd1 : orderOf (φ g) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hgcd : orderOf (φ g) ∣ 1 := by
      have hh := Nat.dvd_gcd hd2 hd1
      rwa [Nat.coprime_two_right.mpr hg] at hh
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  -- Even order gives `φ g = -1`, in particular `φ g ≠ 1`.
  have heven_ker : ∀ g : G, ¬ Odd (orderOf g) → φ g ≠ 1 := by
    intro g hg
    obtain ⟨e, he⟩ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hg)
    have he_pos : 0 < e := by have := orderOf_pos g; omega
    have hsq : (g ^ e) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm e 2, ← he]; exact pow_orderOf_eq_one g
    have hne : g ^ e ≠ 1 := by
      intro h1
      have hd : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one h1
      rw [he] at hd
      have hle : 2 * e ≤ e := Nat.le_of_dvd he_pos hd
      omega
    have hsign := hinv (g ^ e) hsq hne
    have hφ : φ (g ^ e) = -1 := hsign
    have hpe : φ g ^ e = -1 := by rw [← map_pow]; exact hφ
    intro hcon
    rw [hcon, one_pow] at hpe
    have : (1 : ℤ) = -1 := congrArg (fun u : ℤˣ => (u : ℤ)) hpe
    norm_num at this
  -- An element of order `2` exists (Cauchy) and maps to `-1`, so `φ` is onto.
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := G) 2 h2c
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu; exact (by norm_num : ¬ (1 : ℕ) = 2) hu
  have hφu : φ u = -1 := hinv u hu2 hu1
  have hrange : φ.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rcases Int.units_eq_one_or x with h | h
    · rw [h]; exact MonoidHom.mem_range.mpr ⟨1, map_one φ⟩
    · rw [h]; exact MonoidHom.mem_range.mpr ⟨u, hφu⟩
  refine ⟨φ.ker, φ.normal_ker, ?_, ?_⟩
  · have hcardrange : Nat.card φ.range = 2 := by
      rw [hrange, Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv, Nat.card_eq_fintype_card]
      exact Fintype.card_units_int
    rw [← hcardrange]
    exact Subgroup.card_ker_mul_card_range φ
  · intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      by_contra hg
      exact heven_ker g hg h
    · intro hg
      exact hodd_ker g hg

end Work.L2F.Props
