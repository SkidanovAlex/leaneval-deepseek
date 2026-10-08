import Mathlib

set_option linter.style.haveILetI false

namespace Work.AUTA7.A7

/-- In a finite group `Z` of order `24`, a normal subgroup of order `3` is the unique subgroup of
order `3`. Indeed, a normal subgroup of order `3` is a normal Sylow `3`-subgroup, hence contained in
every Sylow `3`-subgroup; any subgroup of order `3` is a Sylow `3`-subgroup, so it contains the
normal one, and the two coincide by cardinality. -/
theorem eq_of_card_three_of_normal_in_card_twentyfour {G : Type*} [Group G] [Finite G]
    {Z K L : Subgroup G} (hKZ : K ≤ Z) (hLZ : L ≤ Z) (hKn : (K.subgroupOf Z).Normal)
    (hK3 : Nat.card ↥K = 3) (hL3 : Nat.card ↥L = 3) (hZ : Nat.card ↥Z = 24) : K = L := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Cardinality of `K` and `L` transported to subgroups of `Z`.
  have hK' : Nat.card ↥(K.subgroupOf Z) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKZ).toEquiv, hK3]
  have hL' : Nat.card ↥(L.subgroupOf Z) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv, hL3]
  -- The multiplicity of `3` in `|Z| = 24` is one.
  have hfac : (Nat.card ↥Z).factorization 3 = 1 := by
    rw [hZ]
    rw [show (24 : ℕ) = 3 * 8 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 8)]
  -- `L` viewed in `Z` is a Sylow `3`-subgroup.
  have hLcard : Nat.card ↥(L.subgroupOf Z) = 3 ^ (Nat.card ↥Z).factorization 3 := by
    rw [hfac, pow_one, hL']
  let H : Sylow 3 ↥Z := Sylow.ofCard (L.subgroupOf Z) hLcard
  -- `K` viewed in `Z` is a normal `3`-subgroup, hence lies in every Sylow `3`-subgroup.
  have hKp : IsPGroup 3 ↥(K.subgroupOf Z) :=
    IsPGroup.of_card (n := 1) (by rw [hK']; norm_num)
  have hle : K.subgroupOf Z ≤ L.subgroupOf Z := by
    haveI : (K.subgroupOf Z).Normal := hKn
    simpa [H] using IsPGroup.le_sylow_of_normal hKp H
  have hEq : K.subgroupOf Z = L.subgroupOf Z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hK', hL'])
  rw [← Subgroup.map_subgroupOf_eq_of_le hKZ, ← Subgroup.map_subgroupOf_eq_of_le hLZ, hEq]

end Work.AUTA7.A7
