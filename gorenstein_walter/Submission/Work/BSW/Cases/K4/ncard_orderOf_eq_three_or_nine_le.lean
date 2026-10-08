import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- For a finite group `G` of order `360` with exactly `10` Sylow `3`-subgroups, the number of
elements of order `3` or `9` is at most `80`.

Every Sylow `3`-subgroup has order `3² = 9` (`Sylow.card_eq_multiplicity`, `360 = 2³·3²·5`), hence
consists of the identity together with `8` elements of order `3` or `9`; every element of order `3`
or `9` generates a cyclic `3`-subgroup, contained in some Sylow `3`-subgroup
(`IsPGroup.exists_le_sylow`).  So the set of elements of order `3` or `9` is contained in the union
of the nonidentity parts of the Sylow `3`-subgroups, and a union bound
(`Set.ncard_iUnion_le_of_fintype`, `Set.ncard_le_ncard`) gives `≤ 8 · 10 = 80`. -/
theorem ncard_orderOf_eq_three_or_nine_le {G : Type} [Group G] [Finite G] (hG : Nat.card G = 360)
    (hn3 : Nat.card (Sylow 3 G) = 10) :
    {x : G | orderOf x = 3 ∨ orderOf x = 9}.ncard ≤ 80 := by
  classical
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  -- Every Sylow `3`-subgroup has order `9`.
  have hPcard : ∀ P : Sylow 3 G, Nat.card ↥(P : Subgroup G) = 9 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num [Nat.factorization]
  -- Each Sylow `3`-subgroup contributes at most its `8` nonidentity elements.
  have hPle : ∀ P : Sylow 3 G,
      ({x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1}).ncard ≤ 8 := by
    intro P
    have hproper :
        {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1} ⊂ ((P : Subgroup G) : Set G) := by
      refine ⟨fun x hx => hx.1, ?_⟩
      intro hsub
      have h1 : (1 : G) ∈ {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1} := hsub P.one_mem
      exact h1.2 rfl
    have hlt := Set.ncard_lt_ncard hproper
    have hcoeeq : ((P : Subgroup G) : Set G).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]
      exact hPcard P
    rw [hcoeeq] at hlt
    omega
  -- Every element of order `3` or `9` lies in the nonidentity part of some Sylow `3`-subgroup.
  have hsub : {x : G | orderOf x = 3 ∨ orderOf x = 9} ⊆
      ⋃ (P : Sylow 3 G), {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1} := by
    intro x hx
    have hne1 : x ≠ 1 := by
      rintro rfl
      rcases hx with h | h <;> simp at h
    have hcard : Nat.card ↥(Subgroup.zpowers x) = 3 ∨ Nat.card ↥(Subgroup.zpowers x) = 9 := by
      rcases hx with h | h
      · exact Or.inl (by rw [Nat.card_zpowers, h])
      · exact Or.inr (by rw [Nat.card_zpowers, h])
    have hp : IsPGroup 3 ↥(Subgroup.zpowers x) := by
      rcases hcard with h | h
      · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
      · exact IsPGroup.of_card (n := 2) (by rw [h]; norm_num)
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    exact Set.mem_iUnion.mpr ⟨Q, hQ (Subgroup.mem_zpowers x), hne1⟩
  calc {x : G | orderOf x = 3 ∨ orderOf x = 9}.ncard
      ≤ (⋃ (P : Sylow 3 G), {x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1}).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ ∑ P : Sylow 3 G, ({x : G | x ∈ (P : Subgroup G) ∧ x ≠ 1}).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _P : Sylow 3 G, 8 := Finset.sum_le_sum (fun P _ => hPle P)
    _ = 80 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hn3, nsmul_eq_mul]
        norm_num

end Work.BSW.Cases.K4
