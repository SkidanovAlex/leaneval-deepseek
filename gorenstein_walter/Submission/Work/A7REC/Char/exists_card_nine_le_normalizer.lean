import Mathlib

namespace Work.A7REC.Char

theorem exists_card_nine_le_normalizer {C : Type*} [Group C] [Finite C] (hC : Nat.card C = 72)
    {U : Subgroup C} (hU3 : Nat.card U = 3) :
    ∃ P : Subgroup C, Nat.card P = 9 ∧ U ≤ P ∧ P ≤ Subgroup.normalizer (U : Set C) := by
  -- `U` is a `3`-group, hence lies in a Sylow `3`-subgroup `S` of `C`.
  have hUpg : IsPGroup 3 U := IsPGroup.of_card (G := U) (p := 3) (n := 1) (by rw [hU3]; norm_num)
  obtain ⟨S, hUS⟩ := IsPGroup.exists_le_sylow (p := 3) hUpg
  -- A Sylow `3`-subgroup of a group of order `72 = 3^2 * 8` has order `9`.
  have hScard : Nat.card S = 9 := by
    rw [Sylow.card_eq_multiplicity S, hC, Nat.factorization_def 72 (p := 3) (by norm_num)]
    have h72 : (72 : ℕ) = 3 ^ 2 * 8 := by norm_num
    rw [h72, padicValNat_base_pow_mul (by norm_num : 1 < 3) (by norm_num : (8 : ℕ) ≠ 0),
      show padicValNat 3 8 = 0 by norm_num]
    norm_num
  -- `S` has order `9 = 3^2`, hence is commutative, so it centralizes (and in particular
  -- normalizes) the subgroup `U ≤ S`.
  have hSle : (S : Subgroup C) ≤ Subgroup.centralizer (U : Set C) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro h hu
    have hhS : h ∈ (S : Subgroup C) := hUS hu
    have hcomm : IsMulCommutative S :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := S) (by rw [hScard]; norm_num)
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨h, hhS⟩ ⟨s, hs⟩)
  exact ⟨(S : Subgroup C), hScard, hUS, hSle.trans (Subgroup.centralizer_le_normalizer _)⟩

end Work.A7REC.Char
