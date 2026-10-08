import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson

theorem sylow_two_complement_card_odd {M : Type} [Group M] [Finite M]
    (hnil : Group.IsNilpotent M) (T : Sylow 2 M) :
    ∃ C : Subgroup M, Subgroup.IsComplement' (T : Subgroup M) C ∧ Odd (Nat.card ↥C) ∧
      Nat.card M = Nat.card ↥T * Nat.card ↥C := by
  -- In a nilpotent group every Sylow subgroup is normal; in particular the Sylow 2-subgroup `T`
  -- is normal, so the Schur–Zassenhaus theorem applies to the pair `(|T|, [M : T])`, which is
  -- coprime because `T` is a Sylow 2-subgroup.
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent M := hnil
  haveI : (T : Subgroup M).Normal := inferInstance
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime T.card_coprime_index
  refine ⟨C, hC, ?_, hC.card_mul_card.symm⟩
  -- `C` is a complement of the normal subgroup `T`, so `|C| = [M : T]`, which is odd because it
  -- is the index of a Sylow 2-subgroup.
  have hcard : T.index = Nat.card ↥C := hC.symm.index_eq_card
  rw [← hcard]
  exact Nat.not_even_iff_odd.mp fun h => T.not_dvd_index (even_iff_two_dvd.mp h)

end Work.AppXIDickson
