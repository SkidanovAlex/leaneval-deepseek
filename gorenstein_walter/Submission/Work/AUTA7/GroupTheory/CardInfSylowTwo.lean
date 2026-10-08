import Mathlib

namespace Work.AUTA7.GroupTheory

/- Hint: `SylowInfNormal` shows `P ⊓ L` is a Sylow `2`-subgroup of `L`; combine with
`IsPGroup.toSylow`/`Sylow.card_eq_multiplicity` (`Nat.card ↥(P ⊓ L) = 2 ^ (Nat.card L).factorization 2`)
and `Nat.card L = 2520 = 2^3 * 315`. Alternatively use `Subgroup.relIndex_mul_card` plus
`Nat.factorization`. -/
theorem CardInfSylowTwo {Q : Type*} [Group Q] [Finite Q] (L : Subgroup Q) (hL : L.Normal)
    (hcard : Nat.card L = 2520) (P : Sylow 2 Q) :
    Nat.card ↥((P : Subgroup Q) ⊓ L) = 8 := by
  classical
  -- `P ⊓ L` has odd index in `L`: indeed `[L : L ⊓ P] = [P ⊔ L : P]` and the latter
  -- divides the (odd) index `[Q : P]` of the Sylow subgroup `P`.
  have h1 : L.relIndex P * Nat.card ↥((P : Subgroup Q) ⊓ L) = Nat.card ↥(P : Subgroup Q) := by
    have h := Subgroup.relIndex_mul_card L (P : Subgroup Q)
    rwa [inf_comm] at h
  have h2 : P.relIndex (P ⊔ L) * Nat.card ↥(P : Subgroup Q) =
      Nat.card ↥((P : Subgroup Q) ⊔ L) := by
    have h := Subgroup.relIndex_mul_card (P : Subgroup Q) ((P : Subgroup Q) ⊔ L)
    rwa [inf_of_le_left le_sup_left] at h
  have h3 : L.relIndex P * Nat.card ↥L = Nat.card ↥((P : Subgroup Q) ⊔ L) := by
    have h := Subgroup.relIndex_mul_card L ((P : Subgroup Q) ⊔ L)
    rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right (P : Subgroup Q) L] at h
    exact h
  have hneLP : L.relIndex P ≠ 0 := by
    have hPpos : 0 < Nat.card ↥(P : Subgroup Q) :=
      Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩)
    obtain ⟨c, hc⟩ : L.relIndex P ∣ Nat.card ↥(P : Subgroup Q) :=
      ⟨Nat.card ↥((P : Subgroup Q) ⊓ L), h1.symm⟩
    intro h0
    rw [h0, zero_mul] at hc
    exact hPpos.ne' hc
  -- the second isomorphism theorem, in terms of relative indices
  have key : P.relIndex (P ⊔ L) * Nat.card ↥((P : Subgroup Q) ⊓ L) = Nat.card ↥L := by
    have h4 : P.relIndex (P ⊔ L) * (L.relIndex P * Nat.card ↥((P : Subgroup Q) ⊓ L))
        = L.relIndex P * Nat.card ↥L := by
      rw [h1, h3]
      exact h2
    have h4' : (P.relIndex (P ⊔ L) * Nat.card ↥((P : Subgroup Q) ⊓ L)) * L.relIndex P
        = Nat.card ↥L * L.relIndex P := by
      calc (P.relIndex (P ⊔ L) * Nat.card ↥((P : Subgroup Q) ⊓ L)) * L.relIndex P
          = P.relIndex (P ⊔ L) * (L.relIndex P * Nat.card ↥((P : Subgroup Q) ⊓ L)) := by
            ring
        _ = L.relIndex P * Nat.card ↥L := h4
        _ = Nat.card ↥L * L.relIndex P := by ring
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hneLP) h4'
  have h5 : P.relIndex L * Nat.card ↥((P : Subgroup Q) ⊓ L) = Nat.card ↥L := by
    have h := Subgroup.relIndex_mul_card ((P : Subgroup Q) ⊓ L) L
    rw [inf_of_le_left inf_le_right, Subgroup.inf_relIndex_right] at h
    exact h
  have hnePL : Nat.card ↥((P : Subgroup Q) ⊓ L) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
  have hsup : P.relIndex (P ⊔ L) = P.relIndex L :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero hnePL) (key.trans h5.symm)
  have hodd : ¬ 2 ∣ ((P : Subgroup Q) ⊓ L).relIndex L := by
    rw [Subgroup.inf_relIndex_right, ← hsup]
    intro h2dvd
    have hdvd : 2 ∣ P.index :=
      h2dvd.trans ⟨_, (Subgroup.relIndex_mul_index le_sup_left).symm⟩
    exact Sylow.not_dvd_index P hdvd
  -- `P ⊓ L` is a `2`-group of odd index in `L`, hence the order is the full `2`-part of `2520`.
  have hpg : IsPGroup 2 ↥((P : Subgroup Q) ⊓ L) :=
    IsPGroup.to_inf_left (p := 2) (K := L) P.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have hrel : ((P : Subgroup Q) ⊓ L).relIndex L * Nat.card ↥((P : Subgroup Q) ⊓ L) = 2520 := by
    have h := Subgroup.relIndex_mul_card ((P : Subgroup Q) ⊓ L) L
    rw [inf_of_le_left inf_le_right, hcard] at h
    exact h
  have hdvd : 2 ^ k ∣ 2520 := by
    refine ⟨((P : Subgroup Q) ⊓ L).relIndex L, ?_⟩
    rw [← hk, mul_comm, ← hrel]
  have hle : k ≤ 3 := by
    by_contra h
    push Not at h
    have h1 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    exact (by norm_num : ¬ (16 ∣ 2520)) (h1.trans hdvd)
  have hk3 : k = 3 := by
    interval_cases k
    · rw [hk] at hrel; norm_num at hrel; exact absurd (by omega : 2 ∣ _) hodd
    · rw [hk] at hrel; norm_num at hrel; exact absurd (by omega : 2 ∣ _) hodd
    · rw [hk] at hrel; norm_num at hrel; exact absurd (by omega : 2 ∣ _) hodd
    · rfl
  rw [hk, hk3]
  norm_num

end Work.AUTA7.GroupTheory
