import Mathlib
import Submission.Work.CORE4.A7S4
import Submission.Work.CORE4.Case2CountPieces

namespace Work.CORE4.NormTwoTransport

theorem NcardMulEquiv {A N : Type*} [Group A] [Group N] (φ : A ≃* N)
    (Y : Subgroup A) (q : ℕ) :
    {Q : Subgroup A | Nat.card ↥Q = q ∧ Y ≤ Subgroup.normalizer (Q : Set A)}.ncard =
      {Q : Subgroup N | Nat.card ↥Q = q ∧
        Y.map φ.toMonoidHom ≤ Subgroup.normalizer (Q : Set N)}.ncard := by
  classical
  -- The isomorphism `φ` transports subgroups by `Q ↦ Q.map φ`, a bijection carrying
  -- `Y ≤ N(Q)` to `Y.map φ ≤ N(Q.map φ)` and preserving `Nat.card`.
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hrange : φ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr φ.surjective
  have hle : ∀ Q : Subgroup N, Q ≤ φ.toMonoidHom.range := fun Q => by
    rw [hrange]; exact le_top
  -- Membership is transported along `Q ↦ Q.map φ`.
  have hmem : ∀ Q : Subgroup A,
      (Nat.card ↥Q = q ∧ Y ≤ Subgroup.normalizer (Q : Set A)) ↔
      (Nat.card ↥(Q.map φ.toMonoidHom) = q ∧
        Y.map φ.toMonoidHom ≤ Subgroup.normalizer (Q.map φ.toMonoidHom : Set N)) := by
    intro Q
    have hcard : Nat.card ↥(Q.map φ.toMonoidHom) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.equivMapOfInjective Q φ.toMonoidHom hinj).toEquiv.symm
    have hnorm : (Y.map φ.toMonoidHom ≤ Subgroup.normalizer (Q.map φ.toMonoidHom : Set N)) ↔
        Y ≤ Subgroup.normalizer (Q : Set A) := by
      rw [← Subgroup.map_equiv_normalizer_eq (Q : Subgroup A) φ]
      exact Subgroup.map_le_map_iff_of_injective hinj
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hcard.trans h1, hnorm.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hcard.symm.trans h1, hnorm.mp h2⟩
  -- `Q ↦ Q.map φ` is injective.
  have hg_inj : Function.Injective (fun Q : Subgroup A => Q.map φ.toMonoidHom) := by
    intro Q Q' h
    exact le_antisymm
      ((Subgroup.map_le_map_iff_of_injective hinj).mp (le_of_eq h))
      ((Subgroup.map_le_map_iff_of_injective hinj).mp (le_of_eq h.symm))
  -- The right-hand set is the image of the left-hand set.
  have himg : (fun Q : Subgroup A => Q.map φ.toMonoidHom) ''
      {Q : Subgroup A | Nat.card ↥Q = q ∧ Y ≤ Subgroup.normalizer (Q : Set A)} =
      {Q : Subgroup N | Nat.card ↥Q = q ∧
        Y.map φ.toMonoidHom ≤ Subgroup.normalizer (Q : Set N)} := by
    ext Q
    constructor
    · rintro ⟨Q', hQ', rfl⟩
      exact (hmem Q').mp hQ'
    · intro hQ
      refine ⟨Q.comap φ.toMonoidHom, (hmem _).mpr ?_, ?_⟩
      · rw [Subgroup.map_comap_eq_self (hle Q)]
        exact hQ
      · exact Subgroup.map_comap_eq_self (hle Q)
  rw [← himg]
  exact (Set.ncard_image_of_injective _ hg_inj).symm

end Work.CORE4.NormTwoTransport
