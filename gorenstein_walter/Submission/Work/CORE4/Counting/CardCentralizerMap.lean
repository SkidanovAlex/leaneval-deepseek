import Mathlib

namespace Work.CORE4.Counting

/-- The centralizer of the image of `S` under an isomorphism `φ` is the image of the
centralizer of `S`. -/
theorem centralizer_map_eq_map_centralizer {M N : Type*} [Group M] [Group N]
    (φ : M ≃* N) (S : Subgroup M) :
    Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup N) : Set N) =
      (Subgroup.centralizer (S : Set M)).map φ.toMonoidHom := by
  apply le_antisymm
  · intro n hn
    obtain ⟨m, rfl⟩ := φ.surjective n
    rw [Subgroup.mem_map]
    refine ⟨m, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : φ h * φ m = φ m * φ h :=
      hn (φ h) (by rw [Subgroup.coe_map]; exact ⟨h, hh, rfl⟩)
    exact φ.injective (by simpa using h1)
  · rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image (S : Set M) φ.toMonoidHom

theorem CardCentralizerMap {M N : Type*} [Group M] [Group N] (φ : M ≃* N) (S : Subgroup M) :
    Nat.card ↥(Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup N) : Set N)) =
      Nat.card ↥(Subgroup.centralizer (S : Set M)) := by
  rw [centralizer_map_eq_map_centralizer φ S]
  exact Subgroup.card_map_of_injective φ.injective

end Work.CORE4.Counting
