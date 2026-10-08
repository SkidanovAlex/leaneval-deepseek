import Mathlib

namespace Work.L2F.PSL

/-- Conjugation by a fixed element preserves the order of the normalizer of a subgroup. -/
theorem natCard_normalizer_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (Subgroup.normalizer (H.map (MulAut.conj g).toMonoidHom : Set G)) =
      Nat.card (Subgroup.normalizer (H : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end Work.L2F.PSL
