import Mathlib
import Submission.Work.BSW.Cases.K4.ConjAction

open scoped Pointwise

namespace Work.BSW.Cases.K4

/-- Under the conjugation action of a subgroup `L ≤ G` on the subgroups of `G`, the stabilizer
of a subgroup `Y` is (up to the identification of an element of `L` with its image in `G`) the
intersection of the normalizer of `Y` with `L`.  In particular the two have the same cardinality.

The two subgroups live in different ambient groups (`MulAction.stabilizer L Y ≤ L` while
`Subgroup.normalizer (Y : Set G) ⊓ L ≤ G`), so we exhibit an explicit bijection between the two
underlying types and compare `Nat.card`s. -/
theorem card_stabilizer_eq_card_normalizer_inf {G : Type} [Group G] (L Y : Subgroup G) :
    Nat.card ↥(MulAction.stabilizer L Y) =
      Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓ L) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨?_, x.1.2⟩⟩
      invFun := fun y => ⟨⟨(y.1 : G), (Subgroup.mem_inf.mp y.2).2⟩, ?_⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl }
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [← smul_eq_map_conj' (x.1) Y]
    exact x.2
  · rw [MulAction.mem_stabilizer_iff, smul_eq_map_conj']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_inf.mp y.2).1

end Work.BSW.Cases.K4
