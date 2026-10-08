import Mathlib
import Submission.Work.BSW.Cases.K4.ConjAction

open scoped Pointwise

namespace Work.BSW.Cases.K4

/-- The `L`-orbit of `Y` under the conjugation action coincides, as a set of subgroups, with
the set of subgroups of the form `Y.map (MulAut.conj l)` for `l ∈ L`. -/
theorem card_orbit_eq_card_conjSet {G : Type} [Group G] (L Y : Subgroup G) :
    Nat.card ↥(MulAction.orbit L Y) =
      Nat.card {Z : Subgroup G // ∃ l ∈ L, Z = Y.map (MulAut.conj (l : G)).toMonoidHom} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1, ?_⟩
      invFun := fun Z => ⟨Z.1, ?_⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  · obtain ⟨l, hl⟩ := x.2
    exact ⟨(l : G), l.2, hl.symm.trans (smul_eq_map_conj l Y)⟩
  · obtain ⟨l, hl, hZ⟩ := Z.2
    exact ⟨⟨l, hl⟩, (smul_eq_map_conj (⟨l, hl⟩ : L) Y).trans hZ.symm⟩

end Work.BSW.Cases.K4
