import Mathlib
import Submission.Work.A7REC.Defs

/-!
# The order of the Sylow `2`-subgroup of an `A₇`-hypothesis group

`|DihedralGroup n| = 2n` (`DihedralGroup.nat_card`), so a subgroup isomorphic to the dihedral
group of order `8` has exactly `8` elements.  Applied to the hypothesis `ctx.hSdih` of the
bundle `A7RecCtx` this gives `|S| = 8`.
-/

namespace Work.A7REC.Basic

/-- A subgroup isomorphic to `DihedralGroup 4` has `8` elements, since
`|DihedralGroup n| = 2n`. -/
theorem card_eq_eight_of_mulEquiv_dihedral_4 {G : Type*} [Group G] (S : Subgroup G)
    (h : Nonempty (↥S ≃* DihedralGroup 4)) : Nat.card S = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_S (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Nat.card ((ctx.S : Subgroup G)) = 8 :=
  card_eq_eight_of_mulEquiv_dihedral_4 _ ctx.hSdih

end Work.A7REC.Basic
