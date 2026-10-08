import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.Endgame.oddCore_map_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The odd core of a normal subgroup sits inside the odd core of the group

For a normal subgroup `L ⊴ G`, the image of `O(L) = O_{2'}(L)` under the inclusion
`↥L →* G` is a normal subgroup of `G` of odd order, hence lies in `O(G)`.

Normality is the only non-trivial point.  `O(L)` is *characteristic* in `L` (the defining
family `{N | N.Normal ∧ Odd (Nat.card N)}` is preserved as a set by every automorphism of `L`,
so its supremum is too), and conjugation by `g ∈ G` restricts to an automorphism of `L`, since
`L` is normal.  Hence `g · (O(L)) · g⁻¹ = O(L)` inside `L`, which is exactly the statement that
the image of `O(L)` in `G` is normal.
-/

namespace Work.ThreePoints

open Submission.Blueprint

/-- The image in `G` of the odd core of a normal subgroup `L` is a normal subgroup of `G`. -/
theorem map_oddCore_normal {G : Type} [Group G] (L : Subgroup G) [L.Normal] :
    ((Submission.Blueprint.oddCore ↥L).map L.subtype).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  -- `(O(L) : G).map (conj g) = O(L).map (conj g ∘ subtype)`, and `conj g ∘ subtype` factors
  -- through the automorphism of `↥L` induced by `g` (`MulAut.conjNormal`), which fixes `O(L)`.
  rw [Subgroup.map_map]
  have hcomp : ((MulAut.conj g : G ≃* G) : G →* G).comp L.subtype
      = L.subtype.comp (MulAut.conjNormal (H := L) g) := by
    ext x
    simp [MulAut.conjNormal_apply]
  rw [hcomp, ← Subgroup.map_map]
  exact congrArg (Subgroup.map L.subtype)
    (Work.Endgame.oddCore_map_mulEquiv (MulAut.conjNormal (H := L) g))

/-- The odd core of a normal subgroup, pushed into the ambient group, is contained in the odd
core of the ambient group. -/
theorem map_oddCore_le_oddCore {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal] :
    (Submission.Blueprint.oddCore ↥L).map L.subtype ≤ Submission.Blueprint.oddCore G := by
  refine Work.BrauerSuzuki.OddCore.le_of_normal_odd (map_oddCore_normal L) ?_
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact Work.BrauerSuzuki.OddCore.oddCard_oddCore

end Work.ThreePoints
