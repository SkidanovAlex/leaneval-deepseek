import Mathlib
import Submission.Work.CORE3.Defs

/-!
# The layer of a subgroup, inside `G` and inside `M`

`Work.GW2.layerIn M = (Work.GW2.layer ↥M).map M.subtype` is the layer of `M`, transported into
`G` along the inclusion `↥M →* G`.  Since that inclusion is injective, the transport is an
isomorphism of groups

`layerIn_equiv_layer : ↥(layerIn M) ≃* ↥(layer ↥M)`,

which is compatible with the centres (the centre is characteristic), hence descends to an
isomorphism of the central quotients:

`LayerInQuotientCenterIso : (↥(layerIn M) ⧸ Z(↥(layerIn M))) ≃* (↥(layer ↥M) ⧸ Z(↥(layer ↥M)))`.

This is the trivial "bookkeeping" step used when an isomorphism statement about a layer
`E(M)/Z(E(M))` is transported from the ambient group `G` to the subgroup `M` (or back).
-/

namespace Work.CORE3.A7V18

open Subgroup

/-- Transporting the layer of `M` into `G` along the inclusion `M.subtype` is an isomorphism:
`↥(layerIn M) ≃* ↥(layer ↥M)`. -/
noncomputable def layerIn_equiv_layer {G : Type} [Group G] (M : Subgroup G) :
    ↥(Work.GW2.layerIn M) ≃* ↥(Work.GW2.layer ↥M) :=
  (Subgroup.equivMapOfInjective (Work.GW2.layer ↥M) M.subtype M.subtype_injective).symm

/-- The central quotient of the layer of `M` does not depend on whether the layer is computed
in `M` or (as `layerIn M`) in the ambient group `G`. -/
theorem LayerInQuotientCenterIso {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
      (↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M))) :=
  ⟨QuotientGroup.congr (Subgroup.center ↥(Work.GW2.layerIn M))
    (Subgroup.center ↥(Work.GW2.layer ↥M)) (layerIn_equiv_layer M)
    (Subgroup.map_center_eq (layerIn_equiv_layer M))⟩

end Work.CORE3.A7V18
