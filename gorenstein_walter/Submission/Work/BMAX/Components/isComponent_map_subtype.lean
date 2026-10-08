import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Components

set_option linter.style.haveILetI false

namespace Work.BMAX.Components

open Subgroup

/-- `IsQuasisimple` is preserved by an injective homomorphism; here specialised to the
inclusion `↥C ↪ X` of a subgroup, the map along which a component of `C` is pushed into `X`. -/
theorem isQuasisimple_map_subtype {X : Type*} [Group X] {C : Subgroup X} {Q : Subgroup ↥C}
    (hQ : Work.GW2.IsQuasisimple Q) : Work.GW2.IsQuasisimple (Q.map C.subtype) := by
  obtain ⟨hperf, hsimp⟩ := hQ
  haveI := hsimp
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_commutator Q Q C.subtype, hperf]
  · let eE := Subgroup.equivMapOfInjective Q C.subtype C.subtype_injective
    have hcen : (Subgroup.center ↥Q).map eE.toMonoidHom
        = Subgroup.center ↥(Q.map C.subtype) := Subgroup.map_center_eq eE
    exact MulEquiv.isSimpleGroup
      (QuotientGroup.congr (Subgroup.center ↥Q)
        (Subgroup.center ↥(Q.map C.subtype)) eE hcen).symm

/-- A component of a normal subgroup `C ≤ X`, viewed in `X` along the inclusion `↥C ↪ X`, is a
component of `X`: subnormality pushes forward through the subgroup inclusion because `C` is
normal (hence subnormal) in `X`, and quasisimplicity is invariant under the injective map. -/
theorem isComponent_map_subtype {X : Type*} [Group X] {C : Subgroup X} [C.Normal]
    {Q : Subgroup ↥C} (hQ : Work.BMAX.IsComponent Q) : Work.BMAX.IsComponent (Q.map C.subtype) := by
  obtain ⟨hsub, hq⟩ := hQ
  refine ⟨?_, isQuasisimple_map_subtype hq⟩
  exact hsub.trans' (inferInstance : C.Normal).isSubnormal

end Work.BMAX.Components
