import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.GroupWithZero.Action.End
import Submission.Work.AbsoluteKummer.Coefficients
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTfin

/-- If the action of `G` on `M` is discrete (every point stabiliser is open), then so is the
restricted action of any subgroup `S ≤ G`, where `S` carries the subspace topology and acts
through the inclusion `S.subtype : S →* G`. -/
theorem isDiscreteModule_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    (S : Subgroup G) {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (h : Work.AbsoluteKummer.IsDiscreteModule G M) :
    letI : DistribMulAction ↥S M := DistribMulAction.compHom M S.subtype
    Work.AbsoluteKummer.IsDiscreteModule ↥S M := by
  intro m
  -- The stabiliser of `m` in `S` is the preimage of the stabiliser of `m` in `G`
  -- along the continuous inclusion `S.subtype`.
  convert (h m).preimage
    (continuous_subtype_val : Continuous (S.subtype : ↥S → G)) using 1
  ext s
  simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact Iff.rfl

end Work.SSGRoute.PTfin
