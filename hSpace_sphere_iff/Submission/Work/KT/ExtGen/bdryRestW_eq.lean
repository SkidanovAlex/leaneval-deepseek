import Mathlib
import Submission.Work.KT.ExtGen.bdry_aux

namespace Work.KT.ExtGen

/-- The two descriptions of the restriction of the fibre product `bdryAlg` to the `w₀`-face agree:
the fibre-product condition says `sliceV W Z z₀ hz₀ ∘ bdryFst = sliceW V W v₀ hv₀ ∘ bdryTrd`. -/
theorem bdryRestW_eq (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceW V W v0 hv0).comp (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0) := by
  apply AlgHom.ext
  intro p
  -- `p.2` is the fibre-product condition `bdryL p = bdryR p`; its `(Kpair W)` component is
  -- exactly the claim.
  have h := congrArg Prod.fst (congrArg Prod.snd p.2)
  simpa [bdryRestW, bdryFst, bdryTrd, bdryL, bdryR, AlgHom.prod_apply, AlgHom.comp_apply,
    AlgHom.fst_apply, AlgHom.snd_apply] using h

end Work.KT.ExtGen
