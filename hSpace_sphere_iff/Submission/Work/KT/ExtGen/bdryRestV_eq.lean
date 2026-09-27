import Mathlib
import Submission.Work.KT.ExtGen.bdry_aux

namespace Work.KT.ExtGen

/-- The two descriptions of the restriction of the fibre product `bdryAlg` to the `v₀`-face agree:
the fibre-product condition says `sliceV V Z z₀ hz₀ ∘ bdrySnd = sliceV V W w₀ hw₀ ∘ bdryTrd`. -/
theorem bdryRestV_eq (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceV V W w0 hw0).comp (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0) := by
  -- The `v₀`-face restriction is literally the third component of the composite
  -- `bdryL`, while the right-hand side is the third component of `bdryR`.
  apply AlgHom.ext
  intro p
  have hp : bdryL V W Z v0 hv0 w0 hw0 z0 hz0 (p : _)
      = bdryR V W Z v0 hv0 w0 hw0 z0 hz0 (p : _) := p.2
  exact congrArg (fun q : Kpair Z × Kpair W × Kpair V => q.2.2) hp

end Work.KT.ExtGen
