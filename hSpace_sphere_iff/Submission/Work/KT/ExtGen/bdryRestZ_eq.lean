import Mathlib
import Submission.Work.KT.ExtGen.bdry_aux

namespace Work.KT.ExtGen

/-- The two descriptions of the restriction of the fibre product `bdryAlg` to the `z₀`-face agree:
the fibre-product condition (`bdryL = bdryR` on the carrier) says
`sliceW W Z w₀ hw₀ ∘ bdryFst = sliceW V Z v₀ hv₀ ∘ bdrySnd`. -/
theorem bdryRestZ_eq (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0
      = (sliceW V Z v0 hv0).comp (bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0) := by
  -- Both sides are algebra homs `bdryAlg → Kpair Z`; it suffices to check on elements.
  apply AlgHom.ext
  intro p
  -- The carrier of `bdryAlg` is defined by `bdryL = bdryR`, and the first component of that
  -- equation is precisely `sliceW W Z w₀ hw₀ ∘ bdryFst = sliceW V Z v₀ hv₀ ∘ bdrySnd` at `p`.
  exact congrArg Prod.fst p.2

end Work.KT.ExtGen
