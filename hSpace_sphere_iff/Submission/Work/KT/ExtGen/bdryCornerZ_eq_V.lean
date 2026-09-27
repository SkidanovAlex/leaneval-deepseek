import Mathlib
import Submission.Work.KT.ExtGen.bdry_aux

namespace Work.KT.ExtGen

set_option maxHeartbeats 1600000

/-- The corner augmentations of the fibre product `bdryAlg` through the `Z`-face and the `V`-face
agree: both evaluate the common corner value at `(v₀,w₀,z₀)` (using the fibre-product condition
`sliceW W Z w₀ hw₀ ∘ bdryFst = sliceW V Z v₀ hv₀ ∘ bdrySnd` evaluated at `z₀`). -/
theorem bdryCornerZ_eq_V (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryCornerZ V W Z v0 hv0 w0 hw0 z0 hz0 = bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0 := by
  apply AlgHom.ext
  intro p
  -- The fibre-product condition, read on the `Z`-face: the two descriptions of the corner
  -- agree between `bdryFst`/`bdrySnd`.
  have hfib : (sliceW W Z w0 hw0) ((bdryFst V W Z v0 hv0 w0 hw0 z0 hz0) p)
      = (sliceW V Z v0 hv0) ((bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0) p) := by
    have h := congrArg (fun q : Kpair Z × Kpair W × Kpair V => q.1) p.2
    simpa only [bdryL, bdryR, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.fst_apply,
      AlgHom.snd_apply, bdryFst_apply, bdrySnd_apply] using h
  -- The two ways of evaluating the corner `(v₀,z₀)` of a function in `prodAlg V Z`.
  have hcorner : ∀ F : prodAlg V Z, (augPair Z z0) ((sliceW V Z v0 hv0) F)
      = (augPair V v0) ((sliceV V Z z0 hz0) F) := by
    intro F
    show (F : C(Ball (V × Z), ℂ)) (pairPtD V Z v0 hv0 z0)
        = (F : C(Ball (V × Z), ℂ)) (pairPtC V Z z0 hz0 v0)
    rw [show pairPtD V Z v0 hv0 z0 = pairPtC V Z z0 hz0 v0 from Subtype.ext rfl]
  simp only [bdryCornerZ, bdryCornerV, bdryRestZ, bdryRestV, AlgHom.comp_apply]
  rw [hfib, hcorner]

end Work.KT.ExtGen
