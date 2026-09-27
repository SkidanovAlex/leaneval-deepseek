import Mathlib
import Submission.Work.KT.ExtGen.bdry_aux

namespace Work.KT.ExtGen

/-- The corner augmentations of the fibre product `bdryAlg` through the `W`-face and the `V`-face
agree: both evaluate the common corner value at `(v₀,w₀,z₀)` (using the fibre-product condition
`sliceW W Z w₀ hw₀ ∘ bdryFst = sliceW V Z v₀ hv₀ ∘ bdrySnd` evaluated at `z₀`). -/
theorem bdryCornerW_eq_V (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryCornerW V W Z v0 hv0 w0 hw0 z0 hz0 = bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0 := by
  apply AlgHom.ext
  intro p
  -- The fibre-product condition, restricted to its first (`Kpair Z`) component:
  -- `sliceW W Z w₀ ∘ bdryFst = sliceW V Z v₀ ∘ bdrySnd` on `bdryAlg`.
  have hcomp : (sliceW W Z w0 hw0) (p.1.1) = (sliceW V Z v0 hv0) (p.1.2.1) := by
    have h := congrArg (fun x : Kpair Z × Kpair W × Kpair V => x.1) (p.2)
    simpa [bdryL, bdryR, AlgHom.prod_apply, AlgHom.comp_apply, AlgHom.fst_apply,
      AlgHom.snd_apply] using h
  -- Evaluate that identity at the boundary point `z₀`.
  have hval : ((p.1.1 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (pairPtD W Z w0 hw0 z0)
      = ((p.1.2.1 : prodAlg V Z) : C(Ball (V × Z), ℂ)) (pairPtD V Z v0 hv0 z0) := by
    have h := congrArg (fun H : Kpair Z => (↑H : C(Ball Z, ℂ)) z0) hcomp
    rwa [show (↑((sliceW W Z w0 hw0) (p.1.1)) : C(Ball Z, ℂ)) z0 =
        ((p.1.1 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (pairPtD W Z w0 hw0 z0) from rfl,
      show (↑((sliceW V Z v0 hv0) (p.1.2.1)) : C(Ball Z, ℂ)) z0 =
        ((p.1.2.1 : prodAlg V Z) : C(Ball (V × Z), ℂ)) (pairPtD V Z v0 hv0 z0) from rfl] at h
  -- `(w₀,z₀)` is the same point of `Ball (W×Z)` whether reached through `pairPtC` or `pairPtD`;
  -- likewise for `(v₀,z₀)` in `Ball (V×Z)`.
  calc bdryCornerW V W Z v0 hv0 w0 hw0 z0 hz0 p
      = (↑(sliceV W Z z0 hz0 (p.1.1)) : C(Ball W, ℂ)) w0 := rfl
    _ = ((p.1.1 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (pairPtC W Z z0 hz0 w0) := rfl
    _ = ((p.1.1 : prodAlg W Z) : C(Ball (W × Z), ℂ)) (pairPtD W Z w0 hw0 z0) := by congr 1
    _ = ((p.1.2.1 : prodAlg V Z) : C(Ball (V × Z), ℂ)) (pairPtD V Z v0 hv0 z0) := hval
    _ = ((p.1.2.1 : prodAlg V Z) : C(Ball (V × Z), ℂ)) (pairPtC V Z z0 hz0 v0) := by congr 1
    _ = (↑(sliceV V Z z0 hz0 (p.1.2.1)) : C(Ball V, ℂ)) v0 := rfl
    _ = bdryCornerV V W Z v0 hv0 w0 hw0 z0 hz0 p := rfl

end Work.KT.ExtGen
