import Mathlib
import Submission.Work.SSSR.serreE1CoefIso
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
/-- **The `i`-th face of the simplex attached to a nondegenerate simplex.**  For a nondegenerate
`(d+1)`-simplex `y` of a simplicial set `Y`, the `i`-th coface of the map
`nIndexSigma Y (d+1) y : Δ[d+1] ⟶ Y` is the map attached to the nondegenerate face
`SimplicialObject.δ Y i (nIndexBase Y y)` of `y` (which is the `d`-simplex of `Y` underlying
`y`).  This is the bookkeeping that identifies the face terms of `faceD` (the alternating-face
differential on nondegenerate simplices) with the face terms `δ i ≫ σ` of a simplex
`σ = nIndexSigma Y (d+1) y`.

Suggested route: `nIndexSigma Y d y` is *definitionally* `SSet.yonedaEquiv.symm (nIndexBase Y y)`,
and Mathlib's `SSet.stdSimplex.δ_comp_yonedaEquiv_symm` gives
`SSet.stdSimplex.δ i ≫ SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm (SimplicialObject.δ Y i x)`;
so both sides are `SSet.yonedaEquiv.symm` of the same element, the RHS because
`nIndexBase Y ⟨SSet.N.mk x h, rfl⟩` is definitionally `x`. -/
theorem nIndexSigma_face {Y : SSet.{0}} {d : ℕ} (y : Work.SSSR.nIndex Y (d+1))
    (i : Fin (d+2))
    (h : SimplicialObject.δ Y i (Work.SSSR.nIndexBase Y y) ∈ Y.nonDegenerate d) :
    SSet.stdSimplex.δ i ≫ Work.SSSR.nIndexSigma Y (d+1) y
      = Work.SSSR.nIndexSigma Y d
          ⟨SSet.N.mk (SimplicialObject.δ Y i (Work.SSSR.nIndexBase Y y)) h, rfl⟩ := by
  rw [show Work.SSSR.nIndexSigma Y (d+1) y
      = SSet.yonedaEquiv.symm (Work.SSSR.nIndexBase Y y) from rfl]
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  rfl

end Work.SSSR
