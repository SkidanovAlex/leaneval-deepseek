import Mathlib
import Submission.Work.Certificates.ChainCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.CellAtlas

/-- The `(e,f)`-entry of the differential `d_{n+1,n}` of `C.toChainComplex`, evaluated on the
`e`-th basis vector, is the `(f,e)`-entry of the sparse boundary matrix `C.bd n`. -/
theorem toChainComplex_d_single (C : Work.Certificates.FinChainCx) (n : ℕ) (e : Fin (C.dim (n + 1))) (f : Fin (C.dim n)) :
    (((C.toChainComplex).d (n + 1) n).hom (Pi.single e (1 : ℤ))) f = (C.bd n).toMatrix f e := by
  simp only [Work.Certificates.FinChainCx.toChainComplex]
  rw [ChainComplex.of_d]
  change Matrix.toLin' ((C.bd n).toMatrix) (Pi.single e (1 : ℤ)) f = (C.bd n).toMatrix f e
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

end Work.MbarHomology.CellAtlas
