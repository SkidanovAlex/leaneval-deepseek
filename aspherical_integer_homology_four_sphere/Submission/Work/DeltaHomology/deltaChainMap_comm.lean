import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

/-- The comparison map on `Δ`-chains is a chain map: the square with vertices `C_{k+1}^Δ(K)`, `C_k^Δ(K)`, the singular chains of `X` in degrees `k+1`, `k`, commutes. `DeltaSimplexMap.deltaChainMapFun χ k = Sigma.desc (fun σ => SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ))` maps the basis simplex `σ` of the free module `K.chainX k := ∐ (fun _ : Fin (K.card k) => ℤ)` to the singular simplex `χ σ`, and `K.chainD k` is the alternating sum of the face maps. Useful lemmas: `DeltaCx.ι_chainD`, `DeltaSimplexMap.deltaChainMapFun_chainι`, `DeltaSimplexMap.face_compat`, `SSet.ιChainComplex_d`, `DeltaCx.chainX_hom_ext`. Note: `singChain ZMod X` is an abbrev for `((TopCat.toSSet.obj X).chainComplex ZMod)`, so `change`/`erw` may be needed to cross the defeq. -/
theorem deltaChainMap_comm {K : DeltaCx} {X : TopCat}
    (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.deltaChainMapFun (k + 1) ≫ (singChain Work.Homology.ZMod X).d (k + 1) k
      = K.chainD k ≫ χ.deltaChainMapFun k := by
  -- Both sides are morphisms out of the coproduct `K.chainX (k+1)`; it suffices
  -- to check them on the basis simplices `K.chainι (k+1) σ`.
  apply DeltaCx.chainX_hom_ext
  intro σ
  -- Evaluate the left-hand side: the comparison map sends `σ` to `χ σ`, and the
  -- singular boundary of a simplex is the alternating sum of its faces.
  rw [← Category.assoc, DeltaSimplexMap.deltaChainMapFun_chainι]
  erw [SSet.ιChainComplex_d]
  -- Evaluate the right-hand side: `K.chainD k = ∑_i (-1)^i d_i`.
  rw [← Category.assoc, DeltaCx.ι_chainD, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, DeltaSimplexMap.deltaChainMapFun_chainι]
  -- Both sums now have the same shape; match the terms using face compatibility.
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [χ.face_compat]
  rfl

end Work.DeltaHomology
