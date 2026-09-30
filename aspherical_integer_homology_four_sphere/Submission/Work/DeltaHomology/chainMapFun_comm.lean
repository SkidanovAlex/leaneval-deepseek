import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

/-- Functoriality of the boundary with respect to a simplicial map of `Δ`-complexes: the square with vertices `C_{k+1}^Δ(K)`, `C_k^Δ(K)`, `C_{k+1}^Δ(L)`, `C_k^Δ(L)` and horizontal boundaries commutes along `chainMapFun f : K.chainX n ⟶ L.chainX n` (`chainMapFun f k = Sigma.desc (fun σ => L.chainι k (f.map σ))`), in the orientation required by `ChainComplex.ofHom`. Useful lemmas: `DeltaCx.ι_chainD`, `DeltaCx.Hom.chainMapFun_chainι`, `DeltaCx.Hom.map_face`, `DeltaCx.chainX_hom_ext`. -/
theorem chainMapFun_comm {K L : DeltaCx} (f : K.Hom L) (k : ℕ) :
    f.chainMapFun (k + 1) ≫ L.chainD k = K.chainD k ≫ f.chainMapFun k := by
  apply DeltaCx.chainX_hom_ext
  intro σ
  rw [← Category.assoc, DeltaCx.Hom.chainMapFun_chainι, DeltaCx.ι_chainD]
  rw [← Category.assoc, DeltaCx.ι_chainD, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, DeltaCx.Hom.chainMapFun_chainι]
  apply Finset.sum_congr rfl
  intro i _
  rw [f.map_face]

end Work.DeltaHomology
