import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.deltaChainMap_comm
import Submission.Work.DeltaHomology.deltaChainMapFun_natural
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The comparison chain map `Δ`-chains → singular chains

For a `Δ`-complex `K` realized in a space `X` (`DeltaSimplexMap K X`, see
`Submission/Work/DeltaHomology/RealizationDefs.lean`) we assemble the comparison
chain map

`deltaChainMap χ : C_*^Δ(K; ℤ) ⟶ C_*^{sing}(X; ℤ)`,  `σ ↦ χ σ`

and prove its naturality (chain level and homology level) with respect to
simplicial maps of `Δ`-complexes and continuous maps of realizations.

The quasi-isomorphism statement (`deltaChainMap_quasiIso`, Hatcher Theorem 2.27)
and the resulting isomorphism `deltaHomologyIso` are in
`Submission/Work/DeltaHomology/Main.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

variable {K L M : DeltaCx} {X Y Z : TopCat}

/-- The comparison chain map from the `Δ`-chains of `K` to the singular chains
of `X`: the basis simplex `σ` is sent to the singular simplex `χ σ`. -/
def DeltaSimplexMap.deltaChainMap (χ : DeltaSimplexMap K X) :
    K.chain ⟶ singChain Work.Homology.ZMod X :=
  ChainComplex.ofHom χ.deltaChainMapFun fun k => by
    rw [DeltaCx.chain_d]
    exact deltaChainMap_comm χ k

theorem DeltaSimplexMap.deltaChainMap_f (χ : DeltaSimplexMap K X) (k : ℕ) :
    χ.deltaChainMap.f k = χ.deltaChainMapFun k := rfl

attribute [simp] DeltaSimplexMap.deltaChainMap_f

/-- The comparison chain map on a basis simplex. -/
theorem DeltaSimplexMap.deltaChainMap_chainι (χ : DeltaSimplexMap K X) (k : ℕ)
    (σ : Fin (K.card k)) :
    K.chainι k σ ≫ χ.deltaChainMap.f k
      = SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ) :=
  χ.deltaChainMapFun_chainι k σ

/-- `deltaChainMap` is additive in the sense that it is a morphism of chain
complexes; in particular it is determined by its values on basis simplices. -/
theorem DeltaSimplexMap.deltaChainMap_ext {χ : DeltaSimplexMap K X}
    {φ : K.chain ⟶ singChain Work.Homology.ZMod X}
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)),
      K.chainι k σ ≫ φ.f k = SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ)) :
    φ = χ.deltaChainMap := by
  rw [← DeltaCx.chain_hom_ext (D := singChain Work.Homology.ZMod X)
    (φ := φ) (ψ := χ.deltaChainMap) fun k σ => ?_]
  rw [h k σ, DeltaSimplexMap.deltaChainMap_chainι]

/-- **Chain-level naturality of the comparison map.** A simplicial map
`f : K ⟶ L` and a continuous map `g : X ⟶ Y` commuting with the characteristic
maps (`singMap g (χ σ) = χ' (f σ)`) give a commuting square of chain maps. -/
theorem DeltaSimplexMap.deltaChainMap_natural (χ : DeltaSimplexMap K X)
    (χ' : DeltaSimplexMap L Y) (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (χ.χ k σ) = χ'.χ k (f.map σ)) :
    χ.deltaChainMap ≫ singChainMap Work.Homology.ZMod g
      = DeltaCx.Hom.chainMap f ≫ χ'.deltaChainMap := by
  apply HomologicalComplex.Hom.ext
  funext k
  simpa only [HomologicalComplex.comp_f, DeltaSimplexMap.deltaChainMap_f,
    DeltaCx.Hom.chainMap_f, DeltaCx.chain_X] using deltaChainMapFun_natural χ χ' f g h k

/-- **Naturality on homology.** Same hypotheses as
`DeltaSimplexMap.deltaChainMap_natural`; the induced square on homology
commutes. -/
theorem DeltaSimplexMap.deltaHomologyMap_natural (χ : DeltaSimplexMap K X)
    (χ' : DeltaSimplexMap L Y) (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (χ.χ k σ) = χ'.χ k (f.map σ))
    (k : ℕ) :
    HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
        ≫ HomologicalComplex.homologyMap χ'.deltaChainMap k
      = HomologicalComplex.homologyMap χ.deltaChainMap k
        ≫ singHomologyMap Work.Homology.ZMod k g := by
  calc HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
        ≫ HomologicalComplex.homologyMap χ'.deltaChainMap k
      = HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f ≫ χ'.deltaChainMap) k :=
        (HomologicalComplex.homologyMap_comp _ _ _).symm
    _ = HomologicalComplex.homologyMap
          (χ.deltaChainMap ≫ singChainMap Work.Homology.ZMod g) k := by
        rw [← DeltaSimplexMap.deltaChainMap_natural χ χ' f g h]
    _ = HomologicalComplex.homologyMap χ.deltaChainMap k
        ≫ singHomologyMap Work.Homology.ZMod k g :=
        HomologicalComplex.homologyMap_comp _ _ _

end

end Work.DeltaHomology
