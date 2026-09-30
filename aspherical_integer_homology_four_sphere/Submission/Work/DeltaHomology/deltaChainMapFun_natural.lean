import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Homology Work.DeltaHomology

/-- The singular chain map induced by a continuous map `g : X ⟶ Y`, evaluated on
the summand of a singular simplex: the basis element `s` of `C_k(X)` is sent to
the basis element `singMap g s` of `C_k(Y)`.

This is the `singChain`-flavoured form of `SSet.ι_chainComplexMap_f`, and is the
key computation that lets one move the comparison map `Δ`-chains → singular
chains past a continuous map. -/
theorem singChainMap_ι_apply {X Y : TopCat} (g : X ⟶ Y) {k : ℕ}
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))) :
    (TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod) s
        ≫ (singChainMap Work.Homology.ZMod g).f k
      = (TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod) (singMap g s) := by
  change (TopCat.toSSet.obj X).ιChainComplex s ≫
      (SSet.chainComplexMap (TopCat.toSSet.map g) Work.Homology.ZMod).f k
      = (TopCat.toSSet.obj Y).ιChainComplex (singMap g s)
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Naturality of the degree-`k` component of the comparison chain map `Δ`-chains → singular chains with respect to a simplicial map `f : K ⟶ L` of `Δ`-complexes and a continuous map `g : X ⟶ Y` of their realizations (or of any two spaces carrying simplex maps) commuting on the characteristic maps: `singMap g (χ σ) = χ' (f σ)` for all `σ`. Here `DeltaSimplexMap.deltaChainMapFun χ k = Sigma.desc (fun σ => SSet.ιChainComplex (TopCat.toSSet.obj X) (χ.χ k σ))`, `DeltaCx.Hom.chainMapFun f k = Sigma.desc (fun σ => L.chainι k (f.map σ))`, and `singChainMap` is the map induced on singular chains. Useful lemmas: `DeltaSimplexMap.deltaChainMapFun_chainι`, `DeltaCx.Hom.chainMapFun_chainι`, `SSet.ι_chainComplexMap_f`, `DeltaCx.chainX_hom_ext`. Note: `singChainMap ZMod g` and `singMap g` are abbrevs/defs unfolding to the `SSet.chainComplexMap`/`TopCat.toSSet.map` of `g`, so `change` may be needed to cross the defeq. -/
theorem deltaChainMapFun_natural {K L : DeltaCx} {X Y : TopCat}
    (χ : DeltaSimplexMap K X) (χ' : DeltaSimplexMap L Y) (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (χ.χ k σ) = χ'.χ k (f.map σ))
    (k : ℕ) :
    χ.deltaChainMapFun k ≫ (singChainMap Work.Homology.ZMod g).f k
      = f.chainMapFun k ≫ χ'.deltaChainMapFun k := by
  -- Both sides are morphisms out of a coproduct; it suffices to check them on
  -- the basis elements `K.chainι k σ`.
  apply DeltaCx.chainX_hom_ext
  intro σ
  have step1 : K.chainι k σ ≫ (χ.deltaChainMapFun k ≫ (singChainMap Work.Homology.ZMod g).f k)
      = (TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod) (χ.χ k σ)
          ≫ (singChainMap Work.Homology.ZMod g).f k := by
    rw [← Category.assoc, DeltaSimplexMap.deltaChainMapFun_chainι]
    rfl
  have step2 : (TopCat.toSSet.obj X).ιChainComplex (R := Work.Homology.ZMod) (χ.χ k σ)
        ≫ (singChainMap Work.Homology.ZMod g).f k
      = (TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod)
          (singMap g (χ.χ k σ)) :=
    singChainMap_ι_apply g (χ.χ k σ)
  have step3 : (TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod)
        (singMap g (χ.χ k σ))
      = (TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod) (χ'.χ k (f.map σ)) := by
    rw [h k σ]
  have step4 : (TopCat.toSSet.obj Y).ιChainComplex (R := Work.Homology.ZMod) (χ'.χ k (f.map σ))
      = L.chainι k (f.map σ) ≫ χ'.deltaChainMapFun k :=
    (DeltaSimplexMap.deltaChainMapFun_chainι χ' k (f.map σ)).symm
  have step5 : L.chainι k (f.map σ) ≫ χ'.deltaChainMapFun k
      = (K.chainι k σ ≫ f.chainMapFun k) ≫ χ'.deltaChainMapFun k := by
    rw [DeltaCx.Hom.chainMapFun_chainι]
  have step6 : (K.chainι k σ ≫ f.chainMapFun k) ≫ χ'.deltaChainMapFun k
      = K.chainι k σ ≫ (f.chainMapFun k ≫ χ'.deltaChainMapFun k) := by
    rw [Category.assoc]
  exact step1.trans (step2.trans (step3.trans (step4.trans (step5.trans step6))))

end Work.DeltaHomology
