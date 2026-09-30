import Mathlib
import Submission.Work.DeltaHomology.CellClassMap
import Submission.Work.DeltaHomology.SkelChainDefs
import Submission.Work.DeltaHomology.CellData
import Submission.Work.HomologyExtra.RelChainMapFunctor
import Submission.Work.HomologyExtra.SimplexClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- **The relative chain of the identity simplex of `Δⁿ` maps to the relative chain of `χ σ`.**

`simplexRelChain n` is the class of the identity simplex `ιₙ` in `Cₙ(Δⁿ, ∂Δⁿ)`, and the pair map
`Ψ := (R.skelPunctPairHom n σ).comp (pairHomOfSubset _)` is the inclusion-induced map
`(Δⁿ, ∂Δⁿ) → (Xⁿ, Xⁿ ∖ {barycentres})` given by `χ σ`.  The claim is that
`(relChainMap ZMod Ψ).f n` carries `[ιₙ]` to the relative chain of the singular simplex
`χ.clsInSkelSet n le_rfl σ`, i.e. that the two sides (morphisms `ZMod ⟶ (relChain _ _ _).X n`)
are literally equal — no boundary correction is needed.

Proof route:

* `simplexRelChain n = simplexIdChain n ≫ (relProj _ (simplex n) (simplexBoundary n)).f n`
  (`rfl`), and `simplexIdChain n = SSet.ιChainComplex (TopCat.toSSet.obj (simplex n)) (simplexId n)`
  (`Work.HomologyExtra.Basic`);
* `relChainMap_comp_relProj` (at degree `n`, via `HomologicalComplex.comp_f`) rewrites
  `(relProj _ _ _).f n ≫ (relChainMap ZMod Ψ).f n` as
  `(singChainMap ZMod Ψ.hom).f n ≫ (relProj _ _ _).f n`;
* `singChainMap ZMod f` is definitionally `SSet.chainComplexMap (TopCat.toSSet.map f) ZMod`
  (unfold `AlgebraicTopology.singularChainComplexFunctor`), so `SSet.ι_chainComplexMap_f` gives
  `simplexIdChain n ≫ (singChainMap ZMod Ψ.hom).f n
     = SSet.ιChainComplex _ ((TopCat.toSSet.map Ψ.hom).app _ (simplexId n))`;
* it remains to identify the singular simplex: `Ψ.hom = TopCat.ofHom (R.toDeltaSimplexMap.clsInSkelSet n le_rfl σ)`
  (since `pairHomOfSubset`'s `hom` is `𝟙`; see `pairHomOfSubset_hom`, `skelPunctPairHom_hom`), so
  `(TopCat.toSSetObjEquiv _ _) ((TopCat.toSSet.map Ψ.hom).app _ (simplexId n)) = Ψ.hom
     = R.toDeltaSimplexMap.clsInSkelSet n le_rfl σ
     = (TopCat.toSSetObjEquiv _ _) (chiInSkelSet n le_rfl σ)`,
  using `toSSetObjEquiv_map_apply`, `toSSetObjEquiv_simplexId`, `toSSetObjEquiv_simplexOf` and
  `clsInSkelSet_coe`; conclude by injectivity of `TopCat.toSSetObjEquiv` (or use
  `Work.HomologyExtra.toSSet_map_simplexId`). -/
theorem simplexRelChain_relChainMap_chiInSkelSet {K : DeltaCx} {X : TopCat}
    (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    (Work.HomologyExtra.simplexRelChain n) ≫
      (relChainMap ZMod ((R.skelPunctPairHom n σ).comp
        (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex n)))).f n
    = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (R.toDeltaSimplexMap.skelSet n)))
        (DeltaSimplexMap.chiInSkelSet R.toDeltaSimplexMap n le_rfl σ)
      ≫ (relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet n))
          {x : ↥(R.toDeltaSimplexMap.skelSet n) |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel n}).f n := by
  -- `simplexRelChain` is, by definition, the identity chain followed by the projection.
  rw [Work.HomologyExtra.simplexRelChain]
  -- Reassociate and combine the degree-`n` components into the degree-`n` component of the
  -- composite of chain maps `(relProj) ≫ (relChainMap _ Ψ)`.
  erw [Category.assoc]
  erw [← HomologicalComplex.comp_f]
  -- Replace that composite by `(singChainMap _ Ψ.hom) ≫ (relProj)`, using the defining property
  -- of the map induced on relative chains by a map of pairs.
  erw [← Work.Homology.relChainMap_comp_relProj Work.Homology.ZMod
      ((R.skelPunctPairHom n σ).comp
        (Work.DeltaHomology.pairHomOfSubset (Work.DeltaHomology.stdSimplexBoundary_subset_punctStdSimplex n)))]
  erw [HomologicalComplex.comp_f]
  erw [← Category.assoc]
  congr 1
  -- It remains to identify the two chains `simplexIdChain n ≫ (singChainMap _ Ψ.hom).f n`
  -- and `SSet.ιChainComplex _ (chiInSkelSet n le_rfl σ)`.
  rw [show (Work.Homology.singChainMap Work.Homology.ZMod
        ((R.skelPunctPairHom n σ).comp
        (Work.DeltaHomology.pairHomOfSubset (Work.DeltaHomology.stdSimplexBoundary_subset_punctStdSimplex n))).hom)
      = SSet.chainComplexMap (TopCat.toSSet.map ((R.skelPunctPairHom n σ).comp
        (Work.DeltaHomology.pairHomOfSubset (Work.DeltaHomology.stdSimplexBoundary_subset_punctStdSimplex n))).hom) Work.Homology.ZMod from rfl]
  rw [show Work.HomologyExtra.simplexIdChain n = SSet.ιChainComplex (TopCat.toSSet.obj (Work.HomologyExtra.simplex n)) (Work.HomologyExtra.simplexId n) from rfl]
  erw [SSet.ι_chainComplexMap_f]
  -- The image of the identity simplex under `χ σ` is precisely `chiInSkelSet n le_rfl σ`.
  congr 1

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The lemma above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered).  The
statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`, which is
the name under which the rest of the project refers to it
(`Work.DeltaHomology.simplexRelChain_relChainMap_chiInSkelSet`). -/
theorem simplexRelChain_relChainMap_chiInSkelSet {K : DeltaCx} {X : TopCat}
    (R : DeltaRealization K X) (n : ℕ) (σ : Fin (K.card n)) :
    (Work.HomologyExtra.simplexRelChain n) ≫
      (relChainMap ZMod ((R.skelPunctPairHom n σ).comp
        (pairHomOfSubset (stdSimplexBoundary_subset_punctStdSimplex n)))).f n
    = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (R.toDeltaSimplexMap.skelSet n)))
        (DeltaSimplexMap.chiInSkelSet R.toDeltaSimplexMap n le_rfl σ)
      ≫ (relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet n))
          {x : ↥(R.toDeltaSimplexMap.skelSet n) |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel n}).f n :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.simplexRelChain_relChainMap_chiInSkelSet R n σ

end Work.DeltaHomology
