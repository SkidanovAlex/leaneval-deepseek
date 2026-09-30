import Mathlib
import Submission.Work.DeltaHomology.SkelChain
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.Skeleton
import Submission.Work.DeltaHomology.SkeletonMap
import Submission.Work.DeltaHomology.isZero_chainX_of_dim_lt
import Submission.Work.DeltaHomology.SkelChainDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

namespace Work.DeltaHomology

/-- **The degree-`(k+1)` component of the cokernel comparison map on a basis cycle.**  The
composite of the basis chain `chainι (k+1) σ` of the `(k+1)`-skeleton with the cokernel
projection `cokernel.π (chainMap (K.skelLE (Nat.le_succ k)))` and then with the comparison
`τ₃ := cokernel.desc _ _ hzero` is the relative chain of the characteristic map `χ σ`.

Proof route (pure bookkeeping):

* `HomologicalComplex.comp_f` turns `(cokernel.π _).f (k+1) ≫ (cokernel.desc _ _ hzero).f (k+1)`
  into `(cokernel.π _ ≫ cokernel.desc _ _ hzero).f (k+1)` and `cokernel.π_desc` rewrites the
  composite of the two chain maps as `deltaChainMapSkel (k+1) ≫ relProj _ _ _`, whose
  `(k+1)`-component is `deltaChainMapSkelFun (k+1) (k+1) ≫ (relProj _ _ _).f (k+1)`;
* `DeltaSimplexMap.deltaChainMapSkelFun_chainι` computes
  `chainι (k+1) σ' ≫ deltaChainMapSkelFun (k+1) (k+1)
     = SSet.ιChainComplex _ (chiInSkelSet (k+1) le_rfl (skelMap K (k+1) σ'))`;
* finally `skelMap K (k+1) (Fin.cast (DeltaCx.skel_card_eq K (k+1) le_rfl).symm σ) = σ`
  (`skelMap_eq` plus `Fin.ext`/`simp`), which identifies the index.

Note: the goal's terms carry type `chain.X (k+1)` while `chainι`'s target is the defeq
`chainX (k+1)`, so plain `rw` may fail at `reducible` transparency; use `DeltaCx.chain_X`,
`change` or `erw` as done elsewhere in this directory. -/
theorem skelQuotient_desc_f_component {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ)
    (hzero : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
      ≫ (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) = 0)
    (σ : Fin (K.card (k + 1))) :
    (K.skel (k + 1)).chainι (k + 1) (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ)
      ≫ (cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).f (k + 1)
      ≫ (cokernel.desc (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
          (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
            ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
                {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                  (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) hzero).f (k + 1)
    = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))))
        (DeltaSimplexMap.chiInSkelSet R.toDeltaSimplexMap (k + 1) le_rfl σ)
      ≫ (relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
          {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}).f (k + 1) := by
  -- The index `Fin.cast (skel_card_eq K (k+1) le_rfl).symm σ` of the `(k+1)`-skeleton is
  -- carried by `skelMap K (k+1)` back to `σ`: this is the pure index bookkeeping that
  -- identifies the two `χ`-indices at the end.
  have hmap : skelMap K (k + 1) (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ) = σ := by
    rw [skelMap_eq K (k + 1) le_rfl]
    apply Fin.ext
    generalize_proofs
    simp only [Fin.val_cast]
  -- `HomologicalComplex.comp_f` backwards turns the composite of the two degreewise
  -- morphisms into the `(k+1)`-component of the composite of the two chain maps, and
  -- `cokernel.π_desc` evaluates `cokernel.π _ ≫ cokernel.desc _ _ hzero`.
  erw [← HomologicalComplex.comp_f, cokernel.π_desc]
  -- Now the task is purely degreewise: split off the `(k+1)`-component of
  -- `deltaChainMapSkel (k+1) ≫ relProj` and use `deltaChainMapSkelFun_chainι`.
  erw [HomologicalComplex.comp_f, DeltaSimplexMap.deltaChainMapSkel_f, ← Category.assoc,
    DeltaSimplexMap.deltaChainMapSkelFun_chainι R.toDeltaSimplexMap le_rfl, hmap]
  -- Both sides are now syntactically the same relative chain of `χ σ`.
  try rfl

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The lemma above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered).  The
statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`, which is
the name under which the rest of the project refers to it
(`Work.DeltaHomology.skelQuotient_desc_f_component`). -/
theorem skelQuotient_desc_f_component {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ)
    (hzero : DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k))
      ≫ (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
          ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
              {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) = 0)
    (σ : Fin (K.card (k + 1))) :
    (K.skel (k + 1)).chainι (k + 1) (Fin.cast (DeltaCx.skel_card_eq K (k + 1) le_rfl).symm σ)
      ≫ (cokernel.π (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))).f (k + 1)
      ≫ (cokernel.desc (DeltaCx.Hom.chainMap (K.skelLE (Nat.le_succ k)))
          (R.toDeltaSimplexMap.deltaChainMapSkel (k + 1)
            ≫ relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
                {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
                  (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}) hzero).f (k + 1)
    = SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1))))
        (DeltaSimplexMap.chiInSkelSet R.toDeltaSimplexMap (k + 1) le_rfl σ)
      ≫ (relProj ZMod (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
          {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)}).f (k + 1) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.skelQuotient_desc_f_component R k hzero σ

end Work.DeltaHomology
