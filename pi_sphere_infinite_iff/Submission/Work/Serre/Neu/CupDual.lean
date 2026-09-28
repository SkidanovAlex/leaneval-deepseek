-- PORTED COPY (neutral island) of `Submission/Work/Serre/cup_dualChainMap_shufRat.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.ezShuffleRat
import Submission.Work.Serre.ezShuffleEval
import Submission.Work.Kunneth.CrossCup
import Submission.Work.Serre.crossCochainR_eq_cup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Kronecker rule for the Eilenberg–Zilber shuffle of two spaces

For a space `W`, a space `P`, cochains `α` on `W` of degree `m` and `β` on `P` of degree `q`, and
chains `u` of `W`, `vt` of `P`, the Alexander–Whitney cup product of the pullbacks of `α` and `β`
along the two projections of `W × P` evaluates on the Eilenberg–Zilber shuffle of `u` and `vt`
as the product of the evaluations:

  `⟨π₁^*α ⌣ π₂^*β, shufRat(u, vt)⟩ = α(u) · β(vt)`.

This is the chain-level Kronecker rule for the cross product, transported from the simplicial
statement to the product of topological spaces.

## The route

* `Work.Cohomology.cupNatural` transports the cup product along a morphism of simplicial sets:
  `cup_chainComplexMap_apply` records the evaluated form
  `⟨α ⌣ β, (chainComplexMap g) c⟩ = ⟨g^*α ⌣ g^*β, c⟩`.
* `Work.Serre.crossCochainR_eq_cup` identifies the cross product of two cochains with the cup
  product of their pullbacks along the two projections of `X ⊗ Y`, and
  `Work.Serre.crossCochainR_ezBilR` is the Kronecker rule for the shuffle chain.  Together they
  give `cup_fst_snd_ezBilR`.
* `Work.Kunneth.singProdIso` is `(Functor.Monoidal.μIso TopCat.toSSet).symm`; the coherence
  `Functor.Monoidal.μ_fst`/`μ_snd` says that the projection of the product of singular simplicial
  sets is obtained from `Sing` of the projection of the product of spaces along the shuffle iso.
  This is `pullback_singProdIso_fst`/`_snd`.
-/

set_option maxHeartbeats 1600000

open CategoryTheory
open scoped MonoidalCategory Simplicial

namespace Work.Serre

noncomputable section

/-! ## Transport of the cup product along a morphism of simplicial sets -/

/-- **The evaluated form of the naturality of the cup product.**  Evaluating the cup product of
two cochains on the image of a chain under the chain map induced by a morphism `g` of simplicial
sets is evaluating the cup product of the pullbacks of the two cochains on the chain. -/
theorem cup_chainComplexMap_apply {X Y : SSet} (g : X ⟶ Y) {n m : ℕ}
    (α : Work.Cohomology.Cochain ℚ Y n) (β : Work.Cohomology.Cochain ℚ Y m)
    (c : (X.chainComplex (ModuleCat.of ℚ ℚ)).X (n + m)) :
    Work.Cohomology.cup ℚ Y α β ((SSet.chainComplexMap g (ModuleCat.of ℚ ℚ)).f (n + m) c)
      = Work.Cohomology.cup ℚ X
              (((SSet.chainComplexMap g (ModuleCat.of ℚ ℚ)).f n).hom.dualMap α)
              (((SSet.chainComplexMap g (ModuleCat.of ℚ ℚ)).f m).hom.dualMap β) c := by
  have h := congrArg (fun (φ : (X.chainComplex (ModuleCat.of ℚ ℚ)).X (n + m) →ₗ[ℚ] ℚ) => φ c)
    (Work.Cohomology.cupNatural ℚ g α β)
  simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply] using h.symm

/-! ## The Kronecker rule for the cross product -/

/-- **The Kronecker rule for the cross product of two cochains on the shuffle chain.**  If `β`
annihilates the degenerate `q`-simplices of `Y`, then the cup product of the pullbacks of `α` and
`β` along the two projections of `X ⊗ Y` evaluates on the Eilenberg–Zilber shuffle of `u` and `v`
as `α(u) · β(v)`.

This is the combination of `Work.Serre.crossCochainR_eq_cup` with the Kronecker rule
`Work.Serre.crossCochainR_ezBilR` for the shuffle chain. -/
theorem cup_fst_snd_ezBilR (X Y : SSet) (p q : ℕ)
    (α : Work.Cohomology.Cochain ℚ X p) (β : Work.Cohomology.Cochain ℚ Y q)
    (hβ : ∀ x ∈ Y.degenerate q, Work.Cohomology.genEval ℚ Y β x = 0)
    (u : (X.chainComplex (ModuleCat.of ℚ ℚ)).X p)
    (v : (Y.chainComplex (ModuleCat.of ℚ ℚ)).X q) :
    Work.Cohomology.cup ℚ (X ⊗ Y)
        (((SSet.chainComplexMap (SemiCartesianMonoidalCategory.fst X Y)
            (ModuleCat.of ℚ ℚ)).f p).hom.dualMap α)
        (((SSet.chainComplexMap (SemiCartesianMonoidalCategory.snd X Y)
            (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β)
        ((Work.Serre.ezBilR ℚ p q X Y).hom u v) = α u * β v := by
  rw [← Work.Serre.crossCochainR_eq_cup ℚ X Y p q α β]
  exact Work.Serre.crossCochainR_ezBilR ℚ X Y p q α β hβ u v

/-! ## The projection coherence of the singular simplicial set of a product -/

/-- **The first projection of a product of spaces, transported along the Eilenberg–Zilber
isomorphism.**  Pulling a cochain on `Sing W` back along the composite of the inverse of
`Work.Kunneth.singProdIso` and the singular simplicial set of the first projection is the same as
pulling it back along the first projection of `Sing W ⊗ Sing P`. -/
theorem pullback_singProdIso_fst (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (m : ℕ) (α : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj (TopCat.of W)) m) :
    ((SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
        (ModuleCat.of ℚ ℚ)).f m).hom.dualMap
      (((SSet.chainComplexMap (TopCat.toSSet.map
          (SemiCartesianMonoidalCategory.fst (TopCat.of W) (TopCat.of P)))
          (ModuleCat.of ℚ ℚ)).f m).hom.dualMap α)
    = ((SSet.chainComplexMap (SemiCartesianMonoidalCategory.fst
        (TopCat.toSSet.obj (TopCat.of W)) (TopCat.toSSet.obj (TopCat.of P)))
        (ModuleCat.of ℚ ℚ)).f m).hom.dualMap α := by
  have hcoh : (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv ≫
      TopCat.toSSet.map (SemiCartesianMonoidalCategory.fst (TopCat.of W) (TopCat.of P)) =
    SemiCartesianMonoidalCategory.fst (TopCat.toSSet.obj (TopCat.of W))
      (TopCat.toSSet.obj (TopCat.of P)) :=
    Functor.Monoidal.μ_fst TopCat.toSSet (TopCat.of W) (TopCat.of P)
  apply Work.Cohomology.cup_ext ℚ
    (TopCat.toSSet.obj (TopCat.of W) ⊗ TopCat.toSSet.obj (TopCat.of P))
  intro z
  rw [Work.Cohomology.genEval_dualMap, Work.Cohomology.genEval_dualMap,
    Work.Cohomology.genEval_dualMap]
  congr 1
  simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
    congrArg (fun φ => φ.app (Opposite.op ⦋m⦌) z) hcoh

/-- **The second projection of a product of spaces, transported along the Eilenberg–Zilber
isomorphism.**  The analogue of `pullback_singProdIso_fst` for `Prod.snd`. -/
theorem pullback_singProdIso_snd (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (q : ℕ) (β : Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj (TopCat.of P)) q) :
    ((SSet.chainComplexMap (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
        (ModuleCat.of ℚ ℚ)).f q).hom.dualMap
      (((SSet.chainComplexMap (TopCat.toSSet.map
          (SemiCartesianMonoidalCategory.snd (TopCat.of W) (TopCat.of P)))
          (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β)
    = ((SSet.chainComplexMap (SemiCartesianMonoidalCategory.snd
        (TopCat.toSSet.obj (TopCat.of W)) (TopCat.toSSet.obj (TopCat.of P)))
        (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β := by
  have hcoh : (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv ≫
      TopCat.toSSet.map (SemiCartesianMonoidalCategory.snd (TopCat.of W) (TopCat.of P)) =
    SemiCartesianMonoidalCategory.snd (TopCat.toSSet.obj (TopCat.of W))
      (TopCat.toSSet.obj (TopCat.of P)) :=
    Functor.Monoidal.μ_snd TopCat.toSSet (TopCat.of W) (TopCat.of P)
  apply Work.Cohomology.cup_ext ℚ
    (TopCat.toSSet.obj (TopCat.of W) ⊗ TopCat.toSSet.obj (TopCat.of P))
  intro z
  rw [Work.Cohomology.genEval_dualMap, Work.Cohomology.genEval_dualMap,
    Work.Cohomology.genEval_dualMap]
  congr 1
  simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
    congrArg (fun φ => φ.app (Opposite.op ⦋q⦌) z) hcoh

/-! ## The target -/

/-- **The Kronecker rule for the shuffle chain of two spaces.**  The cup product of the pullbacks
of `α` and `β` along the two projections of the product `W × P` evaluates on the Eilenberg–Zilber
shuffle of `u` and `vt` as the product `α(u) · β(vt)`. -/
theorem cup_dualChainMap_shufRat (W : Type) [TopologicalSpace W] (P : Type) [TopologicalSpace P]
    (m q : ℕ) (α : Work.Cohomology.Cochain ℚ (Work.Serre.singSSetN W) m)
    (β : Work.Cohomology.Cochain ℚ (Work.Serre.singSSetN P) q)
    (hβ : ∀ x ∈ (Work.Serre.singSSetN P).degenerate q,
      Work.Cohomology.genEval ℚ (Work.Serre.singSSetN P) β x = 0)
    (u : (Work.Cohomology.singularChains ℚ (TopCat.of W)).X m)
    (vt : (Work.Cohomology.singularChains ℚ (TopCat.of P)).X q) :
    (Work.Cohomology.cup ℚ (Work.Serre.singSSetN (W × P))
        (((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W)
            (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)).f m).hom α)
        (((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of P)
            (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)).f q).hom β))
      (Work.Serre.shufRat W P m q u vt) = α u * β vt := by
  -- Rewrite the two pulled-back cochains in the form of pullbacks along the projections of the
  -- *simplicial* product `Sing W ⊗ Sing P` (the two projections of `TopCat` coincide with
  -- `Prod.fst`/`Prod.snd` definitionally).
  have hα : ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of W)
        (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)).f m).hom α
      = ((SSet.chainComplexMap (TopCat.toSSet.map
          (SemiCartesianMonoidalCategory.fst (TopCat.of W) (TopCat.of P)))
          (ModuleCat.of ℚ ℚ)).f m).hom.dualMap α := rfl
  have hβ' : ((Work.Cohomology.dualChainMap ℚ (TopCat.of (W × P)) (TopCat.of P)
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)).f q).hom β
      = ((SSet.chainComplexMap (TopCat.toSSet.map
          (SemiCartesianMonoidalCategory.snd (TopCat.of W) (TopCat.of P)))
          (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β := rfl
  rw [hα, hβ']
  -- Unfold the shuffle: it is the transport of the simplicial shuffle along `singProdIso`.
  change (Work.Cohomology.cup ℚ (TopCat.toSSet.obj ((TopCat.of W) ⊗ (TopCat.of P)))
        (((SSet.chainComplexMap (TopCat.toSSet.map
            (SemiCartesianMonoidalCategory.fst (TopCat.of W) (TopCat.of P)))
            (ModuleCat.of ℚ ℚ)).f m).hom.dualMap α)
        (((SSet.chainComplexMap (TopCat.toSSet.map
            (SemiCartesianMonoidalCategory.snd (TopCat.of W) (TopCat.of P)))
            (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β))
      (((SSet.chainComplexMap
          (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv
          (ModuleCat.of ℚ ℚ)).f (m + q)).hom
        ((Work.Serre.ezBilR ℚ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom u vt))
      = α u * β vt
  -- Transport the cup product back along the shuffle isomorphism.
  rw [cup_chainComplexMap_apply
    (g := (Work.Kunneth.singProdIso (TopCat.of W) (TopCat.of P)).inv)
    (n := m) (m := q)
    (((SSet.chainComplexMap (TopCat.toSSet.map
        (SemiCartesianMonoidalCategory.fst (TopCat.of W) (TopCat.of P)))
        (ModuleCat.of ℚ ℚ)).f m).hom.dualMap α)
    (((SSet.chainComplexMap (TopCat.toSSet.map
        (SemiCartesianMonoidalCategory.snd (TopCat.of W) (TopCat.of P)))
        (ModuleCat.of ℚ ℚ)).f q).hom.dualMap β)
    ((Work.Serre.ezBilR ℚ m q (Work.Serre.singSSetN W) (Work.Serre.singSSetN P)).hom u vt)]
  -- Identify the transported pullbacks with the pullbacks along the simplicial projections.
  rw [pullback_singProdIso_fst W P m α, pullback_singProdIso_snd W P q β]
  exact cup_fst_snd_ezBilR _ _ m q α β hβ u vt

end

end Work.Serre
