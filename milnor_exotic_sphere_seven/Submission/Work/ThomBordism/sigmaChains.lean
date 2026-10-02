import Mathlib
import Submission.Work.ThomBordism.sigmaSSetIso
import Submission.Work.Bordism.chainC_coprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The singular chain complex of a `σ`-type of spaces is the biproduct of the pieces

This file lifts `Work.ThomBordism.ssetSigmaIso` (the singular simplicial set of a `σ`-type is the
coproduct of the singular simplicial sets of the pieces) to the level of singular **chains**, using
that `chainC ℤ` preserves all colimits (`Work.Bordism.chainC_preservesColimitsOfShape`) and that a
coproduct of a finite family in an additive category is its biproduct.

The main output is a family of *retractions*

`chainSigmaRetract α i : chainC ℤ (Σ i, Y i) ⟶ chainC ℤ (Y i)`

with `chainMap (sigmaι i) ≫ chainSigmaRetract i = 𝟙`, `chainMap (sigmaι j) ≫ chainSigmaRetract i
= 0` for `j ≠ i`, and `∑ i, chainSigmaRetract i ≫ chainMap (sigmaι i) = 𝟙`.  These are the chain
maps whose transposes give the cohomological splitting of the disjoint union.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Limits Topology

namespace Work.ThomBordism

noncomputable section

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type} [Fintype ι] (α : ι → TopCat.{0})

/-- The singular chain complex functor `chainC ℤ` on simplicial sets. -/
abbrev ssetChainCFunctor : SSet ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The singular chain complex of the `i`-th piece.  (It is the singular chain complex of the
topological space `α i`; we use `singularChains` rather than `chainC` so that the chain maps
induced by continuous maps have exactly this type.) -/
abbrev pieceChains (i : ι) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ (α i)

/-- The singular chain complex of the whole `σ`-type. -/
abbrev sigmaChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ (TopCat.of (Σ i, α i))

/-- The cofan in chain complexes with point `chainC ℤ (Σ i, α i)` and legs the chain maps induced
by the inclusions. -/
noncomputable def chainSigmaCofan : Cofan (fun i => pieceChains α i) :=
  Cofan.mk (sigmaChains α) (fun i => Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i))
    (TopCat.sigmaι α i))

/-- **The chain-level cofan is colimiting.**  It is the image under the colimit-preserving functor
`chainC ℤ` of the colimiting cofan `ssetSigmaCofan α`, transported across the identification
`Discrete.functor f ⋙ G ≅ Discrete.functor (G.obj ∘ f)`. -/
noncomputable def chainSigmaCofan_isColimit : IsColimit (chainSigmaCofan α) := by
  haveI : PreservesColimitsOfShape (Discrete ι) ssetChainCFunctor :=
    Work.Bordism.chainC_preservesColimitsOfShape (J := Discrete ι)
  have h := isColimitOfPreserves (ssetChainCFunctor)
    (ssetSigmaCofan_isColimit α)
  refine (IsColimit.equivOfNatIsoOfIso
    (α := Discrete.compNatIsoDiscrete (fun i => TopCat.toSSet.obj (α i)) (ssetChainCFunctor))
    (ssetChainCFunctor.mapCocone (ssetSigmaCofan α)) (chainSigmaCofan α) ?_).1 h
  refine Cocone.ext (Iso.refl _) (fun j => ?_)
  rcases j with ⟨i⟩
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Iso.refl_hom, Category.comp_id,
    Discrete.compNatIsoDiscrete_inv_app, Category.id_comp, Functor.mapCocone_ι_app,
    Cofan.mk_ι_app, chainSigmaCofan, ssetSigmaCofan, Work.Cohomology.chainMap,
    ssetChainCFunctor]
  rfl

/-- **The singular chain complex of a `σ`-type is the biproduct of the chain complexes of the
pieces**, compatibly with the inclusions. -/
noncomputable def chainSigmaIso : sigmaChains α ≅ ⨁ (fun i => pieceChains α i) :=
  IsColimit.coconePointUniqueUpToIso (chainSigmaCofan_isColimit α)
    (biproduct.isColimit (fun i => pieceChains α i))

/-- **The defining property of `chainSigmaIso`**: it carries the chain map induced by the inclusion
of the `i`-th piece to the `i`-th biproduct inclusion. -/
theorem chainSigmaIso_chainMap (i : ι) :
    Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
        ≫ (chainSigmaIso α).hom
      = biproduct.ι (fun i => pieceChains α i) i := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom (chainSigmaCofan_isColimit α)
    (biproduct.isColimit (fun i => pieceChains α i)) ⟨i⟩
  simp only [chainSigmaIso, chainSigmaCofan, Cofan.mk_ι_app, Bicone.toCocone_ι_app,
    biproduct.bicone_ι] at h ⊢
  exact h

/-- **The retraction of the singular chain complex of a `σ`-type onto its `i`-th piece.** -/
noncomputable def chainSigmaRetract (i : ι) : sigmaChains α ⟶ pieceChains α i :=
  (chainSigmaIso α).hom ≫ biproduct.π (fun i => pieceChains α i) i

/-- The retractions split the inclusions: `chainMap (sigmaι i) ≫ chainSigmaRetract i = 𝟙`. -/
@[simp] theorem chainMap_sigmaι_comp_retract (i : ι) :
    Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
      ≫ chainSigmaRetract α i = 𝟙 (pieceChains α i) := by
  rw [chainSigmaRetract, ← Category.assoc, chainSigmaIso_chainMap, biproduct.ι_π_self]

/-- The retractions kill the other inclusions: `chainMap (sigmaι j) ≫ chainSigmaRetract i = 0` for
`j ≠ i`. -/
theorem chainMap_sigmaι_comp_retract_ne {i j : ι} (h : j ≠ i) :
    Work.Cohomology.chainMap ℤ (α j) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α j)
      ≫ chainSigmaRetract α i = 0 := by
  classical
  rw [chainSigmaRetract, ← Category.assoc, chainSigmaIso_chainMap, biproduct.ι_π]
  simp [h]

/-- **The retractions and the inclusions are complementary**: their sum is the identity. -/
theorem sum_retract_comp_chainMap :
    ∑ i, chainSigmaRetract α i
      ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
      = 𝟙 (sigmaChains α) := by
  have hι : ∀ i, Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
      = biproduct.ι (fun i => pieceChains α i) i ≫ (chainSigmaIso α).inv := by
    intro i
    rw [← chainSigmaIso_chainMap α i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc ∑ i, chainSigmaRetract α i
      ≫ Work.Cohomology.chainMap ℤ (α i) (TopCat.of (Σ i, α i)) (TopCat.sigmaι α i)
      = ∑ i, ((chainSigmaIso α).hom ≫ biproduct.π (fun i => pieceChains α i) i)
          ≫ (biproduct.ι (fun i => pieceChains α i) i ≫ (chainSigmaIso α).inv) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [chainSigmaRetract, hι i]
    _ = ∑ i, (chainSigmaIso α).hom
          ≫ (biproduct.π (fun i => pieceChains α i) i ≫ biproduct.ι (fun i => pieceChains α i) i)
          ≫ (chainSigmaIso α).inv := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Category.assoc]
    _ = (chainSigmaIso α).hom
          ≫ (∑ i, biproduct.π (fun i => pieceChains α i) i
              ≫ biproduct.ι (fun i => pieceChains α i) i)
          ≫ (chainSigmaIso α).inv := by
        rw [Preadditive.sum_comp, Preadditive.comp_sum]
    _ = 𝟙 (sigmaChains α) := by
        rw [biproduct.total]
        simp only [Category.id_comp, Iso.hom_inv_id]

end

end Work.ThomBordism
