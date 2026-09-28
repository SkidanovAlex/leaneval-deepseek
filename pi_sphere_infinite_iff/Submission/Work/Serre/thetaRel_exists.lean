import Mathlib
import Submission.Work.Serre.RatMVDefs
import Submission.Work.Serre.E3aDefs
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.hmv_naturality

/-!
# The relative comparison `C^*(X,A;ℚ) ≅ DQ(C_*(X,A;ℤ))`

For a pair of topological spaces `A ⊆ X` we construct an isomorphism of cochain complexes
`Θ(X,A) : C^*(X,A;ℚ) ≅ DQ(C_*(X,A;ℤ))`, where `DQ C` is the `ℚ`-dual of the base change
`C ⊗[ℤ] ℚ` of a `ℤ`-chain complex, and we prove that `Θ` is natural with respect to maps of pairs.

The construction is the composite

`C^*(X,A;ℚ) ≅ Hom_ℚ(C_*(X,A;ℚ), ℚ) ≅ Hom_ℚ(C_*(X,A;ℤ) ⊗[ℤ] ℚ, ℚ) ≅ DQ(C_*(X,A;ℤ))`

of

* `dualIsoRQ` — the coefficient-generic duality `relComplex R X A ≅ dualComplex R (relChainsR R X A)`
  (`Work.StemsB.relCochainDualR`) specialised to `R = ℚ`;
* `thetaRelBaseChange` — the `ℤ → ℚ` base change `C_*(X,A;ℤ) ⊗[ℤ] ℚ ≅ C_*(X,A;ℚ)`, obtained from
  the absolute base change `Work.StemsB.RatBC.Phi` by right exactness of `- ⊗[ℤ] ℚ`.

Naturality of both factors is proved (`dualIsoRQ_natural`, `thetaRelBaseChange_natural`), and the
two combine into the naturality of `Θ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

namespace Work.Serre

noncomputable section

/-! ## The pair map on relative chains over `ℚ` -/

/-- The composite `cokernel.π ≫ relChainsRMapOf` is the absolute chain map followed by
`cokernel.π`. -/
theorem cokernel_π_relChainsRMapOf (R : Type) [CommRing R] {X Y : TopCat} (A : Set X) (B : Set Y)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.StemsB.relChainsRIncl R X A) ≫
        Work.Serre.relChainsRMapOf (R := R) X Y A B f g w
      = Work.Cohomology.chainMap R X Y f ≫
          cokernel.π (Work.StemsB.relChainsRIncl R Y B) := by
  rw [Work.Serre.relChainsRMapOf]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The `ℚ`-pair map on relative chains of the map of pairs `(X,A) → (Y,B)`. -/
abbrev hmvPairsChainsQ {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, f x ∈ B) :
    Work.StemsB.relChainsR ℚ X A ⟶ Work.StemsB.relChainsR ℚ Y B :=
  Work.Serre.relChainsRMapOf (R := ℚ) X Y A B f
    (Work.Cohomology.relMapSub A B f hf) (Work.Cohomology.relMapSub_spec A B f hf)

/-! ## The absolute base change, with the vocabulary of the relative chains -/

/-- The absolute base change `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)`, with its type written in the
vocabulary of `Work.Cohomology.singularChains`. -/
noncomputable def PhiAbs (X : TopCat) :
    Work.StemsB.IntRatCM.obj (Work.Cohomology.singularChains ℤ X) ≅
      Work.Cohomology.singularChains ℚ X :=
  show Work.StemsB.IntRatCM.obj (Work.Cohomology.singularChains ℤ X) ≅
      Work.Cohomology.singularChains ℚ X from
    Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)

/-- The forward map of `PhiAbs` is `Phi`. -/
theorem PhiAbs_hom (X : TopCat) :
    (PhiAbs X).hom = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom := rfl

/-- The inverse of `PhiAbs` is the inverse of `Phi`. -/
theorem PhiAbs_inv (X : TopCat) :
    (PhiAbs X).inv = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).inv := rfl

/-- Naturality of the absolute comparison `Phi` with respect to the singular chain map. -/
theorem Phi_naturality_chainMap {X Y : TopCat} (f : X ⟶ Y) :
    (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom ≫ Work.Cohomology.chainMap ℚ X Y f
      = Work.StemsB.IntRatCM.map (Work.Cohomology.chainMap ℤ X Y f)
        ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj Y)).hom :=
  Work.StemsB.RatBC.Phi_naturality (TopCat.toSSet.map f)

/-- The square expressing the naturality of the absolute base change with respect to the
inclusion `A ⊆ X`. -/
theorem phiSquare_incl (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A) ≫ (PhiAbs X).hom
      = (PhiAbs (TopCat.of ↥A)).hom ≫ Work.StemsB.relChainsRIncl ℚ X A := by
  show (Work.StemsB.RatBC.IntRat.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map
        (Functor.whiskerRight (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
          (Limits.sigmaConst.obj Work.StemsB.RatBC.ZMod)))
      ≫ (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj X)).hom
    = (Work.StemsB.RatBC.Phi (TopCat.toSSet.obj (TopCat.of ↥A))).hom
      ≫ (alternatingFaceMapComplex (ModuleCat.{0} ℚ)).map
        (Functor.whiskerRight (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
          (Limits.sigmaConst.obj Work.StemsB.RatBC.QMod))
  exact (Work.StemsB.RatBC.Phi_naturality
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))).symm

/-! ## The `ℤ → ℚ` base change of the relative chains -/

/-- **The base change `C_*(X,A;ℤ) ⊗[ℤ] ℚ ≅ C_*(X,A;ℚ)`** of the relative singular chains.  It is
the composite of the preservation of the cokernel of the inclusion `C_*(A;ℤ) ⟶ C_*(X;ℤ)` by
`- ⊗[ℤ] ℚ` and the canonical isomorphism of the two cokernels, the square being the naturality of
`Phi` with respect to the inclusion `A ⊆ X`. -/
noncomputable def thetaRelBaseChange (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A) ≅ Work.StemsB.relChainsR ℚ X A :=
  Limits.PreservesCokernel.iso Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A) ≪≫
    Limits.cokernel.mapIso (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
      (Work.StemsB.relChainsRIncl ℚ X A) (PhiAbs (TopCat.of ↥A)) (PhiAbs X)
      (phiSquare_incl X A)

/-- **The defining property of the base change**: composed with the projection from the absolute
chains it is `Phi` followed by the projection to the relative chains. -/
theorem thetaRelBaseChange_π (X : TopCat) (A : Set X) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A)
        ≫ (thetaRelBaseChange X A).hom
      = (PhiAbs X).hom ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) := by
  show Work.StemsB.IntRatCM.map (cokernel.π (Work.Cohomology.inclChains X A))
      ≫ ((Limits.PreservesCokernel.iso Work.StemsB.IntRatCM
            (Work.Cohomology.inclChains X A)).hom
          ≫ (Limits.cokernel.mapIso (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
              (Work.StemsB.relChainsRIncl ℚ X A) (PhiAbs (TopCat.of ↥A)) (PhiAbs X)
              (phiSquare_incl X A)).hom)
      = (PhiAbs X).hom ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)
  rw [← Category.assoc, PreservesCokernel.π_iso_hom Work.StemsB.IntRatCM
      (Work.Cohomology.inclChains X A), cokernel.mapIso_hom]
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- **Naturality of the `ℤ → ℚ` base change of the relative chains** in the map of pairs. -/
theorem thetaRelBaseChange_natural {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, f x ∈ B) :
    Work.StemsB.IntRatCM.map (Work.Cohomology.hmvPairsChains A B f hf)
        ≫ (thetaRelBaseChange Y B).hom
      = (thetaRelBaseChange X A).hom ≫ hmvPairsChainsQ A B f hf := by
  haveI : Epi (Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A)) := by
    have h : Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A)
        = cokernel.π (Work.StemsB.IntRatCM.map (Work.Cohomology.inclChains X A))
          ≫ (Limits.PreservesCokernel.iso Work.StemsB.IntRatCM
              (Work.Cohomology.inclChains X A)).inv := by
      rw [← PreservesCokernel.π_iso_hom Work.StemsB.IntRatCM (Work.Cohomology.inclChains X A),
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance
  refine (cancel_epi (Work.StemsB.IntRatCM.map (Work.Cohomology.relChainsProj X A))).1 ?_
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp,
    Work.Cohomology.hmvRelDualProj_relChains A B f hf, Functor.map_comp, Category.assoc,
    thetaRelBaseChange_π Y B, PhiAbs_hom Y, ← Category.assoc, ← Phi_naturality_chainMap f,
    Category.assoc]
  conv_rhs => rw [← Category.assoc, thetaRelBaseChange_π X A, PhiAbs_hom X, Category.assoc,
    cokernel_π_relChainsRMapOf]

/-! ## The relative cochains as the `ℚ`-dual of the relative chains -/

/-- The `ℚ`-duality `Hom_ℚ(C_*(X,A;ℚ), ℚ) ≅ C^*(X,A;ℚ)` as an isomorphism of cochain complexes,
from the coefficient-generic degreewise isomorphism `Work.StemsB.rdRIso`. -/
noncomputable def dualIsoRQ (X : TopCat) (A : Set X) :
    Work.Cohomology.dualComplex ℚ (Work.StemsB.relChainsR ℚ X A) ≅
      Work.Cohomology.relComplex ℚ X A :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Work.StemsB.rdRIso ℚ X A n)
    (fun i j hij => by rw [← hij]; exact Work.StemsB.rdRIso_comm ℚ X A i)

@[simp] theorem dualIsoRQ_hom_f (X : TopCat) (A : Set X) (n : ℕ) :
    (dualIsoRQ X A).hom.f n = (Work.StemsB.rdRIso ℚ X A n).hom :=
  HomologicalComplex.Hom.isoOfComponents_hom_f _ _ n

/-- The map of relative cochain complexes induced by a map of pairs is compatible with the
inclusions into the absolute complexes, over `ℚ`. -/
theorem relComplexMapQ_comp_relIncl {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap ℚ A₁ A₂ f h ≫ Work.Cohomology.relIncl ℚ X₁ A₁
      = Work.Cohomology.relIncl ℚ X₂ A₂ ≫ Work.Cohomology.dualChainMap ℚ X₁ X₂ f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Work.Cohomology.relMapLM_coe ℚ A₁ A₂ f h n x

/-- The dual of a continuous map, in the form of `dualComplexMap` over `ℚ`. -/
theorem dualChainMapQ_eq_dualComplexMap {X Y : TopCat} (f : X ⟶ Y) :
    Work.Cohomology.dualChainMap ℚ X Y f
      = Work.Cohomology.dualComplexMap ℚ (Work.Cohomology.singularChains ℚ X)
          (Work.Cohomology.singularChains ℚ Y) (Work.Cohomology.chainMap ℚ X Y f) := rfl

/-- **Degreewise naturality of the `ℚ`-duality.** -/
theorem dualIsoRQ_natural_f {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (n : ℕ) :
    (Work.StemsB.rdRIso ℚ X₂ A₂ n).hom ≫ (Work.Cohomology.relComplexMap ℚ A₁ A₂ f h).f n
      = Work.Cohomology.dualComplexMapComp ℚ (Work.StemsB.relChainsR ℚ X₁ A₁)
          (Work.StemsB.relChainsR ℚ X₂ A₂) (hmvPairsChainsQ A₁ A₂ f h) n
        ≫ (Work.StemsB.rdRIso ℚ X₁ A₁ n).hom := by
  haveI : Mono ((Work.Cohomology.relIncl ℚ X₁ A₁).f n) := by
    rw [Work.Cohomology.relIncl_f, ModuleCat.mono_iff_injective]
    intro a b hab
    exact Subtype.ext hab
  apply (cancel_mono ((Work.Cohomology.relIncl ℚ X₁ A₁).f n)).1
  rw [Category.assoc, Category.assoc]
  have hdeg : (Work.Cohomology.relComplexMap ℚ A₁ A₂ f h).f n
        ≫ (Work.Cohomology.relIncl ℚ X₁ A₁).f n
      = (Work.Cohomology.relIncl ℚ X₂ A₂).f n
        ≫ (Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f n := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, relComplexMapQ_comp_relIncl]
  rw [hdeg]
  rw [show (Work.StemsB.rdRIso ℚ X₁ A₁ n).hom ≫ (Work.Cohomology.relIncl ℚ X₁ A₁).f n
      = Work.Cohomology.dualComplexMapComp ℚ (Work.Cohomology.singularChains ℚ X₁)
          (Work.StemsB.relChainsR ℚ X₁ A₁)
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ X₁ A₁)) n from
    Work.StemsB.rdRMap_comp_relIncl ℚ X₁ A₁ n]
  rw [← Category.assoc]
  rw [show (Work.StemsB.rdRIso ℚ X₂ A₂ n).hom ≫ (Work.Cohomology.relIncl ℚ X₂ A₂).f n
      = Work.Cohomology.dualComplexMapComp ℚ (Work.Cohomology.singularChains ℚ X₂)
          (Work.StemsB.relChainsR ℚ X₂ A₂)
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ X₂ A₂)) n from
    Work.StemsB.rdRMap_comp_relIncl ℚ X₂ A₂ n]
  rw [show (Work.Cohomology.dualChainMap ℚ X₁ X₂ f).f n
      = Work.Cohomology.dualComplexMapComp ℚ (Work.Cohomology.singularChains ℚ X₁)
          (Work.Cohomology.singularChains ℚ X₂) (Work.Cohomology.chainMap ℚ X₁ X₂ f) n from by
    rw [dualChainMapQ_eq_dualComplexMap, Work.Cohomology.dualComplexMap_f]]
  rw [← Work.Cohomology.dualComplexMapComp_comp, ← Work.Cohomology.dualComplexMapComp_comp]
  rw [cokernel_π_relChainsRMapOf]

/-- **Naturality of the `ℚ`-duality** in a map of pairs. -/
theorem dualIsoRQ_natural {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) :
    (dualIsoRQ X₂ A₂).hom ≫ Work.Cohomology.relComplexMap ℚ A₁ A₂ f h
      = Work.Cohomology.dualComplexMap ℚ (Work.StemsB.relChainsR ℚ X₁ A₁)
          (Work.StemsB.relChainsR ℚ X₂ A₂) (hmvPairsChainsQ A₁ A₂ f h)
        ≫ (dualIsoRQ X₁ A₁).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, dualIsoRQ_hom_f, dualIsoRQ_hom_f,
    Work.Cohomology.dualComplexMap_f]
  exact dualIsoRQ_natural_f A₁ A₂ f h n

/-- The mate of the naturality of the `ℚ`-duality. -/
theorem relComplexMapQ_comp_dualIsoRQ_inv {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap ℚ A₁ A₂ f h ≫ (dualIsoRQ X₁ A₁).inv
      = (dualIsoRQ X₂ A₂).inv
        ≫ Work.Cohomology.dualComplexMap ℚ (Work.StemsB.relChainsR ℚ X₁ A₁)
            (Work.StemsB.relChainsR ℚ X₂ A₂) (hmvPairsChainsQ A₁ A₂ f h) := by
  have hnat := dualIsoRQ_natural A₁ A₂ f h
  calc Work.Cohomology.relComplexMap ℚ A₁ A₂ f h ≫ (dualIsoRQ X₁ A₁).inv
      = ((dualIsoRQ X₂ A₂).inv ≫ (dualIsoRQ X₂ A₂).hom)
          ≫ Work.Cohomology.relComplexMap ℚ A₁ A₂ f h ≫ (dualIsoRQ X₁ A₁).inv := by
          rw [Iso.inv_hom_id, Category.id_comp]
    _ = (dualIsoRQ X₂ A₂).inv
          ≫ ((dualIsoRQ X₂ A₂).hom ≫ Work.Cohomology.relComplexMap ℚ A₁ A₂ f h)
          ≫ (dualIsoRQ X₁ A₁).inv := by simp only [Category.assoc]
    _ = (dualIsoRQ X₂ A₂).inv
          ≫ (Work.Cohomology.dualComplexMap ℚ (Work.StemsB.relChainsR ℚ X₁ A₁)
                (Work.StemsB.relChainsR ℚ X₂ A₂) (hmvPairsChainsQ A₁ A₂ f h)
              ≫ (dualIsoRQ X₁ A₁).hom)
          ≫ (dualIsoRQ X₁ A₁).inv := by rw [hnat]
    _ = (dualIsoRQ X₂ A₂).inv
          ≫ Work.Cohomology.dualComplexMap ℚ (Work.StemsB.relChainsR ℚ X₁ A₁)
              (Work.StemsB.relChainsR ℚ X₂ A₂) (hmvPairsChainsQ A₁ A₂ f h) := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## The isomorphism `Θ` and the theorem -/

/-- The isomorphism `DQ(C_*(X,A;ℤ)) ≅ Hom_ℚ(C_*(X,A;ℚ), ℚ)` given by the dual of the base
change. -/
noncomputable def dqBaseChangeIso (X : TopCat) (A : Set X) :
    Work.Cohomology.dualComplex ℚ (Work.StemsB.relChainsR ℚ X A) ≅
      DQ (Work.Cohomology.relChains X A) where
  hom := Work.Cohomology.dualComplexMap ℚ
    (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A))
    (Work.StemsB.relChainsR ℚ X A) (thetaRelBaseChange X A).hom
  inv := Work.Cohomology.dualComplexMap ℚ (Work.StemsB.relChainsR ℚ X A)
    (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A)) (thetaRelBaseChange X A).inv
  hom_inv_id := by
    rw [← Work.Cohomology.dualComplexMap_comp, Iso.inv_hom_id,
      Work.Cohomology.dualComplexMap_id]
  inv_hom_id := by
    rw [← Work.Cohomology.dualComplexMap_comp, Iso.hom_inv_id,
      Work.Cohomology.dualComplexMap_id]

theorem dqBaseChangeIso_hom (X : TopCat) (A : Set X) :
    (dqBaseChangeIso X A).hom
      = Work.Cohomology.dualComplexMap ℚ
          (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains X A))
          (Work.StemsB.relChainsR ℚ X A) (thetaRelBaseChange X A).hom := rfl

/-- **The relative comparison** `C^*(X,A;ℚ) ≅ DQ(C_*(X,A;ℤ))`. -/
noncomputable def thetaRel (X : TopCat) (A : Set X) :
    Work.Cohomology.relComplex ℚ X A ≅ DQ (Work.Cohomology.relChains X A) :=
  (dualIsoRQ X A).symm ≪≫ dqBaseChangeIso X A

theorem thetaRel_hom (X : TopCat) (A : Set X) :
    (thetaRel X A).hom = (dualIsoRQ X A).inv ≫ (dqBaseChangeIso X A).hom := by
  rw [thetaRel, Iso.trans_hom, Iso.symm_hom]

/-- **Naturality of the relative comparison** in a map of pairs. -/
theorem thetaRel_natural {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, f x ∈ B) :
    (thetaRel Y B).hom ≫ dqMap (Work.Cohomology.hmvPairsChains A B f hf)
      = Work.Cohomology.relComplexMap ℚ A B f hf ≫ (thetaRel X A).hom := by
  rw [thetaRel_hom Y B, thetaRel_hom X A, dqBaseChangeIso_hom, dqBaseChangeIso_hom,
    Work.Serre.dqMap]
  conv_lhs => rw [Category.assoc, ← Work.Cohomology.dualComplexMap_comp,
    thetaRelBaseChange_natural A B f hf, Work.Cohomology.dualComplexMap_comp]
  conv_rhs => rw [← Category.assoc, relComplexMapQ_comp_dualIsoRQ_inv A B f hf, Category.assoc]

theorem thetaRel_exists : ∃ (Theta : ∀ (X : TopCat) (A : Set X), Work.Cohomology.relComplex ℚ X A ≅ Work.Serre.DQ (Work.Cohomology.relChains X A)), (∀ {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y) (hf : ∀ x ∈ A, f x ∈ B), CategoryTheory.CategoryStruct.comp (Theta Y B).hom (Work.Serre.dqMap (Work.Cohomology.hmvPairsChains A B f hf)) = CategoryTheory.CategoryStruct.comp (Work.Cohomology.relComplexMap ℚ A B f hf) (Theta X A).hom) :=
  ⟨thetaRel, fun A B f hf => thetaRel_natural A B f hf⟩

end

end Work.Serre
