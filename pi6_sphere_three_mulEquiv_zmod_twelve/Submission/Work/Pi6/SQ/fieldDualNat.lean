import Mathlib
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Serre.cohRatAlg
import Submission.Work.Serre.moduleCatLeftHomologyMap_mkQ
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Naturality of the field universal coefficient theorem

For a field `F` and a chain complex `C` of `F`-vector spaces, the field universal coefficient
theorem identifies the cohomology of the dual complex `Hom_F(C,F)` with the `F`-dual of the
homology (`Work.StemsB.fieldDualUCT`).  This file shows that this identification can be chosen
*naturally* in `C`: there is a family `Φ C n : Hⁿ(Hom(C,F)) →ₗ Hom(Hₙ(C),F)` of linear
bijections with

`Φ C n (Hⁿ(dual f) x) = dualMap (Hₙ(f)) (Φ D n x)`

for every chain map `f : C ⟶ D`.

The proof follows the structure of `Work.StemsB.fieldDualUCT`: the canonical isomorphism is the
composite

`Hⁿ(dual C) ≅ ker dⁿ / Pre ≅ (Zₙ/Bₙ)ᵛ ≅ (Hₙ C)ᵛ`,

and each of the three pieces is natural:

* the identification of the abstract homology with the explicit "cocycles modulo coboundaries"
  model, `eD` (resp. "cycles modulo boundaries", `eE`), which is
  `homologyIsoSc' ≪≫ moduleCatHomologyIso`;  its naturality is Mathlib's
  `ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality` together with the (proved here)
  naturality of `HomologicalComplex.homologyIsoSc'`;
* the comparison map `Work.StemsB.fdMiddle`, whose naturality is
  `Work.Serre.fdMiddle_square`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

namespace Work.Pi6.SQ

section Field

variable (F : Type) [Field F]

/-! ## Naturality of `homologyIsoSc'` -/

/-- The canonical isomorphism `K.homology j ≅ (K.sc' i j k).homology` is natural in the
homological complex. -/
theorem homologyIsoSc'_naturality {ι : Type} (c : ComplexShape ι)
    (K L : HomologicalComplex (ModuleCat.{0,0} F) c) (φ : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    (K.homologyIsoSc' i j k hi hk).hom ≫
        (ShortComplex.homologyMap ((shortComplexFunctor' (ModuleCat.{0,0} F) c i j k).map φ))
      = (HomologicalComplex.homologyMap φ j) ≫ (L.homologyIsoSc' i j k hi hk).hom := by
  subst hi
  subst hk
  simp only [homologyIsoSc'_eq_refl, Iso.refl_hom]
  rfl

/-- The canonical isomorphism from the abstract homology to the explicit "cycles modulo
boundaries" model of `Work.StemsB.fdZ`/`Work.StemsB.fdH`: it is `homologyIsoSc'` followed by the
module-category left homology data. -/
noncomputable def eSc {ι : Type} (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat.{0,0} F) c) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) [K.HasHomology j] [(K.sc' i j k).HasHomology] :
    K.homology j ≅ (K.sc' i j k).moduleCatLeftHomologyData.H :=
  (K.homologyIsoSc' i j k hi hk) ≪≫ (K.sc' i j k).moduleCatLeftHomologyData.homologyIso

/-- **Naturality of the model isomorphism `eSc`**: it interchanges the map induced by a chain map
on the abstract homology with the explicit left homology map of the associated short complexes. -/
theorem eSc_naturality {ι : Type} (c : ComplexShape ι)
    (K L : HomologicalComplex (ModuleCat.{0,0} F) c) (φ : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    (eSc F c K i j k hi hk).hom ≫
        ShortComplex.leftHomologyMap' ((shortComplexFunctor' (ModuleCat.{0,0} F) c i j k).map φ)
          (K.sc' i j k).moduleCatLeftHomologyData (L.sc' i j k).moduleCatLeftHomologyData
      = HomologicalComplex.homologyMap φ j ≫ (eSc F c L i j k hi hk).hom := by
  rw [eSc, eSc, Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  have h1 := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
      ((shortComplexFunctor' (ModuleCat.{0,0} F) c i j k).map φ)
      (K.sc' i j k).moduleCatLeftHomologyData (L.sc' i j k).moduleCatLeftHomologyData
  rw [h1]
  have h2 := homologyIsoSc'_naturality F c K L φ i j k hi hk
  rw [← Category.assoc, h2, Category.assoc]

/-! ## The two specialisations -/

/-- The canonical isomorphism `Hₙ(C) ≅ Zₙ/Bₙ` of the chain complex `C`, in the explicit model. -/
noncomputable def eE (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of F (↥(Work.StemsB.fdZ F C n) ⧸ Work.StemsB.fdH F C n) :=
  eSc F (ComplexShape.down ℕ) C (n + 1) n (n - 1)
    (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)

/-- The canonical isomorphism `Hⁿ(Hom(C,F)) ≅ ker dⁿ/Im dⁿ⁻¹` of the dual complex, in the
explicit model (`Work.StemsB.fdPre`). -/
noncomputable def eD (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F C).homology n ≅
      ModuleCat.of F (↥(LinearMap.ker (((Work.Cohomology.dualComplex F C).d n (n + 1)).hom)) ⧸
        Work.StemsB.fdPre F C n) :=
  eSc F (ComplexShape.up ℕ) (Work.Cohomology.dualComplex F C) (n - 1) n (n + 1)
    (Work.Cohomology.up_prev n) (Work.Cohomology.up_next n)

/-- Naturality of `eE` against the explicit homology map `Work.Serre.fdZMap`. -/
theorem eE_naturality (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ) :
    (eE F C n).hom ≫ Work.Serre.fdZMap C D f n
      = HomologicalComplex.homologyMap f n ≫ (eE F D n).hom :=
  eSc_naturality F (ComplexShape.down ℕ) C D f (n + 1) n (n - 1)
    (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)

/-- Naturality of `eD` against the explicit cohomology map `Work.Serre.dualHMap`. -/
theorem eD_naturality (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ) :
    (eD F D n).hom ≫ Work.Serre.dualHMap C D f n
      = HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D f) n
          ≫ (eD F C n).hom :=
  eSc_naturality F (ComplexShape.up ℕ) (Work.Cohomology.dualComplex F D)
    (Work.Cohomology.dualComplex F C) (Work.Cohomology.dualComplexMap F C D f) (n - 1) n (n + 1)
    (Work.Cohomology.up_prev n) (Work.Cohomology.up_next n)

/-- Pointwise form of `eE_naturality`. -/
theorem eE_naturality_apply (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ)
    (z : ↥(C.homology n)) :
    (Work.Serre.fdZMap C D f n).hom ((eE F C n).hom.hom z)
      = (eE F D n).hom.hom ((HomologicalComplex.homologyMap f n).hom z) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (eE_naturality F C D f n)) z
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Pointwise form of `eD_naturality`. -/
theorem eD_naturality_apply (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ)
    (x : ↥((Work.Cohomology.dualComplex F D).homology n)) :
    (Work.Serre.dualHMap C D f n).hom ((eD F D n).hom.hom x)
      = (eD F C n).hom.hom
          ((HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D f) n).hom x) := by
  have h := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (eD_naturality F C D f n)) x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Pointwise form of `Work.Serre.fdMiddle_square`: evaluation of the comparison map on the class
of a cycle. -/
theorem fdMiddle_square_apply (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ)
    (w : ↥(LinearMap.ker (((Work.Cohomology.dualComplex F D).d n (n + 1)).hom)) ⧸
      Work.StemsB.fdPre F D n)
    (z : ↥(Work.StemsB.fdZ F C n) ⧸ Work.StemsB.fdH F C n) :
    (Work.StemsB.fdMiddle F C n).toLinearMap ((Work.Serre.dualHMap C D f n).hom w) z
      = (Work.StemsB.fdMiddle F D n).toLinearMap w ((Work.Serre.fdZMap C D f n).hom z) := by
  have h := LinearMap.congr_fun (Work.Serre.fdMiddle_square C D f n) w
  have h2 := LinearMap.congr_fun h z
  simpa only [LinearMap.comp_apply, LinearMap.dualMap_apply] using h2

/-! ## The natural family and its properties -/

/-- **The universal coefficient isomorphism**, as an explicit linear map: the composite of the
identification `eD` of cohomology with the explicit model, the comparison map
`Work.StemsB.fdMiddle`, and the transpose of the identification `eE` of homology. -/
noncomputable def Phi (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    (Work.Cohomology.dualComplex F C).homology n →ₗ[F] (↥(C.homology n) →ₗ[F] F) :=
  (LinearMap.dualMap (eE F C n).hom.hom).comp
    ((Work.StemsB.fdMiddle F C n).toLinearMap.comp (eD F C n).hom.hom)

/-- **Naturality of `Phi`** in the chain complex. -/
theorem Phi_naturality (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ)
    (x : ↥((Work.Cohomology.dualComplex F D).homology n)) :
    (Phi F C n)
        ((HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D f) n).hom x)
      = (LinearMap.dualMap (HomologicalComplex.homologyMap f n).hom) ((Phi F D n) x) := by
  apply LinearMap.ext
  intro z
  simp only [Phi, LinearMap.comp_apply, LinearMap.dualMap_apply]
  rw [← eD_naturality_apply F C D f n x,
    fdMiddle_square_apply F C D f n ((eD F D n).hom.hom x) ((eE F C n).hom.hom z),
    eE_naturality_apply F C D f n z]

/-- `Phi` is a bijection, being a composite of bijections. -/
theorem Phi_bijective (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ) :
    Function.Bijective (Phi F C n) := by
  have hE : Function.Bijective (eE F C n).hom.hom :=
    (Work.Cohomology.uctIsoToLinearEquiv (eE F C n)).bijective
  have hM : Function.Bijective (Work.StemsB.fdMiddle F C n).toLinearMap :=
    (Work.StemsB.fdMiddle F C n).bijective
  have hD : Function.Bijective (eD F C n).hom.hom :=
    (Work.Cohomology.uctIsoToLinearEquiv (eD F C n)).bijective
  have hdual : Function.Bijective (LinearMap.dualMap (eE F C n).hom.hom) :=
    ⟨LinearMap.dualMap_injective_of_surjective hE.2,
      LinearMap.dualMap_surjective_of_injective hE.1⟩
  have h := hdual.comp (hM.comp hD)
  have hfun : ⇑(Phi F C n) = ⇑(LinearMap.dualMap (eE F C n).hom.hom) ∘
      (⇑(Work.StemsB.fdMiddle F C n).toLinearMap ∘ ⇑(eD F C n).hom.hom) := by
    funext y
    simp only [Phi, LinearMap.comp_apply, Function.comp_apply]
  rw [hfun]
  exact h

end Field

theorem fieldDualNat (F : Type) [Field F] :
    ∃ Φ : ∀ (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ),
        (Work.Cohomology.dualComplex F C).homology n →ₗ[F] (↥(C.homology n) →ₗ[F] F),
      (∀ (C : ChainComplex (ModuleCat.{0,0} F) ℕ) (n : ℕ), Function.Bijective (Φ C n)) ∧
      (∀ (C D : ChainComplex (ModuleCat.{0,0} F) ℕ) (f : C ⟶ D) (n : ℕ)
          (x : (Work.Cohomology.dualComplex F D).homology n),
        Φ C n ((HomologicalComplex.homologyMap (Work.Cohomology.dualComplexMap F C D f) n).hom x)
          = (LinearMap.dualMap (HomologicalComplex.homologyMap f n).hom) (Φ D n x)) :=
  ⟨fun C n => Phi F C n, fun C n => Phi_bijective F C n,
    fun C D f n x => Phi_naturality F C D f n x⟩

end Work.Pi6.SQ
