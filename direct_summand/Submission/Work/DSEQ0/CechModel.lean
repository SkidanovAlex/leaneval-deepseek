import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Model

/-!
# DSEQ0 (area EQ0): assembly of the Čech model with a perfect model

The frozen area `DSMap.area_F1_cech` produces, for a finite affine cover `U` of `X` (with `X`
separated and quasi-compact over `Spec A`), a chain map `cc : A[0] ⟶ Č(U; 𝒪)` and an
isomorphism `e : ι (RΓ(X,𝒪)) ≅ Q (Č(U;𝒪))` which intertwines the challenge unit `rgUnit` with
the Čech coaugmentation `cc`.

Everything that is left in area `EQ0` is then the construction of a *perfect model*: a complex
`P` of finite free `A`-modules together with

* a quasi-isomorphism `q : P ⟶ Č(U;𝒪)` (the existence of `P` is the coherence statement
  `DSMap.area_COH` plus the finiteness of the projective dimension of the cohomology modules
  over a regular local ring);
* a lift `c : A[0] ⟶ P` of the coaugmentation `cc` along `q`; and
* a chain map `φ : P ⟶ A[0]` with `c ≫ φ = 𝟙`.

The last item is what the *trace on the perfect model* (Bhatt's remark) produces: `φ` is the
supertrace of multiplication by `−` (or rather its value on `c(1)`), scaled by the inverse of
the Euler characteristic `χ = [K(X):K]`, which is invertible because the residue field of `A`
has characteristic zero (`Work.DSEQ0.isUnit_natCast_of_charZero_residueField`).

This file proves the *assembly*: given the Čech data and the perfect model data, the challenge
unit is a split mono (and hence `DSplit` holds).
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u v w w₁ w₂

variable (A : Type u) [CommRing A]

/-- **Assembly of the Čech model with a perfect model.**  Given the data produced by the frozen
`DSMap.area_F1_cech` (the Čech coaugmentation `cc` and the model isomorphism `e` together with
the compatibility clause `he`), a complex `P` with a quasi-isomorphism `q : P ⟶ Č`, a lift
`c : A[0] ⟶ P` of `cc`, and a chain map `φ : P ⟶ A[0]` retracting `c`, the challenge unit
`rgUnit A X f` is a split monomorphism. -/
theorem isSplitMono_of_cechModel [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {ι : Type u} (U : ι → X.Opens)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (c : singleZ A ⟶ P)
    (hc : DerivedCategory.Q.map cc = DerivedCategory.Q.map c ≫ DerivedCategory.Q.map q)
    (φ : P ⟶ singleZ A) (hφ : c ≫ φ = 𝟙 (singleZ A)) :
    IsSplitMono (DSMap.rgUnit A X f) := by
  have hqiso : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) q).mpr hq
  refine isSplitMono_of_chainModel A X f P c φ (e ≪≫ (asIso (DerivedCategory.Q.map q)).symm)
    ?_ hφ
  rw [Iso.trans_hom, ← Category.assoc, he, Category.assoc, hc, Category.assoc]
  rw [show DerivedCategory.Q.map q ≫ (asIso (DerivedCategory.Q.map q)).symm.hom = 𝟙 _ from
    Iso.hom_inv_id (asIso (DerivedCategory.Q.map q)), Category.comp_id]

/-- The strict form of the preceding lemma, where `c` lifts the coaugmentation `cc` *on the
nose* rather than only in the derived category.  The derived form above is the one that
`Work.DSEQ0.PerfectModel` uses, since it is the one that can always be arranged (lifting a
morphism along a quasi-isomorphism is possible because `A[0]` is K-projective), whereas the
strict form needs `q` to have the lifting property. -/
theorem isSplitMono_of_cechModel_strict [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {ι : Type u} (U : ι → X.Opens)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q)
    (c : singleZ A ⟶ P) (hc : c ≫ q = cc)
    (φ : P ⟶ singleZ A) (hφ : c ≫ φ = 𝟙 (singleZ A)) :
    IsSplitMono (DSMap.rgUnit A X f) :=
  isSplitMono_of_cechModel A X f U cc e he P q hq c (by rw [← hc, DerivedCategory.Q.map_comp])
    φ hφ

end Work.DSEQ0
