import Mathlib
import Submission.Work.CY3Stab.Cylinder
import Submission.Work.CY3Stab.Prod.AlgMapResidue
import Submission.Work.CY3Stab.Prod.pushout_iso_of_iso_base
import Submission.Work.CY3Stab.Prod.isIso_algMapResidue_id
import Submission.Work.CY3Stab.Prod.exists_ringEquiv_residueField_genericPoint
import Submission.Work.CY3Stab.Prod.isDomain_tensor_fractionRing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.isDomain_cylTriplet_tensor`

`IsDomain ((cylTriplet X x k).tensor)`: the tensor of residue fields of the cylinder point over
`x` is the localisation `S⁻¹(κ(x)[t₁,…,t_k])` of the polynomial ring `κ(x)[t₁,…,t_k]` at the
nonzero `𝕜`-polynomials, hence a domain.

The route:

* `(cylTriplet X x k).tensor` is the pushout of `κ(s) ⟶ κ(genericPoint 𝔸ᵏ)` and
  `κ(s) ⟶ κ(x)`, where `s = (X ↘ Spec 𝕜) x` and `κ(s) ≅ 𝕜` (`isIso_algMapResidue_id`);
* changing the base of the pushout along that isomorphism (`pushout_iso_of_iso_base`) identifies
  it with `pushout a' b'` for the canonical `𝕜`-algebra structure maps `a'`, `b'`
  (`algMapResidue f (genericPoint 𝔸ᵏ)`, `algMapResidue (X ↘ Spec 𝕜) x`);
* that pushout is `B ⊗[𝕜] C` with `B = κ(genericPoint 𝔸ᵏ)`, `C = κ(x)`;
* `B ≅ 𝕜(t₁,…,t_k)` as `𝕜`-algebras (`exists_ringEquiv_residueField_affineK`, from the affine
  computation `exists_ringEquiv_residueField_genericPoint` of the residue field of the generic
  point of `Spec A`);
* `IsDomain (K ⊗[𝕜] 𝕜(t₁,…,t_k))` for a domain `K` (`isDomain_tensor_fractionRing`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.CY3Stab.Prod

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The residue-field-congruence lemma for `algMapResidue` at a point of `Spec A`, in the form
needed for the base change of the pushout. -/
theorem algMapResidue_residueFieldCongr_gen {A : Type} [CommRing A]
    {y₁ y₂ : Spec (CommRingCat.of A)} (e : y₁ = y₂) :
    algMapResidue (𝟙 (Spec (CommRingCat.of A))) y₁
        ≫ ((Spec (CommRingCat.of A)).residueFieldCongr e).hom =
      algMapResidue (𝟙 (Spec (CommRingCat.of A))) y₂ := by
  subst e
  simp [algMapResidue]

/-- **The residue field of the generic point of `𝔸ᵏ` is `𝕜(t₁,…,t_k)`**, as a `𝕜`-algebra:
the affine identification `𝔸ᵏ ≅ Spec 𝕜[t₁,…,t_k]` transports
`exists_ringEquiv_residueField_genericPoint` (the computation of the residue field of the generic
point of `Spec A` for a domain `A`) to affine space. -/
theorem exists_ringEquiv_residueField_affineK (𝕜 : Type) [Field 𝕜] (k : ℕ) :
    ∃ e : (AffineK (𝕜 := 𝕜) k).residueField (genericPoint (AffineK (𝕜 := 𝕜) k)) ≃+*
        FractionRing (MvPolynomial (Fin k) 𝕜),
      ∀ r : 𝕜, e ((algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (genericPoint (AffineK (𝕜 := 𝕜) k))).hom r)
          = algebraMap 𝕜 (FractionRing (MvPolynomial (Fin k) 𝕜)) r := by
  obtain ⟨e₄, he₄⟩ := exists_ringEquiv_residueField_genericPoint (MvPolynomial (Fin k) 𝕜)
  let e : AffineK (𝕜 := 𝕜) k ≅ Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)) :=
    AffineSpace.SpecIso (Fin k) (CommRingCat.of 𝕜)
  haveI : IsOpenImmersion e.hom := IsOpenImmersion.of_isIso e.hom
  have hgp : e.hom (genericPoint (AffineK (𝕜 := 𝕜) k)) =
      genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))) :=
    genericPoint_eq_of_isOpenImmersion e.hom
  have hstruct : (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)) ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin k) 𝕜)) := rfl
  have hf : e.hom ≫ (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)) ↘ Spec (CommRingCat.of 𝕜)) =
      (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) := by
    rw [hstruct, ← AffineSpace.SpecIso_inv_over (n := Fin k) (CommRingCat.of 𝕜), ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
    rfl
  let rf := e.hom.residueFieldMap (genericPoint (AffineK (𝕜 := 𝕜) k))
  let j : (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))).residueField
        (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)))) ≅
      (AffineK (𝕜 := 𝕜) k).residueField (genericPoint (AffineK (𝕜 := 𝕜) k)) :=
    ((Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))).residueFieldCongr hgp).symm ≪≫ asIso rf
  have hnat : algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (genericPoint (AffineK (𝕜 := 𝕜) k))
      = algMapResidue (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)) ↘ Spec (CommRingCat.of 𝕜))
          (e.hom (genericPoint (AffineK (𝕜 := 𝕜) k))) ≫ rf := by
    rw [← hf, algMapResidue_naturality]
  have hspec : algMapResidue
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin k) 𝕜)))
        (e.hom (genericPoint (AffineK (𝕜 := 𝕜) k)))
      = CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin k) 𝕜) ≫
        algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
          (e.hom (genericPoint (AffineK (𝕜 := 𝕜) k))) :=
    algMapResidue_specMap (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin k) 𝕜))
      (e.hom (genericPoint (AffineK (𝕜 := 𝕜) k)))
  have hab : algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
        (e.hom (genericPoint (AffineK (𝕜 := 𝕜) k)))
      = algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
          (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)))) ≫
        ((Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))).residueFieldCongr hgp).inv := by
    rw [show ((Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))).residueFieldCongr hgp).inv =
        ((Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))).residueFieldCongr hgp.symm).hom from
      Scheme.residueFieldCongr_inv (X := Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))) hgp]
    rw [← algMapResidue_residueFieldCongr_gen hgp.symm]
  have hcomp : algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (genericPoint (AffineK (𝕜 := 𝕜) k))
      = CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin k) 𝕜) ≫
        algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
          (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜)))) ≫ j.hom := by
    rw [hnat, hstruct, hspec, hab]
    simp only [j, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rfl
  refine ⟨(j.symm.commRingCatIsoToRingEquiv).trans e₄, ?_⟩
  intro r
  have hkey : ∀ x : ↥((AffineK (𝕜 := 𝕜) k).residueField (genericPoint (AffineK (𝕜 := 𝕜) k))),
      j.symm.commRingCatIsoToRingEquiv x = j.inv.hom x := by
    intro x
    show (j.symm.commRingCatIsoToRingEquiv : _ →+* _) x = j.inv.hom x
    rw [Iso.commRingCatIsoToRingEquiv_toRingHom]
    rfl
  rw [RingEquiv.trans_apply, hkey]
  have harg : (algMapResidue (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (genericPoint (AffineK (𝕜 := 𝕜) k))).hom r
      = j.hom.hom ((algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
          (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))).hom
            (MvPolynomial.C r)) := by
    rw [hcomp]
    rfl
  rw [harg]
  have hcancel : j.inv.hom (j.hom.hom ((algMapResidue
      (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
      (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))).hom (MvPolynomial.C r)))
      = ((algMapResidue (𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))
      (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin k) 𝕜))))).hom (MvPolynomial.C r)) := by
    have h1 : j.hom ≫ j.inv = 𝟙 _ := Iso.hom_inv_id j
    have h2 := congrArg CommRingCat.Hom.hom h1
    have h3 : j.inv.hom.comp j.hom.hom = RingHom.id _ := h2
    exact RingHom.congr_fun h3 _
  rw [hcancel, he₄]
  rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin k) 𝕜)
    (FractionRing (MvPolynomial (Fin k) 𝕜))]
  rfl

/-- **The tensor of residue fields of the cylinder point over `x` is a domain**, i.e.

`κ(genericPoint 𝔸ᵏ) ⊗_{κ(s)} κ(x) = 𝕜(t₁,…,t_k) ⊗_𝕜 κ(x) = S⁻¹(κ(x)[t₁,…,t_k])`

for `S = 𝕜[t₁,…,t_k] \ {0}`, a localisation of a polynomial ring over a field (hence over a
domain) at nonzero elements. -/
theorem isDomain_cylTriplet_tensor (𝕜 : Type) [Field 𝕜] (k : ℕ) (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (x : X) :
    IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor := by
  let S := Spec (CommRingCat.of 𝕜)
  let P1 := AffineK (𝕜 := 𝕜) k
  let f : P1 ⟶ S := P1 ↘ S
  let g : X ⟶ S := X ↘ S
  let T : Pullback.Triplet (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) :=
    Pullback.Triplet.mk' (genericPoint (AffineK (𝕜 := 𝕜) k)) x (Subsingleton.elim _ _)
  change IsDomain T.tensor
  set aa : S.residueField T.s ⟶ P1.residueField T.x :=
    (S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x with haa
  set bb : S.residueField T.s ⟶ X.residueField T.y :=
    (S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y with hbb
  have hten : T.tensor = pushout aa bb := rfl
  set a' : CommRingCat.of 𝕜 ⟶ P1.residueField T.x := algMapResidue f T.x with ha'
  set b' : CommRingCat.of 𝕜 ⟶ X.residueField T.y := algMapResidue g T.y with hb'
  haveI : IsIso (algMapResidue (𝟙 S) T.s) := isIso_algMapResidue_id 𝕜 T.s
  set χ : CommRingCat.of 𝕜 ≅ S.residueField T.s :=
    asIso (algMapResidue (𝟙 S) T.s) with hχ
  have hχhom : χ.hom = algMapResidue (𝟙 S) T.s := rfl
  have hmid : algMapResidue (𝟙 S) T.s ≫ (S.residueFieldCongr T.hx).inv
      = algMapResidue (𝟙 S) (f T.x) := by
    rw [show (S.residueFieldCongr T.hx).inv = (S.residueFieldCongr T.hx.symm).hom from
      Scheme.residueFieldCongr_inv (X := S) T.hx]
    rw [← algMapResidue_residueFieldCongr_gen T.hx.symm]
  have haa' : a' = χ.hom ≫ aa := by
    rw [haa, hχhom, ← Category.assoc, hmid, algMapResidue_id, ← ha']
  have h1 : (S.residueFieldCongr T.hy).inv = 𝟙 (S.residueField T.s) := by
    have h2 : (S.residueFieldCongr T.hy) = Iso.refl (S.residueField T.s) := rfl
    rw [h2]
    rfl
  have hbb_eq : bb = g.residueFieldMap T.y := by
    rw [hbb, h1]
    exact Category.id_comp _
  have hbb' : b' = χ.hom ≫ bb := by
    rw [hb', hχhom, hbb_eq]
    exact (algMapResidue_id g T.y).symm
  have hφa : χ.inv ≫ a' = aa := by
    rw [haa']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hφb : χ.inv ≫ b' = bb := by
    rw [hbb']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hstep1 : Nonempty (T.tensor ≅ pushout a' b') := by
    obtain ⟨e⟩ := pushout_iso_of_iso_base χ.inv a' b'
    have hobj : pushout aa bb = pushout (χ.inv ≫ a') (χ.inv ≫ b') :=
      congrArg₂ (fun f g => pushout f g) hφa.symm hφb.symm
    exact ⟨by rw [hten, hobj]; exact e⟩
  let B₁ := P1.residueField T.x
  let C₁ := X.residueField T.y
  letI : Algebra 𝕜 ↥B₁ := a'.hom.toAlgebra
  letI : Algebra 𝕜 ↥C₁ := b'.hom.toAlgebra
  have hstep2 : Nonempty (pushout a' b' ≅ ↧(TensorProduct 𝕜 ↥B₁ ↥C₁)) :=
    ⟨IsColimit.coconePointUniqueUpToIso (pushoutIsPushout a' b')
      (CommRingCat.pushoutCoconeIsColimit 𝕜 ↥B₁ ↥C₁)⟩
  obtain ⟨h4e, h4prop⟩ := exists_ringEquiv_residueField_affineK 𝕜 k
  have hBalg : B₁ ≃ₐ[𝕜] FractionRing (MvPolynomial (Fin k) 𝕜) :=
    AlgEquiv.ofRingEquiv (f := h4e) h4prop
  haveI hdomC : IsDomain (TensorProduct 𝕜 ↥C₁ (FractionRing (MvPolynomial (Fin k) 𝕜))) :=
    isDomain_tensor_fractionRing 𝕜 (Fin k) ↥C₁
  have hdomB : IsDomain (TensorProduct 𝕜 ↥B₁ ↥C₁) := by
    have hAB : TensorProduct 𝕜 ↥B₁ ↥C₁ ≃ₐ[𝕜]
        TensorProduct 𝕜 (FractionRing (MvPolynomial (Fin k) 𝕜)) ↥C₁ :=
      Algebra.TensorProduct.congr hBalg (AlgEquiv.refl : ↥C₁ ≃ₐ[𝕜] ↥C₁)
    have hBC : TensorProduct 𝕜 (FractionRing (MvPolynomial (Fin k) 𝕜)) ↥C₁ ≃ₐ[𝕜]
        TensorProduct 𝕜 ↥C₁ (FractionRing (MvPolynomial (Fin k) 𝕜)) :=
      Algebra.TensorProduct.comm 𝕜 _ _
    have hfin : TensorProduct 𝕜 ↥B₁ ↥C₁ ≃+* TensorProduct 𝕜 ↥C₁
        (FractionRing (MvPolynomial (Fin k) 𝕜)) := (hAB.trans hBC).toRingEquiv
    exact Function.Injective.isDomain
      (hfin : TensorProduct 𝕜 ↥B₁ ↥C₁ →+* TensorProduct 𝕜 ↥C₁
        (FractionRing (MvPolynomial (Fin k) 𝕜))) hfin.injective
  obtain ⟨e1⟩ := hstep1
  obtain ⟨e2⟩ := hstep2
  have hIso : T.tensor ≅ ↧(TensorProduct 𝕜 ↥B₁ ↥C₁) := e1 ≪≫ e2
  exact Function.Injective.isDomain
    (hIso.commRingCatIsoToRingEquiv : ↥T.tensor →+* TensorProduct 𝕜 ↥B₁ ↥C₁)
    hIso.commRingCatIsoToRingEquiv.injective

end

end Work.CY3Stab.Prod
