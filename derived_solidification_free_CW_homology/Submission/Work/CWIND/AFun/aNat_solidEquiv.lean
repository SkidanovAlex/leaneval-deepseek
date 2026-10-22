import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.AFun.Setup
import Submission.Work.CWIND.AFun.Gext_solidEquiv
import Submission.Work.CWIND.AFun.Ac_solidEquiv

namespace Work.CWIND.AFun

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-! ## The factorisation of `a` through `Aconst`

The comparison map `a X : ℤ[X] ⟶ A(X)` of `CWIND/AFun/exists_aNat` factors as
`ℤ[X] --Ac--> Aconst X --Gext--> A(X)`, where `Ac` is the extra-degeneracy comparison
(`Setup.Ac`, a solid-equivalence) and `Gext` is the map induced by the constant simplices
(`Setup.Gext`, a solid-equivalence by levelwise homotopy invariance). -/

/-- The factorisation `a.app X = Ac X ≫ Gext X`.  Both sides are maps out of the single complex
on `ℤ[X]`, so by `HomologicalComplex.from_single_hom_ext` it suffices to compare degree `0`
components: `(Ac X).f 0 ≫ (Gext X).f 0 = (singleObjXSelf …).hom ≫ (AconstXIso X 0).inv ≫
(AconstXIso X 0).hom ≫ a0 X = (a.app X).f 0` by `ha`. -/
lemma Ac_comp_Gext
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor)
    (ha : ∀ (X : TopCat.{0}),
        (a.app X).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫ a0 X)
    (X : TopCat.{0}) :
    Ac X ≫ Gext X = a.app X := by
  apply HomologicalComplex.from_single_hom_ext (j := 0)
  rw [HomologicalComplex.comp_f, Ac_f_zero, Gext_f_zero, ha X]
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- **CWIND/T4.** For a Hausdorff space `X`, the comparison map `a(X) : ℤ[X] ⟶ A(X)` of
`CWIND/AFun/exists_aNat` is a solid-equivalence (becomes an isomorphism after derived
solidification).  This is REFS/05 section 1: the inclusion of the constant simplices
`X ⟶ X^{Δⁿ}` is a homotopy equivalence for each `n`, so by homotopy invariance (`HIProp`) each
component of the map of constant simplicial objects `const ℤ[X] ⟶ (n ↦ ℤ[X^{Δⁿ}])` is a
solid-equivalence; the alternating face complex of a constant simplicial object carries an extra
degeneracy, so it is homotopy equivalent to `ℤ[X]` concentrated in degree `0`; then
`ToolkitProp.levelwise` gives the claim.

The hypotheses `hconst` (homotopy invariance for the constant maps `X ⟶ X^{Δⁿ}`) and `ha` (the
defining property of `a`) are supplied separately so that this proof only performs the
simplicial-object and extra-degeneracy argument.  `DerivedProp` is needed only to translate
solid-equivalences into isomorphisms after `D.L` and vice versa. -/
theorem aNat_solidEquiv (hD : DerivedProp) [isSolid.ι.IsRightAdjoint] (D : DerivedPackage)
    (hHI : HIProp) (hTK : ToolkitProp)
    (a : freeLightCondAbOfTopFunctor ⋙ (CochainComplex.singleFunctor LightCondAb 0) ⟶ AFunctor)
    (ha : ∀ (X : TopCat.{0}),
        (a.app X).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (freeLightCondAbOfTop X)).hom ≫ a0 X)
    (hconst : ∀ (X : TopCat.{0}) [T2Space X] (n : ℕ), SolidEquiv (dFree (constMap X n)))
    (X : TopCat.{0}) [T2Space X] : SolidEquiv ((DerivedCategory.Q).map (a.app X)) := by
  have h₁ : SolidEquiv ((DerivedCategory.Q).map (Gext X)) := Gext_solidEquiv hTK hconst X
  have h₂ : SolidEquiv ((DerivedCategory.Q).map (Ac X)) := Ac_solidEquiv hTK X
  have h := hTK.comp (DerivedCategory.Q.map (Ac X)) (DerivedCategory.Q.map (Gext X)) h₂ h₁
  rw [← Functor.map_comp] at h
  rw [Ac_comp_Gext a ha X] at h
  exact h

end Work.CWIND.AFun
