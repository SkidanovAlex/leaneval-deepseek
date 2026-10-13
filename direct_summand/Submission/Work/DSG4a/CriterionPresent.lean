import Mathlib
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSG4a.F1Interface
import Submission.Work.DSG4a.exists_present_modelModule
import Submission.Work.DSG4a.chainSplit_iff_isUnimodular
import Submission.Work.DSG4a.isSplitMono_rgUnit_iff_chainSplit

/-!
# DSG4a: the model criterion in coordinates

This file records the *join* between the areas `F1`/`COH` and the algebra of this area, on the
`A`-side (the base-change side is the subject of `NOTES.md`, item 3).

The areas `F1` and `COH` are supposed to produce, for `f : X ⟶ Spec A` proper and projective
over Noetherian `A`,

* a K-projective finite free complex `P` with a quasi-isomorphism onto the Čech complex of a
  finite affine cover of `X`,
* a coaugmentation `cc : A[0] ⟶ P` whose image in `D(A)` is the challenge unit
  (`F1UnitCompatible`), and
* a choice of bases `b₀ : P.X 0 ≃ₗ (Fin m → A)`, `b₁ : P.X (-1) ≃ₗ (Fin n → A)`.

Given exactly that data, `dsplit_iff_isUnimodular_present` below states the criterion in
coordinates: `IsSplitMono (rgUnit A X f)` is equivalent to the unimodularity (`Module.IsUnimodular`)
of the class of `coaugVector P b₀ cc` in the finitely presented module
`A^m ⧸ im (diffMatrix P b₀ b₁)`.  This is the hypothesis `hcrit` of
`Work.DSG4a.area_G4a_localGlobal_of_models` (and of the presentation form
`area_G4a_localGlobal_of_presentation`), obtained from `F1 + COH` alone.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSG4a

universe u

namespace Criterion

/-- The matrix of the differential `d⁻¹ : P.X (-1) ⟶ P.X 0` of a complex `P` in the bases
`b₀` (of `P.X 0`) and `b₁` (of `P.X (-1)`). -/
noncomputable def diffMatrix {A : Type u} [CommRing A] {m n : ℕ}
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (b₀ : P.X 0 ≃ₗ[A] (Fin m → A))
    (b₁ : P.X (-1) ≃ₗ[A] (Fin n → A)) : Fin m → Fin n → A :=
  fun i j => b₀ ((P.d (-1) 0).hom (b₁.symm (Pi.single j 1))) i

/-- The coordinates of the coaugmentation element `cc.f 0 1` of a complex `P` in the basis
`b₀` of `P.X 0`. -/
noncomputable def coaugVector {A : Type u} [CommRing A] {m : ℕ}
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (b₀ : P.X 0 ≃ₗ[A] (Fin m → A))
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) : Fin m → A :=
  fun i => b₀ (coaugElem P cc) i

/-- **The chain-level criterion in coordinates.**  Choosing bases of `P.X 0` and `P.X (-1)`
turns `ChainSplit P cc` into the unimodularity of the class of the coaugmentation vector in
`A^m ⧸ im (diffMatrix P b₀ b₁)`. -/
theorem chainSplit_iff_isUnimodular_present {A : Type u} [CommRing A] {m n : ℕ}
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P)
    (b₀ : P.X 0 ≃ₗ[A] (Fin m → A)) (b₁ : P.X (-1) ≃ₗ[A] (Fin n → A)) :
    Criterion.ChainSplit P cc ↔
      Module.IsUnimodular A (presentMk (diffMatrix P b₀ b₁) (coaugVector P b₀ cc)) := by
  obtain ⟨Φ, hΦ⟩ := exists_present_modelModule P b₀ b₁
  rw [chainSplit_iff_isUnimodular]
  have hkey : modelElem P cc =
      Φ (presentMk (diffMatrix P b₀ b₁) (coaugVector P b₀ cc)) :=
    (hΦ (coaugElem P cc)).symm
  rw [hkey]
  exact isUnimodular_apply_iff Φ (presentMk (diffMatrix P b₀ b₁) (coaugVector P b₀ cc))

/-- **The criterion for the challenge unit, in coordinates.**  With the data produced by
`F1 + COH` (a K-projective model `P`, a coaugmentation `cc` compatible with the challenge unit,
and bases), `IsSplitMono (rgUnit A X f)` is equivalent to the unimodularity of the class of
`coaugVector P b₀ cc` in `A^m ⧸ im (diffMatrix P b₀ b₁)`. -/
theorem dsplit_iff_isUnimodular_present {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    [HasDerivedCategory (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)] {m n : ℕ}
    (P : CochainComplex (ModuleCat.{u} A) ℤ) [P.IsKProjective]
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅ DerivedCategory.Q.obj P)
    (he : Criterion.F1UnitCompatible P cc e)
    (b₀ : P.X 0 ≃ₗ[A] (Fin m → A)) (b₁ : P.X (-1) ≃ₗ[A] (Fin n → A)) :
    IsSplitMono (DSMap.rgUnit A X f) ↔
      Module.IsUnimodular A (presentMk (diffMatrix P b₀ b₁) (coaugVector P b₀ cc)) :=
  (isSplitMono_rgUnit_iff_chainSplit X f P cc e he).trans
    (chainSplit_iff_isUnimodular_present P cc b₀ b₁)

end Criterion

end Work.DSG4a
