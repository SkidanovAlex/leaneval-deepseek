import Mathlib
import Submission.Work.DSAMR.Defs

universe u

namespace Work.DSAMR

/-- `DSMap.Mix2.unitA ψ` is the `A`-linear map induced by `ψ`; in particular it sends `1` to
`ψ 1 = 1`. -/
lemma unitA_apply {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W) (x : A) :
    ModuleCat.Hom.hom (DSMap.Mix2.unitA ψ) x = ψ x := rfl

/-- **The unit of `ρ` at the level of the extended complex.**

`hρ` is the frozen compatibility hypothesis of `DSMap.Mix2.modSplit_of_almostAcyc`
(`ε ≫ ρ.f 0 ≫ iso.hom = unitA ψ ≫ map eK`, an equation of morphisms `A → K.X 0` over `A`).
The statement extracts the element equation which that morphism equation expresses: `ρ.f 0` sends
the unit `ε 1 ∈ P⁰` to the image of `eK 1` under the isomorphism `K.X 0 ≅ (K.extend
embeddingUpNat).X 0`, i.e. to `e' 1`, where `e' := eK ≫ (K.extendXIso …).inv` is the transported
coaugmentation of `Work.DSAMR.almostAcycZ_extend`.

Hints.  `DSMap.Mix2.unitA ψ` is the `A`-linear map `A → W` induced by `ψ`, so `(unitA ψ).hom 1 = 1`.
Apply `DFunLike.congr_fun`/`ConcreteCategory.congr_hom` (or `congrArg (fun f => f 1)`) to `hρ`,
simplify with `CategoryTheory.ModuleCat` composition being function composition, and finish with
`Iso.inv_hom_id_apply` / `(iso.inv ≫ iso.hom).hom = id`. -/
theorem rho_f_zero_unit {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    (K : CochainComplex (ModuleCat.{u} W) ℕ) (eK : ModuleCat.of W W ⟶ K.X 0)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex _).obj
      (K.extend ComplexShape.embeddingUpNat))
    (hρ : CategoryTheory.CategoryStruct.comp ε (CategoryTheory.CategoryStruct.comp (ρ.f 0)
      ((ModuleCat.restrictScalars ψ).map
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom)) =
        CategoryTheory.CategoryStruct.comp (DSMap.Mix2.unitA ψ)
          ((ModuleCat.restrictScalars ψ).map eK)) :
    ((ρ.f 0) (ε.hom (1 : A)) : (K.extend ComplexShape.embeddingUpNat).X 0) =
      (CategoryTheory.CategoryStruct.comp eK
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv).hom (1 : W) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom hρ (1 : A)
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at h
  -- `h` is now the element equation `iso.hom (ρ⁰ (ε 1)) = eK 1` (up to the restricted scalars),
  -- with the two outer composites expanded; the two remaining rewrites are the `restrictScalars`
  -- and `unitA` evaluations.  We assemble it with `Eq.trans`, whose definitional-equality checks
  -- are performed at the default transparency (needed because the coaugmentation lives on the
  -- `ℤ`-indexed extension, where `embeddingUpNat.f 0` and `0` are only propositionally equal).
  have key : ModuleCat.Hom.hom
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom
        (ModuleCat.Hom.hom (ρ.f 0) (ModuleCat.Hom.hom ε 1)) =
      ModuleCat.Hom.hom eK 1 :=
    (ModuleCat.restrictScalars.map_apply ψ
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom
        (ModuleCat.Hom.hom (ρ.f 0) (ModuleCat.Hom.hom ε 1))).symm.trans
      (h.trans ((ModuleCat.restrictScalars.map_apply ψ eK
        (ModuleCat.Hom.hom (DSMap.Mix2.unitA ψ) 1)).trans
        (by rw [unitA_apply, map_one])))
  have hfin : ModuleCat.Hom.hom
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv
        (ModuleCat.Hom.hom
          (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom
          (ModuleCat.Hom.hom (ρ.f 0) (ModuleCat.Hom.hom ε 1))) =
      ModuleCat.Hom.hom (ρ.f 0) (ModuleCat.Hom.hom ε 1) :=
    LinearEquiv.symm_apply_apply
      (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).toLinearEquiv
      (ModuleCat.Hom.hom (ρ.f 0) (ModuleCat.Hom.hom ε 1))
  have hcomp : ModuleCat.Hom.hom
        (CategoryTheory.CategoryStruct.comp eK
          (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv) 1 =
      ModuleCat.Hom.hom
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv
        (ModuleCat.Hom.hom eK 1) :=
    ModuleCat.comp_apply eK _ 1
  exact hfin.symm.trans
    ((congrArg (ModuleCat.Hom.hom
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv) key).trans
      hcomp.symm)

end Work.DSAMR
