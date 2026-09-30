import Mathlib
import Submission.Work.Pi6.BOCK.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

/-! ## Naturality of the comparison `C_*(X;ℤ) ⊗ ℤ ≅ C_*(X;ℤ)` -/

/-- The unit isomorphism `expTens K ℤ ≅ K` is natural in the complex `K`. -/
theorem expTensUnitIso_natural (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K') :
    expTensMapHom K K' φ (𝟙_ (ModuleCat ℤ)) ≫ (Work.SSS.expTensUnitIso K').hom =
      (Work.SSS.expTensUnitIso K).hom ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  rw [expTensMapHom_f,
    show (Work.SSS.expTensUnitIso K').hom.f n = (ρ_ (K'.X n)).hom from rfl,
    show (Work.SSS.expTensUnitIso K).hom.f n = (ρ_ (K.X n)).hom from rfl]
  exact MonoidalCategory.rightUnitor_naturality (φ.f n)

/-! ## Naturality of the comparison `K ⊗ M ≅ (tensorRight M).obj K` -/

/-- The naive tensor complex `expTens K M` is the image of `K` under the functor `- ⊗ M`; this
isomorphism is natural in `K`. -/
theorem expTensNatIso_natural (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K')
    (M : ModuleCat ℤ) :
    ((MonoidalCategory.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).map φ ≫
        (Work.SSS.tensorRightMapHomIsoExpTens K' M).hom =
      (Work.SSS.tensorRightMapHomIsoExpTens K M).hom ≫ expTensMapHom K K' φ M := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [Work.SSS.tensorRightMapHomIsoExpTens, expTensMapHom]

/-- The comparison `expTens K M ≅ (tensorRight M).obj K` in the direction used below, natural in
`K`. -/
def expTensIsoNat (M : ModuleCat ℤ) (K : ChainComplex (ModuleCat ℤ) ℕ) :
    Work.SSS.expTens K M ≅ ((MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K :=
  (Work.SSS.tensorRightMapHomIsoExpTens K M).symm

/-- Naturality of `expTensIsoNat` in the complex. -/
theorem expTensIsoNat_natural (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K')
    (M : ModuleCat ℤ) :
    expTensMapHom K K' φ M ≫ (expTensIsoNat M K').hom =
      (expTensIsoNat M K).hom ≫
        ((MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [expTensIsoNat, Work.SSS.tensorRightMapHomIsoExpTens, expTensMapHom]

/-! ## Multiplication by `p` on the coefficient extension -/

/-- Whiskering on the left with a fixed object, as an additive homomorphism. -/
def whiskerLeftAddHom (X Y Z : ModuleCat ℤ) : (Y ⟶ Z) →+ (X ⊗ Y ⟶ X ⊗ Z) where
  toFun f := X ◁ f
  map_zero' := MonoidalPreadditive.whiskerLeft_zero
  map_add' f g := MonoidalPreadditive.whiskerLeft_add f g

/-- The coefficient extension of "multiplication by `p`" is multiplication by `p`. -/
theorem expTensHom_mulP (p : ℕ) (K : ChainComplex (ModuleCat ℤ) ℕ) :
    Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p) = (p : ℤ) • 𝟙 (Work.SSS.expTens K zZ) := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [Work.SSS.expTensHom_f, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
  show K.X i ◁ Work.Pi6.EMZ.mulP p = (p : ℤ) • 𝟙 (K.X i ⊗ zZ)
  rw [show Work.Pi6.EMZ.mulP p = (p : ℤ) • 𝟙 zZ from rfl,
    show K.X i ◁ ((p : ℤ) • 𝟙 zZ) = (p : ℤ) • (K.X i ◁ 𝟙 zZ) from
      map_zsmul (whiskerLeftAddHom (K.X i) zZ zZ) p (𝟙 zZ),
    MonoidalCategory.whiskerLeft_id]

/-- Homology commutes with integer multiples of the identity. -/
theorem homologyMap_smul_id (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (a : ℤ) :
    HomologicalComplex.homologyMap (a • 𝟙 K) n = a • 𝟙 (K.homology n) := by
  have h : HomologicalComplex.homologyMap (a • 𝟙 K) n = a • HomologicalComplex.homologyMap (𝟙 K) n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map_smul a (𝟙 K)
  rw [HomologicalComplex.homologyMap_id] at h
  exact h

/-- On homology, multiplication by `p` of the coefficients acts as `x ↦ p • x`. -/
theorem homologyMap_expTensHom_mulP (p : ℕ) (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (y : ↥((Work.SSS.expTens K zZ).homology n)) :
    (HomologicalComplex.homologyMap (Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p)) n).hom y =
      (p : ℤ) • y := by
  rw [expTensHom_mulP p K, homologyMap_smul_id]
  exact Work.Pi6.EMZ.smul_id_hom_apply p _ y

end

end Work.Pi6.BOCK
