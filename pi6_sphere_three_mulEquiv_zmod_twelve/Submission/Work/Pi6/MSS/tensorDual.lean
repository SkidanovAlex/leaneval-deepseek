import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Pi6.MSS.TensorDefs
import Submission.Work.Pi6.MSS.TensorAux
import Submission.Work.SSSR.tensorComplexIsoExpTens
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The dual of the coefficient-extended tensor complex

This file proves `Work.Pi6.MSS.tensorDual`: for a field `𝕜`, a chain complex `C` of `𝕜`-modules,
a finite dimensional `𝕜`-module `V` and a natural number `n`,

`Hⁿ(Hom_𝕜(C_* ⊗ V, 𝕜)) ≅ Hⁿ(Hom_𝕜(C_*, 𝕜)) ⊗_𝕜 V^*`,

where `V^* = V →ₗ[𝕜] 𝕜`.

The proof has three steps, each proved here as a separate lemma:

* `tensorC_iso_expTens` : the tensor complex `C ⊗ single₀ V` (with the complex concentrated in
  degree `0` at `V`) is the naive coefficient extension `expTens C V` (`X n = C.X n ⊗ V`,
  `d = d ⊗ id`).  This is the `CommRing`-generalisation of
  `Work.SSS.tensorComplexIsoExpTens`, assembled from the collapse/section pair `Work.SSSR.split`.
* `coTensC_iso_dualExpTens` : the duality `Hom(M ⊗ V, 𝕜) ≅ Hom(M, 𝕜) ⊗ V^*` for finite
  dimensional `V` (the linear equivalence `phiLin`, natural in `M`) upgrades to an isomorphism of
  cochain complexes between `dualComplex 𝕜 (expTens 𝕜 C V)` and
  `coTensC 𝕜 (dualComplex 𝕜 C) (dualMod 𝕜 V)`.
* `coTensC_homology` : over a field, homology commutes with tensoring by a module:
  `Hⁿ(coTensC 𝕜 K W) ≅ Hⁿ(K) ⊗ W`.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.MSS

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## Step 1: the coefficient extension `tensorC` is the naive tensor complex -/

/-- The tensor complex `Work.Pi6.MSS.tensorC 𝕜 C V` of a chain complex with the complex
concentrated in degree `0` at `V` is isomorphic to the naive coefficient extension
`Work.Pi6.MSS.expTens 𝕜 C V`. -/
theorem tensorC_iso_expTens (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜]
    (C : ChainComplex (ModuleCat 𝕜) ℕ) (V : ModuleCat 𝕜) :
    Nonempty (Work.Pi6.MSS.tensorC 𝕜 C V ≅ Work.Pi6.MSS.expTens 𝕜 C V) := by
  haveI : ∀ n, IsIso ((Work.SSSR.split C V).f n) := fun n =>
    ⟨Work.SSSR.collapseX C V n, Work.SSSR.splitX_collapseX C V n, Work.SSSR.collapseX_splitX C V n⟩
  haveI : IsIso (Work.SSSR.split C V) := HomologicalComplex.Hom.isIso_of_components _
  exact ⟨(asIso (Work.SSSR.split C V)).symm⟩

/-! ## Step 2: duality `Hom(M ⊗ V, 𝕜) ≅ Hom(M, 𝕜) ⊗ V^*` -/

/-- The `𝕜`-linear equivalence `Hom(M ⊗ V, 𝕜) ≅ Hom(M, 𝕜) ⊗ V^*`, for `V` finite dimensional:
on `f ⊗ g` it is the map `m ⊗ v ↦ f m * g v`. -/
noncomputable def phiLin (V : ModuleCat 𝕜) [FiniteDimensional 𝕜 V]
    (M : Type) [AddCommGroup M] [Module 𝕜 M] :
    TensorProduct 𝕜 (M →ₗ[𝕜] 𝕜) (↥V →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
      ((TensorProduct 𝕜 M ↥V) →ₗ[𝕜] 𝕜) :=
  haveI : Module.Finite 𝕜 (↥V →ₗ[𝕜] 𝕜) := inferInstance
  haveI : Module.Projective 𝕜 (↥V →ₗ[𝕜] 𝕜) := inferInstance
  (LinearEquiv.ofBijective (dualTensorHom 𝕜 M (↥V →ₗ[𝕜] 𝕜))
      (dualTensorHom_bijective_of_finite_projective_right)).trans
    (TensorProduct.lift.equiv (RingHom.id 𝕜) M ↥V 𝕜)

lemma phiLin_tmul (V : ModuleCat 𝕜) [FiniteDimensional 𝕜 V] (M : Type) [AddCommGroup M] [Module 𝕜 M]
    (f : M →ₗ[𝕜] 𝕜) (g : ↥V →ₗ[𝕜] 𝕜) (x : M) (y : ↥V) :
    phiLin V M (TensorProduct.tmul 𝕜 f g) (TensorProduct.tmul 𝕜 x y) = f x * g y := by
  rw [phiLin, LinearEquiv.trans_apply, TensorProduct.lift.equiv_apply,
    LinearEquiv.ofBijective_apply, dualTensorHom_apply, LinearMap.smul_apply]
  simp [smul_eq_mul]

lemma phiLin_natural (V : ModuleCat 𝕜) [FiniteDimensional 𝕜 V]
    (M M' : Type) [AddCommGroup M] [Module 𝕜 M] [AddCommGroup M'] [Module 𝕜 M']
    (u : M' →ₗ[𝕜] M) (f : M →ₗ[𝕜] 𝕜) (g : ↥V →ₗ[𝕜] 𝕜) :
    phiLin V M' (TensorProduct.tmul 𝕜 (f.comp u) g) =
      (phiLin V M (TensorProduct.tmul 𝕜 f g)).comp (LinearMap.rTensor ↥V u) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, phiLin_tmul, phiLin_tmul]
  rfl

lemma phiLin_natural_apply (V : ModuleCat 𝕜) [FiniteDimensional 𝕜 V]
    (M M' : Type) [AddCommGroup M] [Module 𝕜 M] [AddCommGroup M'] [Module 𝕜 M']
    (u : M' →ₗ[𝕜] M) (z : TensorProduct 𝕜 (M →ₗ[𝕜] 𝕜) (↥V →ₗ[𝕜] 𝕜)) :
    phiLin V M' (LinearMap.rTensor (↥V →ₗ[𝕜] 𝕜) (LinearMap.dualMap u) z) =
      (phiLin V M z).comp (LinearMap.rTensor ↥V u) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro f g
    rw [LinearMap.rTensor_tmul]
    have hd : LinearMap.dualMap u f = f.comp u := by
      ext x; rw [LinearMap.dualMap_apply, LinearMap.comp_apply]
    rw [hd]
    exact phiLin_natural V M M' u f g
  · intro z w hz hw
    simp only [map_add, hz, hw, LinearMap.add_comp]

/-- **Naturality of the duality isomorphism**, in the form of an isomorphism of cochain complexes:
`Hom(- ⊗ V, 𝕜) ≅ Hom(-, 𝕜) ⊗ V^*` upgrades to the naive coefficient extensions over the dual
complex of `C`. -/
noncomputable def coTensC_iso_dualExpTens (V : ModuleCat 𝕜) [FiniteDimensional 𝕜 V]
    (C : ChainComplex (ModuleCat 𝕜) ℕ) :
    coTensC 𝕜 (Work.Cohomology.dualComplex 𝕜 C) (dualMod 𝕜 V) ≅
      Work.Cohomology.dualComplex 𝕜 (expTens 𝕜 C V) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (phiLin V ↥(C.X n)).toModuleIso) ?_
  intro n m hnm
  rw [ComplexShape.up_Rel] at hnm
  subst hnm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
    ModuleCat.hom_ofHom, LinearEquiv.coe_toLinearMap, coTensC_d, ModuleCat.hom_whiskerRight,
    Work.Cohomology.dualComplex, CochainComplex.of_d]
  have h1 : ModuleCat.Hom.hom (Work.Cohomology.dualDiff 𝕜 C n)
      = LinearMap.dualMap (ModuleCat.Hom.hom (C.d (n + 1) n)) := by
    ext φ
    rw [Work.Cohomology.dualDiff_apply']
    rfl
  rw [show LinearMap.rTensor (↥V →ₗ[𝕜] 𝕜) (ModuleCat.Hom.hom (Work.Cohomology.dualDiff 𝕜 C n))
        = LinearMap.rTensor (↥V →ₗ[𝕜] 𝕜) (LinearMap.dualMap (ModuleCat.Hom.hom (C.d (n + 1) n)))
        from congrArg _ h1]
  have h3 : ModuleCat.Hom.hom (Work.Cohomology.dualDiff 𝕜 (expTens 𝕜 C V) n)
      = LinearMap.dualMap (LinearMap.rTensor ↥V (ModuleCat.Hom.hom (C.d (n + 1) n))) := by
    ext φ
    rw [Work.Cohomology.dualDiff_apply', expTens_d, ModuleCat.hom_whiskerRight]
    rfl
  rw [h3]
  exact (phiLin_natural_apply V ↥(C.X n) ↥(C.X (n + 1))
    (ModuleCat.Hom.hom (C.d (n + 1) n)) z).symm

/-! ## Step 3: homology commutes with tensoring by a module -/

/-- The differential of `Work.Pi6.MSS.coTensC` in arbitrary degrees. -/
lemma coTensC_d_eq (K : CochainComplex (ModuleCat 𝕜) ℕ) (W : ModuleCat 𝕜) (i j : ℕ) :
    (coTensC 𝕜 K W).d i j = K.d i j ▷ W := by
  by_cases h : (ComplexShape.up ℕ).Rel i j
  · rw [ComplexShape.up_Rel] at h
    subst h
    rw [coTensC_d]
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape K _ _ h]
    simp

/-- Over a field, the homology of the naive coefficient extension `coTensC 𝕜 K W` is the tensor
product of the homology of `K` with `W`. -/
theorem coTensC_homology (K : CochainComplex (ModuleCat 𝕜) ℕ) (W : ModuleCat 𝕜) (n : ℕ) :
    Nonempty ((coTensC 𝕜 K W).homology n ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 ↥(K.homology n) ↥W)) := by
  have e : ((K.sc n).map (tensorRight W)) ≅ ((coTensC 𝕜 K W).sc n) := by
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp only [Category.id_comp, Category.comp_id, ShortComplex.map_f,
        HomologicalComplex.shortComplexFunctor_obj_f]
      exact coTensC_d_eq K W _ _
    · simp only [Category.id_comp, Category.comp_id, ShortComplex.map_g,
        HomologicalComplex.shortComplexFunctor_obj_g]
      exact coTensC_d_eq K W _ _
  exact ⟨(ShortComplex.homologyFunctor (ModuleCat 𝕜)).mapIso e.symm ≪≫
    ShortComplex.mapHomologyIso (K.sc n) (tensorRight W)⟩

/-! ## Assembly -/

theorem tensorDual (𝕜 : Type) [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (V : ModuleCat 𝕜)
    [FiniteDimensional 𝕜 V] (n : ℕ) :
    Nonempty ((Work.Cohomology.dualComplex 𝕜 (Work.Pi6.MSS.tensorC 𝕜 C V)).homology n ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 ((Work.Cohomology.dualComplex 𝕜 C).homology n)
        (↥V →ₗ[𝕜] 𝕜))) := by
  obtain ⟨e₁⟩ := tensorC_iso_expTens 𝕜 C V
  haveI : IsIso (Work.Cohomology.dualComplexMap 𝕜 (tensorC 𝕜 C V) (expTens 𝕜 C V) e₁.hom) :=
    ⟨Work.Cohomology.dualComplexMap 𝕜 (expTens 𝕜 C V) (tensorC 𝕜 C V) e₁.inv,
      by rw [← Work.Cohomology.dualComplexMap_comp, e₁.inv_hom_id,
        Work.Cohomology.dualComplexMap_id],
      by rw [← Work.Cohomology.dualComplexMap_comp, e₁.hom_inv_id,
        Work.Cohomology.dualComplexMap_id]⟩
  have e₂ : Work.Cohomology.dualComplex 𝕜 (expTens 𝕜 C V) ≅
      coTensC 𝕜 (Work.Cohomology.dualComplex 𝕜 C) (dualMod 𝕜 V) :=
    (coTensC_iso_dualExpTens V C).symm
  obtain ⟨e₃⟩ := coTensC_homology (Work.Cohomology.dualComplex 𝕜 C) (dualMod 𝕜 V) n
  exact ⟨(Functor.mapIso
      (HomologicalComplex.homologyFunctor (ModuleCat 𝕜) (ComplexShape.up ℕ) n)
      ((asIso (Work.Cohomology.dualComplexMap 𝕜 (tensorC 𝕜 C V) (expTens 𝕜 C V)
        e₁.hom)).symm ≪≫ e₂)) ≪≫ e₃⟩

end

end Work.Pi6.MSS
