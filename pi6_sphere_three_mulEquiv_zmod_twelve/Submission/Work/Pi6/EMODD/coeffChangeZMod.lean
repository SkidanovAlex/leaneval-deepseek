import Mathlib
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.SSS.ExpTensLES
import Submission.Work.SSS.ExpTens
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Work.Pi6.EMODD

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

attribute [local instance 2000] Submodule.Quotient.module TensorProduct.instModule

noncomputable section

/-!
# Coefficient change `H_n(K ⊗ ℤ/p) ≅ H_n(K) ⊗ ℤ/p`

For a chain complex `K` of `ℤ`-modules with degreewise flat terms and `H_{n-1}(K)` free (hence
torsion-free), tensoring the coefficient short exact sequence `0 → ℤ --p--> ℤ → ℤ/p → 0` with `K`
gives the short exact sequence of complexes
`0 → K --p--> K → K ⊗ ℤ/p → 0`, whose long exact homology sequence reads

`H_n(K) --·p--> H_n(K) → H_n(K ⊗ ℤ/p) --δ--> H_{n-1}(K) --·p--> H_{n-1}(K)`.

Because `H_{n-1}(K)` is torsion-free, the connecting map `δ` vanishes, so
`H_n(K ⊗ ℤ/p) ≅ H_n(K)/pH_n(K) ≅ H_n(K) ⊗ ℤ/p`.
-/

/-! ## Multiplication by `p` on the coefficient extension `K ⊗ ℤ` -/

/-- Whiskering on the left with a fixed object, as an additive homomorphism. -/
def whiskerLeftAddHomE (X Y Z : ModuleCat ℤ) : (Y ⟶ Z) →+ (X ⊗ Y ⟶ X ⊗ Z) where
  toFun f := X ◁ f
  map_zero' := MonoidalPreadditive.whiskerLeft_zero
  map_add' f g := MonoidalPreadditive.whiskerLeft_add f g

/-- The coefficient extension of "multiplication by `p`" is multiplication by `p`. -/
theorem expTensHom_mulP_E (p : ℕ) (K : ChainComplex (ModuleCat ℤ) ℕ) :
    Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p) =
      (p : ℤ) • 𝟙 (Work.SSS.expTens K Work.Pi6.EMZ.zZ) := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [Work.SSS.expTensHom_f, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
  show K.X i ◁ Work.Pi6.EMZ.mulP p = (p : ℤ) • 𝟙 (K.X i ⊗ Work.Pi6.EMZ.zZ)
  rw [show Work.Pi6.EMZ.mulP p = (p : ℤ) • 𝟙 Work.Pi6.EMZ.zZ from rfl]
  rw [show K.X i ◁ ((p : ℤ) • 𝟙 Work.Pi6.EMZ.zZ) =
      (whiskerLeftAddHomE (K.X i) Work.Pi6.EMZ.zZ Work.Pi6.EMZ.zZ)
        ((p : ℤ) • 𝟙 Work.Pi6.EMZ.zZ) from rfl]
  rw [map_zsmul]
  rw [show (whiskerLeftAddHomE (K.X i) Work.Pi6.EMZ.zZ Work.Pi6.EMZ.zZ) (𝟙 Work.Pi6.EMZ.zZ) =
      𝟙 (K.X i ⊗ Work.Pi6.EMZ.zZ) from MonoidalCategory.whiskerLeft_id (K.X i) Work.Pi6.EMZ.zZ]

/-- Homology commutes with integer multiples of the identity chain map. -/
theorem homologyMap_smul_id_E (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (a : ℤ) :
    HomologicalComplex.homologyMap (a • 𝟙 K) n = a • 𝟙 (K.homology n) := by
  have h : HomologicalComplex.homologyMap (a • 𝟙 K) n =
      a • HomologicalComplex.homologyMap (𝟙 K) n :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map_smul a (𝟙 K)
  rw [HomologicalComplex.homologyMap_id] at h
  exact h

/-- On homology, multiplication by `p` in the coefficients acts as `y ↦ p • y`. -/
theorem homologyMapExpTensMulP_E (p : ℕ) (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (y : ↥((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n)) :
    (HomologicalComplex.homologyMap (Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p)) n).hom y =
      (p : ℤ) • y := by
  rw [expTensHom_mulP_E p K, homologyMap_smul_id_E]
  exact Work.Pi6.EMZ.smul_id_hom_apply p _ y

/-- The underlying linear map of `p · 𝟙 M` is multiplication by `p`. -/
theorem smulHom_eq_lsmul (p : ℤ) (M : ModuleCat ℤ) :
    ((p) • 𝟙 M).hom = LinearMap.lsmul ℤ ↥M p := by
  ext x
  rw [LinearMap.lsmul_apply, Work.Pi6.EMZ.smul_id_hom_apply]
  exact (Int.cast_smul_eq_zsmul (R := ℤ) p x).symm

/-- Pointwise form of `smulHom_eq_lsmul`. -/
theorem smulHom_apply_eq (p : ℤ) (M : ModuleCat ℤ) (x : ↥M) :
    ((p) • 𝟙 M).hom x = (LinearMap.lsmul ℤ ↥M p) x := by
  rw [LinearMap.lsmul_apply, Work.Pi6.EMZ.smul_id_hom_apply]
  exact (Int.cast_smul_eq_zsmul (R := ℤ) p x).symm

/-- **Injectivity of `·p` on the homology of `K ⊗ ℤ`.**  If `H_j(K)` is free (hence torsion-free)
and `p ≠ 0`, then multiplication by `p` is injective on `H_j(K ⊗ ℤ) ≅ H_j(K)`. -/
theorem monoHomologyMapMulP_E (p : ℕ) (hp : p ≠ 0) (K : ChainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    (hfree : Module.Free ℤ ↥(K.homology j)) :
    Mono (HomologicalComplex.homologyMap (Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p)) j) := by
  haveI : Module.IsTorsionFree ℤ ↥(K.homology j) := inferInstance
  let el := Iso.toLinearEquiv (HomologicalComplex.homologyMapIso (Work.SSS.expTensUnitIso K) j)
  haveI : Module.IsTorsionFree ℤ ↥((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology j) :=
    Function.Injective.moduleIsTorsionFree (R := ℤ) (fun y => el y) el.injective
      (fun r m => el.map_smul r m)
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hme : HomologicalComplex.homologyMap (Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p)) j
      = (p : ℤ) • 𝟙 ((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology j) := by
    rw [expTensHom_mulP_E, homologyMap_smul_id_E]
  rw [hme, ModuleCat.mono_iff_injective]
  intro x y hxy
  rw [smulHom_apply_eq, smulHom_apply_eq] at hxy
  exact (LinearMap.lsmul_injective hpz) hxy

/-! ## Transport of the range of `·p` along a linear equivalence -/

/-- A linear equivalence carries the range of `·p` on `A` onto the range of `·p` on `B`. -/
theorem map_range_smulHom_E {A B : ModuleCat ℤ} (el : ↥A ≃ₗ[ℤ] ↥B) (p : ℤ) :
    Submodule.map (el : ↥A →ₗ[ℤ] ↥B) (LinearMap.range ((p : ℤ) • 𝟙 A).hom) =
      LinearMap.range ((p : ℤ) • 𝟙 B).hom := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz⟩, hyx⟩
    refine ⟨el z, ?_⟩
    rw [← hyx, ← hz, Work.Pi6.EMZ.smul_id_hom_apply, Work.Pi6.EMZ.smul_id_hom_apply]
    exact (map_zsmul (el : ↥A →+ ↥B) p z).symm
  · rintro ⟨y, hy⟩
    have hy' : (p : ℤ) • y = x := by rw [← hy, Work.Pi6.EMZ.smul_id_hom_apply]
    refine Submodule.mem_map.mpr ⟨el.symm x, ?_, by simp⟩
    refine ⟨el.symm y, ?_⟩
    rw [Work.Pi6.EMZ.smul_id_hom_apply, ← hy']
    exact (map_zsmul (el.symm : ↥B →+ ↥A) p y).symm

/-! ## `M ⧸ pM ≅ M ⊗ ℤ/p` -/

/-- **`M ⧸ pM ≅ M ⊗[ℤ] ℤ/p`.**  Tensoring the presentation `0 → ℤ --p--> ℤ → ℤ/p → 0` with `M`
(right exactness) identifies `M ⊗ ℤ/p` with the cokernel of `·p` on `M`. -/
theorem quotTensorZMod (p : ℕ) (M : ModuleCat ℤ) :
    Nonempty (ModuleCat.of ℤ (↥M ⧸ (LinearMap.range (LinearMap.lsmul ℤ ↥M (p : ℤ)))) ≅
      (M ⊗ ModuleCat.of ℤ (ZMod p))) := by
  have hI : (Ideal.span {(p : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ↥M) =
      LinearMap.range (LinearMap.lsmul ℤ ↥M (p : ℤ)) := by
    rw [Submodule.smul_eq_map₂, Submodule.map₂_span_singleton_eq_map, Submodule.map_top]
  have e1 : ModuleCat.of ℤ (↥M ⧸ LinearMap.range (LinearMap.lsmul ℤ ↥M (p : ℤ))) ≅
      ModuleCat.of ℤ (↥M ⧸ ((Ideal.span {(p : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ↥M))) :=
    (Submodule.quotEquivOfEq _ _ hI.symm).toModuleIso
  have e2 : ModuleCat.of ℤ (↥M ⧸ ((Ideal.span {(p : ℤ)} : Ideal ℤ) • (⊤ : Submodule ℤ ↥M))) ≅
      ModuleCat.of ℤ (↥M ⊗[ℤ] (ℤ ⧸ (Ideal.span {(p : ℤ)} : Ideal ℤ))) :=
    ((TensorProduct.tensorQuotEquivQuotSMul ↥M (Ideal.span {(p : ℤ)})).symm).toModuleIso
  have e3 : ModuleCat.of ℤ (↥M ⊗[ℤ] (ℤ ⧸ (Ideal.span {(p : ℤ)} : Ideal ℤ))) ≅
      ModuleCat.of ℤ (↥M ⊗[ℤ] ZMod p) :=
    (TensorProduct.congr (LinearEquiv.refl ℤ ↥M)
      ((Int.quotientSpanNatEquivZMod p).toAddEquiv.toIntLinearEquiv)).toModuleIso
  exact ⟨e1.trans (e2.trans (e3.trans (Iso.refl _)))⟩

/-! ## The cokernel of the first map of a short exact sequence of complexes -/

/-- **Cokernel of the first map of a short exact complex.**  If
`A --f--> B --g--> C --δ--> A' --f'--> B'` is exact (three consecutive exactnesses) and `f'` is
injective, then `C ≅ B ⧸ im f`.  (The connecting map `δ` vanishes because its image lands in
`ker f' = 0`, so `g` is onto and its kernel is `im f`.) -/
theorem cokerIsoOfExact (L : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) (hL : L.ShortExact)
    (n : ℕ) (hn : 1 ≤ n) (hmono : Mono (HomologicalComplex.homologyMap L.f (n - 1))) :
    Nonempty (L.X₃.homology n ≅ ModuleCat.of ℤ
      (↥(L.X₂.homology n) ⧸ (LinearMap.range (HomologicalComplex.homologyMap L.f n).hom))) := by
  have hij : (ComplexShape.down ℕ).Rel n (n - 1) := by
    rw [ComplexShape.down_Rel]
    omega
  have hf' : Function.Injective (HomologicalComplex.homologyMap L.f (n - 1)).hom :=
    (ModuleCat.mono_iff_injective _).mp hmono
  have hex1 : Function.Exact (hL.δ n (n - 1) hij).hom
      (HomologicalComplex.homologyMap L.f (n - 1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hL.homology_exact₁ n (n - 1) hij)
  have hex2 : Function.Exact (HomologicalComplex.homologyMap L.f n).hom
      (HomologicalComplex.homologyMap L.g n).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hL.homology_exact₂ n)
  have hex3 : Function.Exact (HomologicalComplex.homologyMap L.g n).hom
      (hL.δ n (n - 1) hij).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hL.homology_exact₃ n (n - 1) hij)
  have hδ0 : (hL.δ n (n - 1) hij).hom = 0 := by
    ext x
    have h1 : (HomologicalComplex.homologyMap L.f (n - 1)).hom ((hL.δ n (n - 1) hij).hom x) =
        (HomologicalComplex.homologyMap L.f (n - 1)).hom 0 := by
      rw [map_zero]
      exact (hex1 ((hL.δ n (n - 1) hij).hom x)).mpr ⟨x, rfl⟩
    exact hf' h1
  have hg : Function.Surjective (HomologicalComplex.homologyMap L.g n).hom := fun y =>
    Set.mem_range.mp ((hex3 y).mp (by rw [hδ0]; rfl))
  have hker : LinearMap.ker (HomologicalComplex.homologyMap L.g n).hom =
      LinearMap.range (HomologicalComplex.homologyMap L.f n).hom := by
    ext y
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact hex2 y
  have e1 : L.X₃.homology n ≅ ModuleCat.of ℤ (↥(L.X₂.homology n) ⧸
        (LinearMap.ker (HomologicalComplex.homologyMap L.g n).hom)) :=
    ((LinearMap.quotKerEquivOfSurjective _ hg).toModuleIso).symm
  have e2 : ModuleCat.of ℤ (↥(L.X₂.homology n) ⧸
        (LinearMap.ker (HomologicalComplex.homologyMap L.g n).hom)) ≅
      ModuleCat.of ℤ (↥(L.X₂.homology n) ⧸
        (LinearMap.range (HomologicalComplex.homologyMap L.f n).hom)) :=
    (Submodule.quotEquivOfEq _ _ hker).toModuleIso
  exact ⟨e1.trans e2⟩

/-! ## The main theorem -/

theorem coeffChangeZMod (p : ℕ) [Fact p.Prime] (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (hn : 1 ≤ n) (hS : (Work.Pi6.EMZ.coeffSES p).ShortExact)
    (hflat : ∀ i : ℕ, Module.Flat ℤ (K.X i))
    (hfree : Module.Free ℤ ↥(K.homology (n - 1))) :
    Nonempty ((Work.SSS.expTens K (ModuleCat.of ℤ (ZMod p))).homology n ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj (K.homology n) (ModuleCat.of ℤ (ZMod p))) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hL : (Work.SSS.expTensShort K (Work.Pi6.EMZ.coeffSES p)).ShortExact :=
    Work.SSS.expTensShort_shortExact _ hS hflat
  have hmono : Mono (HomologicalComplex.homologyMap
      (Work.SSS.expTensShort K (Work.Pi6.EMZ.coeffSES p)).f (n - 1)) :=
    monoHomologyMapMulP_E p hp0 K (n - 1) hfree
  obtain ⟨eC⟩ := cokerIsoOfExact (Work.SSS.expTensShort K (Work.Pi6.EMZ.coeffSES p)) hL n hn hmono
  -- describe the first map as multiplication by `p` on `H_n(K ⊗ ℤ)`
  have hme : (HomologicalComplex.homologyMap
        (Work.SSS.expTensShort K (Work.Pi6.EMZ.coeffSES p)).f n) =
      (p : ℤ) • 𝟙 ((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n) := by
    change HomologicalComplex.homologyMap (Work.SSS.expTensHom K (Work.Pi6.EMZ.mulP p)) n =
      (p : ℤ) • 𝟙 ((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n)
    rw [expTensHom_mulP_E, homologyMap_smul_id_E]
  rw [hme] at eC
  -- the identification `H_n(K ⊗ ℤ) ≅ H_n(K)`
  let el : ↥((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n) ≃ₗ[ℤ] ↥(K.homology n) :=
    Iso.toLinearEquiv (HomologicalComplex.homologyMapIso (Work.SSS.expTensUnitIso K) n)
  have eT : ModuleCat.of ℤ (↥((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n) ⧸
        (LinearMap.range (((p : ℤ)) • 𝟙
          ((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n)).hom)) ≅
      ModuleCat.of ℤ (↥(K.homology n) ⧸
        (LinearMap.range (((p : ℤ)) • 𝟙 (K.homology n)).hom)) :=
    (Submodule.Quotient.equiv
      (LinearMap.range (((p : ℤ)) • 𝟙 ((Work.SSS.expTens K Work.Pi6.EMZ.zZ).homology n)).hom)
      (LinearMap.range (((p : ℤ)) • 𝟙 (K.homology n)).hom) el
      (map_range_smulHom_E el (p : ℤ))).toModuleIso
  have eQ : ModuleCat.of ℤ (↥(K.homology n) ⧸
        (LinearMap.range (((p : ℤ)) • 𝟙 (K.homology n)).hom)) ≅
      (K.homology n ⊗ ModuleCat.of ℤ (ZMod p)) := by
    rw [smulHom_eq_lsmul (p : ℤ) (K.homology n)]
    exact (quotTensorZMod p (K.homology n)).some
  exact ⟨eC.trans (eT.trans eQ)⟩

end

end Work.Pi6.EMODD
