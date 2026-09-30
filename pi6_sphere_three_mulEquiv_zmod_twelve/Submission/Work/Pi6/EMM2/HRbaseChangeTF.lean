import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.K2Z.baseChangeFlat
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.Pi6.SRANGE.rTensor_injective_of_torsionFree_quotient
import Submission.Work.Pi6.EMM2.rTensorSubtypeInjective
import Submission.Work.Cohomology.uctDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Pi6.EMM2

noncomputable section

variable {𝕜 : Type} [CommRing 𝕜]

abbrev hrbcQc (𝕜 : Type) [CommRing 𝕜] : Type :=
  ↥((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of 𝕜 𝕜))

/-- Quotients by equal submodules. -/
noncomputable def hrbcQuotCongr {M : Type} [AddCommGroup M] [Module 𝕜 M]
    {p q : Submodule 𝕜 M} (h : p = q) : (M ⧸ p) ≃ₗ[𝕜] (M ⧸ q) :=
  h ▸ LinearEquiv.refl 𝕜 (M ⧸ p)

/-! ## Part A: ℤ-level flatness helpers -/

theorem hrbcIsTorsionFreeSubmodule {B : Type} [AddCommGroup B] [Module ℤ B]
    [Module.IsTorsionFree ℤ B] (S : Submodule ℤ B) : Module.IsTorsionFree ℤ ↥S := by
  refine ⟨fun r hr => ?_⟩
  have h := (‹Module.IsTorsionFree ℤ B›).isSMulRegular hr
  intro x y hxy
  apply Subtype.ext
  exact h (by simpa using congrArg (fun z : ↥S => (z : B)) hxy)

theorem hrbcFlatSubmoduleOfFree {B : Type} [AddCommGroup B] [Module ℤ B] [Module.Free ℤ B]
    (S : Submodule ℤ B) : Module.Flat ℤ ↥S := by
  haveI : Module.IsTorsionFree ℤ B := inferInstance
  haveI : Module.IsTorsionFree ℤ ↥S := hrbcIsTorsionFreeSubmodule S
  infer_instance

/-- A map whose cokernel is flat stays injective after tensoring with anything. -/
theorem hrbcLTensorSubtypeInjectiveOfFlat {A B : Type} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A →ₗ[ℤ] B) (hf : Function.Injective f)
    (hA : Module.Flat ℤ A) (hB : Module.Flat ℤ B)
    (hC : Module.Flat ℤ (B ⧸ LinearMap.range f)) (Q : Type) [AddCommGroup Q] [Module ℤ Q] :
    Function.Injective (LinearMap.lTensor Q f) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj Q f).mpr
    (rTensorSubtypeInjective (N := Q) f (LinearMap.range f).mkQ hf
      (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ]))
      (Submodule.mkQ_surjective _) hA hB hC)

/-! ## Part B: the flatness computations for the cycles and boundaries -/

theorem hrbcLTensorUctBInjective (K : ChainComplex (ModuleCat.{0,0} ℤ) ℕ) (m : ℕ)
    (Q : Type) [AddCommGroup Q] [Module ℤ Q]
    (hfree : ∀ i : ℕ, i ≤ m + 1 → Module.Free ℤ ↥(K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Function.Injective (LinearMap.lTensor Q (Work.Cohomology.uctB K m).subtype) := by
  haveI hFm : Module.Free ℤ ↥(K.X m) := hfree m (by omega)
  haveI hFm1 : Module.Free ℤ ↥(K.X (m - 1)) := hfree (m - 1) (by omega)
  haveI hFlatR : Module.Flat ℤ ↥(Work.Cohomology.uctR K m) := hrbcFlatSubmoduleOfFree _
  haveI hFlatZ : Module.Flat ℤ ↥(Work.Cohomology.uctZ K m) := hrbcFlatSubmoduleOfFree _
  haveI hFlatB : Module.Flat ℤ ↥(Work.Cohomology.uctB K m) := hrbcFlatSubmoduleOfFree _
  set j : ↥(Work.Cohomology.uctB K m) →ₗ[ℤ] ↥(Work.Cohomology.uctZ K m) :=
    (Work.Cohomology.uctB K m).subtype.codRestrict (Work.Cohomology.uctZ K m)
      (fun x => Work.Cohomology.uctB_le_uctZ K m x.2) with hj
  have hjrange : j.range = Work.Cohomology.uctH K m := by
    rw [hj, LinearMap.range_codRestrict, Submodule.range_subtype,
      Work.Cohomology.uctH_eq_comap]
  have hFlatZB : Module.Flat ℤ (↥(Work.Cohomology.uctZ K m) ⧸ Work.Cohomology.uctH K m) := by
    haveI : Module.Flat ℤ ↥(K.homology m) := by
      haveI := hTF
      infer_instance
    exact Module.Flat.of_linearEquiv
      (Work.Cohomology.uctIsoToLinearEquiv (Work.Cohomology.homology_iso_H K m).some).symm
  have hFlatJ : Module.Flat ℤ (↥(Work.Cohomology.uctZ K m) ⧸ j.range) := by
    rw [hjrange]; exact hFlatZB
  have hFlatQ : Module.Flat ℤ (↥(K.X m) ⧸ Work.Cohomology.uctZ K m) :=
    Module.Flat.of_linearEquiv (LinearMap.quotKerEquivRange (K.d m (m - 1)).hom)
  have hsub : (Work.Cohomology.uctB K m).subtype
      = (Work.Cohomology.uctZ K m).subtype ∘ₗ j := by
    rw [hj]
    exact (LinearMap.subtype_comp_codRestrict _ _ _).symm
  have hZinj : Function.Injective
      (LinearMap.lTensor Q (Work.Cohomology.uctZ K m).subtype) := by
    refine hrbcLTensorSubtypeInjectiveOfFlat _ (Submodule.subtype_injective _) hFlatZ
      (Module.Flat.of_free) ?_ Q
    rw [Submodule.range_subtype]; exact hFlatQ
  have hj_inj : Function.Injective (LinearMap.lTensor Q j) :=
    hrbcLTensorSubtypeInjectiveOfFlat _ (fun x y hxy => Subtype.ext
      (show (x : ↥(K.X m)) = (y : ↥(K.X m)) from congrArg Subtype.val hxy))
      hFlatB hFlatZ hFlatJ Q
  rw [hsub, LinearMap.lTensor_comp]
  exact hZinj.comp hj_inj

theorem hrbcLTensorUctZInjective (K : ChainComplex (ModuleCat.{0,0} ℤ) ℕ) (m : ℕ)
    (Q : Type) [AddCommGroup Q] [Module ℤ Q]
    (hfree : ∀ i : ℕ, i ≤ m → Module.Free ℤ ↥(K.X i)) :
    Function.Injective (LinearMap.lTensor Q (Work.Cohomology.uctZ K m).subtype) := by
  haveI hFm : Module.Free ℤ ↥(K.X m) := hfree m le_rfl
  haveI hFm1 : Module.Free ℤ ↥(K.X (m - 1)) := hfree (m - 1) (by omega)
  haveI hFlatR : Module.Flat ℤ ↥(Work.Cohomology.uctR K m) := hrbcFlatSubmoduleOfFree _
  haveI hFlatZ : Module.Flat ℤ ↥(Work.Cohomology.uctZ K m) := hrbcFlatSubmoduleOfFree _
  have hFlatQ : Module.Flat ℤ (↥(K.X m) ⧸ Work.Cohomology.uctZ K m) :=
    Module.Flat.of_linearEquiv (LinearMap.quotKerEquivRange (K.d m (m - 1)).hom)
  refine hrbcLTensorSubtypeInjectiveOfFlat _ (Submodule.subtype_injective _) hFlatZ
    (Module.Flat.of_free) ?_ Q
  rw [Submodule.range_subtype]; exact hFlatQ

/-! ## Part C: transports to the extension-of-scalars functor -/

theorem hrbcExtendScalarsMapSurjective {A B : ModuleCat.{0,0} ℤ} (b : A ⟶ B)
    (hb : Function.Surjective b.hom) :
    Function.Surjective (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map b).hom) :=
  LinearMap.lTensor_surjective (hrbcQc 𝕜) hb

theorem hrbcExtendScalarsMapExact {A B C : ModuleCat.{0,0} ℤ} (a : A ⟶ B) (b : B ⟶ C)
    (hex : Function.Exact a.hom b.hom) (hb : Function.Surjective b.hom) :
    Function.Exact (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map a).hom)
      (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map b).hom) :=
  lTensor_exact (hrbcQc 𝕜) hex hb

theorem hrbcExtendScalarsKerEqRange {A B C : ModuleCat.{0,0} ℤ} (a : A ⟶ B) (b : B ⟶ C)
    (hex : Function.Exact a.hom b.hom) (hb : Function.Surjective b.hom) :
    LinearMap.ker (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map b).hom)
      = LinearMap.range (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map a).hom) :=
  LinearMap.exact_iff.mp (hrbcExtendScalarsMapExact a b hex hb)

theorem hrbcUctBInj (K : ChainComplex (ModuleCat.{0,0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, i ≤ m + 1 → Module.Free ℤ ↥(K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Function.Injective (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map
      (ModuleCat.ofHom (Work.Cohomology.uctB K m).subtype)).hom) :=
  hrbcLTensorUctBInjective K m (hrbcQc 𝕜) hfree hTF

theorem hrbcUctZInj (K : ChainComplex (ModuleCat.{0,0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, i ≤ m → Module.Free ℤ ↥(K.X i)) :
    Function.Injective (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map
      (ModuleCat.ofHom (Work.Cohomology.uctZ K m).subtype)).hom) :=
  hrbcLTensorUctZInjective K m (hrbcQc 𝕜) hfree

/-! ## Part D: utility isomorphisms -/

noncomputable def hrbcQuotEquivOfLinearEquiv {M M' : Type} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup M'] [Module 𝕜 M'] (e : M ≃ₗ[𝕜] M') (p : Submodule 𝕜 M) :
    (M ⧸ p) ≃ₗ[𝕜] (M' ⧸ p.map (e : M →ₗ[𝕜] M')) := by
  have hle : p ≤ Submodule.comap (e : M →ₗ[𝕜] M') (p.map (e : M →ₗ[𝕜] M')) :=
    fun x hx => Submodule.mem_map_of_mem hx
  have hcomap : Submodule.comap (e : M →ₗ[𝕜] M') (p.map (e : M →ₗ[𝕜] M')) = p :=
    Submodule.comap_map_eq_of_injective e.injective p
  refine LinearEquiv.ofBijective
    (Submodule.mapQ p (p.map (e : M →ₗ[𝕜] M')) (e : M →ₗ[𝕜] M') hle) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  · intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨m, rfl⟩ := e.surjective x
    exact ⟨Submodule.mkQ _ m, Submodule.mapQ_apply _ _ _ _⟩

noncomputable def hrbcQuotRangeIso {M M' P : Type} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup M']
    [Module 𝕜 M'] [AddCommGroup P] [Module 𝕜 P] (φ : M →ₗ[𝕜] M')
    (hφ : Function.Injective φ) (ψ : P →ₗ[𝕜] M) :
    (↥(LinearMap.range φ) ⧸
        (LinearMap.range ψ).map (φ.codRestrict (LinearMap.range φ) (fun x => ⟨x, rfl⟩)))
      ≃ₗ[𝕜] (M ⧸ LinearMap.range ψ) := by
  set Φ : M →ₗ[𝕜] ↥(LinearMap.range φ) :=
    φ.codRestrict (LinearMap.range φ) (fun x => ⟨x, rfl⟩) with hΦ
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hΦinj : Function.Injective Φ := fun x y h => hφ (Subtype.ext_iff.mp h)
  set q : Submodule 𝕜 ↥(LinearMap.range φ) := (LinearMap.range ψ).map Φ with hq
  have hle : LinearMap.range ψ ≤ Submodule.comap Φ q := by
    rintro x ⟨p, hp⟩
    rw [← hp]
    exact Submodule.mem_map_of_mem ⟨p, rfl⟩
  have hcomap : Submodule.comap Φ q = LinearMap.range ψ := by
    refine le_antisymm ?_ hle
    rintro x ⟨y, hy, hxy⟩
    rw [← hΦinj hxy]
    exact hy
  refine (LinearEquiv.ofBijective
    (Submodule.mapQ (LinearMap.range ψ) q Φ hle) ⟨?_, ?_⟩).symm
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  · intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective q y
    obtain ⟨x, rfl⟩ := hΦsurj z
    exact ⟨Submodule.mkQ _ x, Submodule.mapQ_apply _ _ _ _⟩

noncomputable def hrbcExtendScalarsQuotRangeIso {A B C : ModuleCat.{0,0} ℤ} (a : A ⟶ B) (b : B ⟶ C)
    (hex : Function.Exact a.hom b.hom) (hb : Function.Surjective b.hom) :
    (↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj B) ⧸
        LinearMap.range (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map a).hom))
      ≃ₗ[𝕜] ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj C) :=
  (hrbcQuotCongr (hrbcExtendScalarsKerEqRange a b hex hb).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (hrbcExtendScalarsMapSurjective b hb))


/-! ## Part E: the chain-level change of coefficients -/

theorem hrbcChainLevel (K : ChainComplex (ModuleCat.{0,0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, i ≤ m + 2 → Module.Free ℤ ↥(K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Nonempty ((((ModuleCat.extendScalars (Int.castRingHom 𝕜)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).homology (m + 1) ≅
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (K.homology (m + 1))) := by
  let F := ModuleCat.extendScalars (Int.castRingHom 𝕜)
  let D : ChainComplex (ModuleCat 𝕜) ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  -- the boundary-to-cycle inclusion
  let j : ↥(Work.Cohomology.uctB K (m+1)) →ₗ[ℤ] ↥(Work.Cohomology.uctZ K (m+1)) :=
    (Work.Cohomology.uctB K (m+1)).subtype.codRestrict (Work.Cohomology.uctZ K (m+1))
      (fun x => Work.Cohomology.uctB_le_uctZ K (m+1) x.2)
  let ObjZ : ModuleCat ℤ := ModuleCat.of ℤ ↥(Work.Cohomology.uctZ K (m+1))
  let ObjB : ModuleCat ℤ := ModuleCat.of ℤ ↥(Work.Cohomology.uctB K (m+1))
  let φ : (F.obj ObjZ : Type) →ₗ[𝕜] (D.X (m+1) : Type) :=
    (F.map (ModuleCat.ofHom (Work.Cohomology.uctZ K (m+1)).subtype)).hom
  let ψ' : (F.obj ObjB : Type) →ₗ[𝕜] (F.obj ObjZ : Type) :=
    (F.map (ModuleCat.ofHom j)).hom
  have hφinj : Function.Injective φ :=
    hrbcUctZInj K (m+1) (fun i hi => hfree i (by omega))
  have hψ'eq : ((F.map (ModuleCat.ofHom (Work.Cohomology.uctB K (m+1)).subtype)).hom)
      = φ ∘ₗ ψ' := by
    have hsubj : (Work.Cohomology.uctB K (m+1)).subtype
        = (Work.Cohomology.uctZ K (m+1)).subtype ∘ₗ j := by
      ext x
      rfl
    have hmor : ModuleCat.ofHom (Work.Cohomology.uctB K (m+1)).subtype
        = ModuleCat.ofHom j ≫ ModuleCat.ofHom (Work.Cohomology.uctZ K (m+1)).subtype := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    have := congrArg (fun (u : ObjB ⟶ K.X (m+1)) => (F.map u).hom) hmor
    rw [F.map_comp, ModuleCat.hom_comp] at this
    exact this
  -- ## identification of the cycles
  have hkerZ : LinearMap.ker (D.d (m+1) m).hom = LinearMap.range φ := by
    let gK2 : ↥(K.X (m+1)) →ₗ[ℤ] ↥(Work.Cohomology.uctB K m) :=
      ((K.d (m+1) m).hom).codRestrict (Work.Cohomology.uctB K m) (fun x => ⟨x, rfl⟩)
    have hsurj_gK2 : Function.Surjective gK2 := fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩
    have hmor : K.d (m+1) m
        = ModuleCat.ofHom gK2 ≫ ModuleCat.ofHom (Work.Cohomology.uctB K m).subtype := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    have hcomp : (D.d (m+1) m).hom
        = ((F.map (ModuleCat.ofHom (Work.Cohomology.uctB K m).subtype)).hom) ∘ₗ
          ((F.map (ModuleCat.ofHom gK2)).hom) := by
      show (F.map (K.d (m+1) m)).hom = _
      rw [hmor, F.map_comp, ModuleCat.hom_comp]
    rw [hcomp, LinearMap.ker_comp]
    rw [LinearMap.ker_eq_bot.mpr (hrbcUctBInj K m (fun i hi => hfree i (by omega)) hTF),
      Submodule.comap_bot]
    have hexZ : Function.Exact (ModuleCat.ofHom (Work.Cohomology.uctZ K (m+1)).subtype).hom
        (ModuleCat.ofHom gK2).hom := by
      show Function.Exact (Work.Cohomology.uctZ K (m+1)).subtype gK2
      rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_codRestrict]
      show Work.Cohomology.uctZ K (m+1) = LinearMap.ker (K.d (m+1) m).hom
      rw [show Work.Cohomology.uctZ K (m+1) = LinearMap.ker (K.d (m+1) (m+1-1)).hom from rfl,
        show m + 1 - 1 = m from Nat.add_sub_cancel m 1]
    exact LinearMap.exact_iff.mp (hrbcExtendScalarsMapExact
      (ModuleCat.ofHom (Work.Cohomology.uctZ K (m+1)).subtype) (ModuleCat.ofHom gK2) hexZ hsurj_gK2)
  -- ## identification of the boundaries
  have hrangeB : LinearMap.range (D.d (m+2) (m+1)).hom = LinearMap.range
      ((F.map (ModuleCat.ofHom (Work.Cohomology.uctB K (m+1)).subtype)).hom) := by
    let gK : ↥(K.X (m+2)) →ₗ[ℤ] ↥(Work.Cohomology.uctB K (m+1)) :=
      ((K.d (m+2) (m+1)).hom).codRestrict (Work.Cohomology.uctB K (m+1)) (fun x => ⟨x, rfl⟩)
    have hsurj_gK : Function.Surjective gK := fun y => by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x, Subtype.ext hx⟩
    have hmor : K.d (m+2) (m+1)
        = ModuleCat.ofHom gK ≫ ModuleCat.ofHom (Work.Cohomology.uctB K (m+1)).subtype := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    have hcomp : (D.d (m+2) (m+1)).hom
        = ((F.map (ModuleCat.ofHom (Work.Cohomology.uctB K (m+1)).subtype)).hom) ∘ₗ
          ((F.map (ModuleCat.ofHom gK)).hom) := by
      show (F.map (K.d (m+2) (m+1))).hom = _
      rw [hmor, F.map_comp, ModuleCat.hom_comp]
    rw [hcomp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (hrbcExtendScalarsMapSurjective (ModuleCat.ofHom gK) hsurj_gK),
      Submodule.map_top]
  -- ## the short complex and its homology
  let S : ShortComplex (ModuleCat 𝕜) := D.sc' (m+2) (m+1) m
  have hSf : S.f = D.d (m+2) (m+1) := rfl
  have hSg : S.g = D.d (m+1) m := rfl
  have hkerS : LinearMap.ker S.g.hom = LinearMap.range φ := by
    rw [hSg]; exact hkerZ
  have hrangeS : LinearMap.range S.f.hom = (LinearMap.range ψ').map φ := by
    rw [hSf, hrangeB, hψ'eq, LinearMap.range_comp]
  let ZB : Submodule 𝕜 ↥(LinearMap.ker S.g.hom) := S.moduleCatToCycles.range
  have e1 : D.homology (m+1) ≅ S.homology :=
    D.homologyIsoSc' (m+2) (m+1) m (Work.Cohomology.down_prev (m+1))
      (Work.Cohomology.down_next (m+1))
  have e2 : S.homology ≅ ModuleCat.of 𝕜 (↥(LinearMap.ker S.g.hom) ⧸ ZB) :=
    ShortComplex.moduleCatHomologyIso S
  -- ## the identification of ZB with the image of `range ψ'`
  have hZB1 : ZB = Submodule.comap (LinearMap.ker S.g.hom).subtype (LinearMap.range S.f.hom) :=
    LinearMap.range_codRestrict _ _ _
  have hZB3 : Submodule.map (LinearEquiv.ofEq _ _ hkerS).toLinearMap ZB
      = (LinearMap.range ψ').map (φ.codRestrict (LinearMap.range φ) (fun x => ⟨x, rfl⟩)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hZB1] at hy
      have hy' : (LinearMap.ker S.g.hom).subtype y ∈ LinearMap.range S.f.hom := hy
      rw [hrangeS] at hy'
      obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp hy'
      refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
      refine Subtype.ext ?_
      exact hpx.trans (LinearEquiv.coe_ofEq_apply hkerS y).symm
    · rintro ⟨p, hp, hpx⟩
      have hy : (⟨φ p, (by rw [hkerS]; exact ⟨p, rfl⟩)⟩ : ↥(LinearMap.ker S.g.hom)) ∈ ZB := by
        rw [hZB1, Submodule.mem_comap, hrangeS]
        exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩
      refine Submodule.mem_map.mpr
        ⟨⟨φ p, (by rw [hkerS]; exact ⟨p, rfl⟩)⟩, hy, ?_⟩
      refine Subtype.ext ?_
      exact (LinearEquiv.coe_ofEq_apply hkerS
        ⟨φ p, (by rw [hkerS]; exact ⟨p, rfl⟩)⟩).trans (congrArg Subtype.val hpx)
  have e3 : (↥(LinearMap.ker S.g.hom) ⧸ ZB) ≃ₗ[𝕜]
      ((F.obj ObjZ : Type) ⧸ LinearMap.range ψ') :=
    (hrbcQuotEquivOfLinearEquiv (LinearEquiv.ofEq _ _ hkerS) ZB).trans
      ((hrbcQuotCongr hZB3).trans (hrbcQuotRangeIso φ hφinj ψ'))
  -- ## right exactness of the coefficient change
  have hjrange : j.range = Work.Cohomology.uctH K (m+1) := by
    show ((Work.Cohomology.uctB K (m+1)).subtype.codRestrict (Work.Cohomology.uctZ K (m+1)) _).range
      = Work.Cohomology.uctH K (m+1)
    rw [LinearMap.range_codRestrict, Submodule.range_subtype, Work.Cohomology.uctH_eq_comap]
  have hψ'' : LinearMap.range ψ'
      = LinearMap.range ((F.map (ModuleCat.ofHom (j.range).subtype)).hom) := by
    have hmor : ModuleCat.ofHom j
        = ModuleCat.ofHom j.rangeRestrict ≫ ModuleCat.ofHom (j.range).subtype := by
      apply ModuleCat.hom_ext
      ext x
      rfl
    have hsurj : Function.Surjective
        ((F.map (ModuleCat.ofHom j.rangeRestrict)).hom) :=
      hrbcExtendScalarsMapSurjective (ModuleCat.ofHom (LinearMap.rangeRestrict j))
        (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict j))
    have hcomp : ψ' = ((F.map (ModuleCat.ofHom (j.range).subtype)).hom) ∘ₗ
        ((F.map (ModuleCat.ofHom j.rangeRestrict)).hom) := by
      show (F.map (ModuleCat.ofHom j)).hom = _
      rw [hmor, F.map_comp, ModuleCat.hom_comp]
    rw [hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have e4 : ((F.obj ObjZ : Type) ⧸ LinearMap.range ψ') ≃ₗ[𝕜]
      ↥(F.obj (ModuleCat.of ℤ (↥(Work.Cohomology.uctZ K (m+1)) ⧸ j.range))) :=
    (hrbcQuotCongr hψ'').trans
      (hrbcExtendScalarsQuotRangeIso (ModuleCat.ofHom (j.range).subtype)
        (ModuleCat.ofHom (j.range).mkQ)
        (LinearMap.exact_subtype_mkQ j.range) (Submodule.mkQ_surjective j.range))
  -- ## comparison with the homology of `K`
  have e5 : ↥(F.obj (ModuleCat.of ℤ (↥(Work.Cohomology.uctZ K (m+1)) ⧸ j.range)))
      ≃ₗ[𝕜] ↥(F.obj (K.homology (m+1))) :=
    (Iso.toLinearEquiv (F.mapIso ((hrbcQuotCongr hjrange).toModuleIso ≪≫
      (Work.Cohomology.homology_iso_H K (m+1)).some.symm)))
  refine ⟨e1 ≪≫ e2 ≪≫ LinearEquiv.toModuleIso (e3.trans (e4.trans e5))⟩


/-! ## Part F: the requested theorem -/

/-- **Change of coefficients `ℤ → 𝕜` for singular homology, one degree above a torsion-free
group.** -/
theorem HRbaseChangeTF (𝕜 : Type) [CommRing 𝕜] {X : Type} [TopologicalSpace X] (m : ℕ)
    (hH : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ X m)) :
    Nonempty (Work.Pi6.HR 𝕜 X (m + 1) ≅
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ X (m + 1))) := by
  let F := ModuleCat.extendScalars (Int.castRingHom 𝕜)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  obtain ⟨e⟩ := hrbcChainLevel (𝕜 := 𝕜) K m
    (fun i _ => Work.Cohomology.singularChains_free Y i) hH
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      Work.Cohomology.singularChains 𝕜 Y :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        (Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜)
  exact ⟨(HomologicalComplex.homologyMapIso hΦ (m+1)).symm ≪≫ e⟩

end

end Work.Pi6.EMM2
