import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMODD.tensorDefs
import Submission.Work.Pi6.EMODD.tmulCycleNeZero
import Submission.Work.Cohomology.singularChains_free
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace Work.Pi6.EMODD

noncomputable section

/-- The unit `x ↦ 1 ⊗ x` of the extension/restriction adjunction, on elements. -/
abbrev unitZ (𝕜 : Type) [CommRing 𝕜] (M : ModuleCat.{0} ℤ) :
    ↥M → ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj M) :=
  fun x => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app M x

/-- The singular chain complex of `X` with coefficients in `ℤ`. -/
abbrev chZ (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SSet.chainComplex (TopCat.toSSet.obj (TopCat.of X)) Work.Pi6.SRANGE.ZModZ

/-- The singular chain complex of `X` with coefficients in `𝕜`. -/
abbrev chK (𝕜 : Type) [CommRing 𝕜] (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  SSet.chainComplex (TopCat.toSSet.obj (TopCat.of X)) (Work.Pi6.SRANGE.RMod 𝕜)

/-- The differential of a cycle is zero. -/
lemma iCycles_d_apply (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (ζ : C.cycles 2) : (C.d 2 1).hom ((C.iCycles 2).hom ζ) = 0 := by
  have h := congrArg (fun (g : C.cycles 2 ⟶ C.X 1) => (ConcreteCategory.hom g) ζ)
    (HomologicalComplex.iCycles_d C 2 1)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The composite `X₃ → cycles₂ → X₂` is the differential. -/
lemma iCycles_toCycles_apply (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (y : ↥(C.X 3)) : (C.iCycles 2).hom ((C.toCycles 3 2).hom y) = (C.d 3 2).hom y := by
  have h := congrArg (fun (g : C.X 3 ⟶ C.X 2) => (ConcreteCategory.hom g) y)
    (HomologicalComplex.toCycles_i C 3 2)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The unit `1 ⊗ -` is additive. -/
lemma unitZ_add (𝕜 : Type) [CommRing 𝕜] (M : ModuleCat.{0} ℤ) (x y : ↥M) :
    unitZ 𝕜 M (x + y) = unitZ 𝕜 M x + unitZ 𝕜 M y :=
  map_add ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app M).hom x y

/-- The differential of the base change of the unit `1 ⊗ -`. -/
lemma baseChange_d_unitZ (𝕜 : Type) [CommRing 𝕜] (C : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n m : ℕ) (x : ↥(C.X n)) :
    ((Work.Pi6.SRANGE.baseChange 𝕜 C).d n m).hom (unitZ 𝕜 (C.X n) x)
      = unitZ 𝕜 (C.X m) ((C.d n m).hom x) := by
  rw [show (Work.Pi6.SRANGE.baseChange 𝕜 C).d n m
      = (ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.d n m) from rfl]
  exact extendScalars_map_unit 𝕜 (C.d n m) x

/-- Naturality of the unit `1 ⊗ -` on elements. -/
lemma map_unitZ (𝕜 : Type) [CommRing 𝕜] {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (x : ↥M) :
    ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map f).hom (unitZ 𝕜 M x)
      = unitZ 𝕜 N (f.hom x) :=
  extendScalars_map_unit 𝕜 f x

/-- The `homologyπ` of a cycle coming from `toCycles` vanishes. -/
lemma homologyπ_toCycles (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (y : ↥(C.X 3)) : (C.homologyπ 2).hom ((C.toCycles 3 2).hom y) = 0 := by
  have h := congrArg (fun (g : C.X 3 ⟶ C.homology 2) => (ConcreteCategory.hom g) y)
    (HomologicalComplex.toCycles_comp_homologyπ (K := C) 3 2)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- **A `×2` map on `π₂` of `K(ℤ,2)`-models is non-zero on `H₂` over any field of characteristic `≠ 2`.** Let `ι : F → T` be a map of range models of `K(ℤ,2)` through `9` whose induced map on `H₂(−;ℤ)` sends a generator `zF` of `H₂(F;ℤ) ≅ ℤ` to twice a generator `zT` of `H₂(T;ℤ) ≅ ℤ`. Then the induced map on `H₂(−;𝕜)` is non-zero for every field `𝕜` with `(2 : 𝕜) ≠ 0`.

(Route: base change `ℤ → 𝕜` on the singular chain complexes, natural in the space (`Work.Pi6.SRANGE.BaseChange`), turns `zF` into a non-zero class `zF ⊗ 1` (the integral homology in degree `2` of a `K(ℤ,2)`-range model is free, so `− ⊗ 𝕜` is injective there) whose image is `2 · (zT ⊗ 1) ≠ 0` because `2 ≠ 0` in `𝕜`.) -/
theorem hmapTwoNeZero (𝕜 : Type) [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0) {F T : Type} [TopologicalSpace F]
    [TopologicalSpace T] (ι : C(F, T)) (f₀ : F)
    (hF : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 9 F f₀)
    (hT : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 9 T (ι f₀))
    (hgen : ∃ (zF : Work.Pi6.HR ℤ F 2) (zT : Work.Pi6.HR ℤ T 2),
      (∀ z : Work.Pi6.HR ℤ F 2, ∃! n : ℤ, z = n • zF) ∧
      (∀ z : Work.Pi6.HR ℤ T 2, ∃! n : ℤ, z = n • zT) ∧
      (Work.Pi6.hmap ℤ ι 2).hom zF = (2 : ℤ) • zT) :
    (Work.Pi6.hmap 𝕜 ι 2).hom ≠ 0 := by
  obtain ⟨zF, zT, hzF, hzT, hσ⟩ := hgen
  -- ### 0. Notation
  let sig := TopCat.toSSet.map (TopCat.ofHom ι)
  let σ' : chZ F ⟶ chZ T := SSet.chainComplexMap sig Work.Pi6.SRANGE.ZModZ
  let σ𝕜 : chK 𝕜 F ⟶ chK 𝕜 T := SSet.chainComplexMap sig (Work.Pi6.SRANGE.RMod 𝕜)
  have hσT : (HomologicalComplex.homologyMap σ' 2).hom zF = zT + zT := by
    have h1 : (HomologicalComplex.homologyMap σ' 2).hom zF = (2 : ℤ) • zT := hσ
    rw [h1, two_zsmul]
  -- ### 1. Cycle representatives of the two integral generators
  obtain ⟨ζF, hζF⟩ := (ModuleCat.epi_iff_surjective ((chZ F).homologyπ 2)).mp
    (inferInstance : Epi ((chZ F).homologyπ 2)) zF
  obtain ⟨ζT, hζT⟩ := (ModuleCat.epi_iff_surjective ((chZ T).homologyπ 2)).mp
    (inferInstance : Epi ((chZ T).homologyπ 2)) zT
  -- ### 2. Flatness of the cokernel of the cycle inclusion, for `T`
  haveI hfreeT : Module.Free ℤ ↥((chZ T).X 1) :=
    Work.Cohomology.singularChains_free (TopCat.of T) 1
  have hflatT : Module.Flat ℤ ↥(LinearMap.range ((chZ T).d 2 1).hom) := by
    haveI htf : Module.IsTorsionFree ℤ ↥((chZ T).X 1) := inferInstance
    have key := @Submodule.instIsTorsionFree ℤ ↥((chZ T).X 1) _ _ _
      (LinearMap.range ((chZ T).d 2 1).hom) htf
    haveI : Module.IsTorsionFree ℤ ↥(LinearMap.range ((chZ T).d 2 1).hom) := by
      convert key using 1
      exact Subsingleton.elim _ _
    infer_instance
  -- ### 3. The generating cycle condition, in the form needed by the crux
  have hgenT : ∀ y : (chZ T).homology 2,
      ∃! n : ℤ, y = n • ((chZ T).homologyπ 2).hom ζT := by
    intro y
    obtain ⟨n, hn, huniq⟩ := hzT y
    exact ⟨n, by rw [hn, hζT], fun m hm => huniq m (by rw [hm, hζT])⟩
  -- ### 4. The cycles `1 ⊗ ζ` in the base changed complexes
  obtain ⟨zT', hzT'⟩ := exists_iCycles_eq 𝕜 (Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)) 2 (by norm_num)
    (unitZ 𝕜 ((chZ T).X 2) (((chZ T).iCycles 2).hom ζT))
    (by rw [baseChange_d_unitZ, iCycles_d_apply]; exact map_zero _)
  obtain ⟨zF', hzF'⟩ := exists_iCycles_eq 𝕜 (Work.Pi6.SRANGE.baseChange 𝕜 (chZ F)) 2 (by norm_num)
    (unitZ 𝕜 ((chZ F).X 2) (((chZ F).iCycles 2).hom ζF))
    (by rw [baseChange_d_unitZ, iCycles_d_apply]; exact map_zero _)
  -- ### 5. The crux: the base change of the generator of `H₂(T;ℤ)` is non-zero
  have hneT : ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom zT' ≠ 0 :=
    tmulCycleNeZero 𝕜 (chZ T) ζT hgenT hflatT zT' hzT'
  -- ### 6. The integral relation `σ_* ζF = 2 ζT` and its boundary `u`
  have hclass : ((chZ T).homologyπ 2).hom
      (HomologicalComplex.cyclesMap σ' 2 ζF - (ζT + ζT)) = 0 := by
    rw [map_sub, map_add, ← homologyMap_homologyπ_gen ℤ σ' 2 ζF, hζF, hσT, hζT, sub_self]
  obtain ⟨u, hu⟩ := chain_homologypi_eq_zero_gen ℤ (chZ T) 2
    (HomologicalComplex.cyclesMap σ' 2 ζF - (ζT + ζT)) hclass
  have hu' : ((chZ T).d 3 2).hom u
      = ((chZ T).iCycles 2).hom (HomologicalComplex.cyclesMap σ' 2 ζF)
        - (((chZ T).iCycles 2).hom ζT + ((chZ T).iCycles 2).hom ζT) := by
    rw [hu, map_sub, map_add]
  have hu'' : ((chZ T).iCycles 2).hom (HomologicalComplex.cyclesMap σ' 2 ζF)
      = (((chZ T).iCycles 2).hom ζT + ((chZ T).iCycles 2).hom ζT)
        + ((chZ T).d 3 2).hom u := by
    rw [hu']; abel
  -- ### 7. The same relation after base change
  have hchain : ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom
        (HomologicalComplex.cyclesMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF')
      = ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom zT'
        + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom zT'
        + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).d 3 2).hom (unitZ 𝕜 ((chZ T).X 3) u) := by
    calc ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom
          (HomologicalComplex.cyclesMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF')
        = ((Work.Pi6.SRANGE.baseChangeMap 𝕜 σ').f 2).hom
            (((Work.Pi6.SRANGE.baseChange 𝕜 (chZ F)).iCycles 2).hom zF') :=
          iCycles_cyclesMap_gen 𝕜 _ 2 zF'
      _ = ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (σ'.f 2)).hom
            (unitZ 𝕜 ((chZ F).X 2) (((chZ F).iCycles 2).hom ζF)) := by
          rw [show (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ').f 2
              = (ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (σ'.f 2) from rfl]
          exact congrArg (fun t =>
            ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (σ'.f 2)).hom t) hzF'
      _ = unitZ 𝕜 ((chZ T).X 2) ((σ'.f 2).hom (((chZ F).iCycles 2).hom ζF)) :=
          map_unitZ 𝕜 (σ'.f 2) (((chZ F).iCycles 2).hom ζF)
      _ = unitZ 𝕜 ((chZ T).X 2)
            (((chZ T).iCycles 2).hom (HomologicalComplex.cyclesMap σ' 2 ζF)) :=
          congrArg (fun t => unitZ 𝕜 ((chZ T).X 2) t)
            (iCycles_cyclesMap_gen ℤ σ' 2 ζF).symm
      _ = unitZ 𝕜 ((chZ T).X 2)
            ((((chZ T).iCycles 2).hom ζT + ((chZ T).iCycles 2).hom ζT)
              + ((chZ T).d 3 2).hom u) :=
          congrArg (fun t => unitZ 𝕜 ((chZ T).X 2) t) hu''
      _ = (unitZ 𝕜 ((chZ T).X 2) (((chZ T).iCycles 2).hom ζT)
            + unitZ 𝕜 ((chZ T).X 2) (((chZ T).iCycles 2).hom ζT))
            + unitZ 𝕜 ((chZ T).X 2) (((chZ T).d 3 2).hom u) := by
          rw [unitZ_add, unitZ_add]
      _ = ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom zT'
            + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2).hom zT'
            + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).d 3 2).hom
                (unitZ 𝕜 ((chZ T).X 3) u) := by
          rw [← hzT', ← baseChange_d_unitZ 𝕜 (chZ T) 3 2 u]
  have hcycles : HomologicalComplex.cyclesMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF'
      - (zT' + zT') = (Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).toCycles 3 2
          (unitZ 𝕜 ((chZ T).X 3) u) := by
    refine (ModuleCat.mono_iff_injective _).mp
      (inferInstance : Mono ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).iCycles 2)) ?_
    rw [map_sub, map_add, hchain, iCycles_toCycles_apply]
    abel
  have hhom : ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom
        (HomologicalComplex.cyclesMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF')
      = ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom zT'
        + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom zT' := by
    have h := congrArg (fun w => ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom w)
      hcycles
    rw [map_sub, map_add, homologyπ_toCycles] at h
    exact sub_eq_zero.mp h
  -- ### 8. `2 ⊗ [ζT] ≠ 0`
  have hneTpair : ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom zT'
      + ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom zT' ≠ 0 := by
    intro h0
    refine smul_ne_zero h2 hneT ?_
    rw [two_smul 𝕜]; exact h0
  -- ### 9. Naturality of the comparison `C_*(X;ℤ) ⊗ 𝕜 ≅ C_*(X;𝕜)`
  obtain ⟨e, he⟩ := baseChangeNat 𝕜
  have hnat : (e (TopCat.toSSet.obj (TopCat.of F))).hom ≫ σ𝕜
      = Work.Pi6.SRANGE.baseChangeMap 𝕜 σ' ≫ (e (TopCat.toSSet.obj (TopCat.of T))).hom :=
    he _ _ sig
  have hnat2 : HomologicalComplex.homologyMap (e (TopCat.toSSet.obj (TopCat.of F))).hom 2
        ≫ HomologicalComplex.homologyMap σ𝕜 2
      = HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2
        ≫ HomologicalComplex.homologyMap (e (TopCat.toSSet.obj (TopCat.of T))).hom 2 := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hnat]
  -- ### 10. Assembly
  refine fun hzero => ?_
  have hnat2' := congrArg ModuleCat.Hom.hom hnat2
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnat2'
  have hnat3 := DFunLike.congr_fun hnat2'
    (((Work.Pi6.SRANGE.baseChange 𝕜 (chZ F)).homologyπ 2).hom zF')
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hnat3
  have hbase : (HomologicalComplex.homologyMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2).hom
      (((Work.Pi6.SRANGE.baseChange 𝕜 (chZ F)).homologyπ 2).hom zF')
      = ((Work.Pi6.SRANGE.baseChange 𝕜 (chZ T)).homologyπ 2).hom
          (HomologicalComplex.cyclesMap (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF') :=
    homologyMap_homologyπ_gen 𝕜 (Work.Pi6.SRANGE.baseChangeMap 𝕜 σ') 2 zF'
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (e (TopCat.toSSet.obj (TopCat.of T))).hom 2).hom := by
    intro a b hab
    have h1 : ((HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).hom).hom a
        = ((HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).hom).hom b := hab
    have h2 := congrArg (fun x =>
      ((HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).inv).hom x) h1
    have h3 : ((HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).hom
          ≫ (HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).inv).hom a
        = ((HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).hom
          ≫ (HomologicalComplex.homologyMapIso (e (TopCat.toSSet.obj (TopCat.of T))) 2).inv).hom b := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
    rw [Iso.hom_inv_id] at h3
    simpa using h3
  have hv : (HomologicalComplex.homologyMap σ𝕜 2).hom
      ((HomologicalComplex.homologyMap (e (TopCat.toSSet.obj (TopCat.of F))).hom 2).hom
        (((Work.Pi6.SRANGE.baseChange 𝕜 (chZ F)).homologyπ 2).hom zF')) ≠ 0 := by
    rw [hnat3, hbase, hhom]
    intro habs
    exact hneTpair (hinj (by rw [habs, map_zero]))
  have hz2 : (HomologicalComplex.homologyMap σ𝕜 2).hom = 0 := hzero
  exact hv (by rw [hz2]; rfl)


end

end Work.Pi6.EMODD
