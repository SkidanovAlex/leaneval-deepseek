import Mathlib
import Submission.Work.Pi6.EMODD.tensorDefs
import Submission.Work.RatHurewicz.Bridge.HomologyAux
import Submission.Work.RatHurewicz.Bridge.chainBoundary
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The base changed class of a generating cycle is non-zero

Let `C` be a chain complex of `ℤ`-modules and `ζ` a `2`-cycle of `C` whose homology class `[ζ]`
generates `H₂(C) ≅ ℤ` freely.  Then in the base changed complex `C ⊗[ℤ] 𝕜` the class of the cycle
`1 ⊗ ζ` is non-zero (`Work.Pi6.EMODD.tmulCycleNeZero`).

The proof is the elementary universal coefficient argument: writing `Z₂ = ker ∂₂` and
`B₂ = im ∂₃`, the quotient `Z₂ ⧸ B₂ ≅ ℤ` is free, so `(iCycles) ⊗ 𝕜 : Z₂ ⊗ 𝕜 → C₂ ⊗ 𝕜` is
injective (`Work.Pi6.EMODD.injective_extendScalars_map`, the flatness of the cokernel of the
inclusion of the cycles being exactly what is needed).  A boundary equation for `1 ⊗ ζ` therefore exhibits
`1 ⊗ [ζ]` as an element of `im (∂₃ ⊗ 𝕜)`; applying `H₂(C) ⊗ 𝕜 →` (the tensor of
`Z₂ ↠ H₂(C)`) then gives `1 ⊗ [ζ] = 0`, absurd because `[ζ]` freely generates a copy of `ℤ`
(`Work.Pi6.EMODD.unit_app_ne_zero_of_gen`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace Work.Pi6.EMODD

noncomputable section

/-! ## Elementary facts about the unit of `extendScalars ⊣ restrictScalars` -/

/-- The unit of the extension/restriction adjunction at the coefficient ring is non-zero. -/
lemma unit_app_one_ne_zero (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜] :
    (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of ℤ ℤ)) from
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app
          (ModuleCat.of ℤ ℤ) (1 : ℤ)) ≠ 0 := by
  letI : Module ℤ 𝕜 := Module.compHom 𝕜 (Int.castRingHom 𝕜)
  intro h
  have h2 : (TensorProduct.rid ℤ 𝕜)
      (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of ℤ ℤ)) from
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app
          (ModuleCat.of ℤ ℤ) (1 : ℤ)) = 0 :=
    (LinearEquiv.map_eq_zero_iff (TensorProduct.rid ℤ 𝕜)).mpr h
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at h2
  rw [TensorProduct.rid_tmul] at h2
  have h4 : (1 : 𝕜) = 0 := by simpa using h2
  exact one_ne_zero h4

/-- **Naturality of the unit `x ↦ 1 ⊗ x` on elements.** -/
lemma extendScalars_map_unit (𝕜 : Type) [CommRing 𝕜] {M N : ModuleCat.{0} ℤ} (f : M ⟶ N)
    (x : ↥M) :
    ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map f).hom
        (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj M) from
          (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app M x)
      = (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj N) from
          (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app N (f.hom x)) := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply, ModuleCat.ExtendScalars.map_tmul]

/-- **Extension of scalars is injective on a map with flat cokernel.**  If `0 → M --g--> N --f--> P → 0`
is exact with `f` surjective, `g` injective and `P` flat over `ℤ`, then `g ⊗[ℤ] 𝕜` is injective. -/
lemma injective_extendScalars_map (𝕜 : Type) [CommRing 𝕜] {M N : ModuleCat.{0} ℤ}
    {P : Type} [AddCommGroup P] [Module ℤ P]
    (f : N ⟶ ModuleCat.of ℤ P) (hf : Function.Surjective f.hom)
    (g : M ⟶ N) (hg : Function.Injective g.hom) (H : Function.Exact g.hom f.hom)
    [Module.Flat ℤ P] :
    Function.Injective ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map g).hom := by
  letI : Module ℤ 𝕜 := Module.compHom 𝕜 (Int.castRingHom 𝕜)
  have hl : Function.Injective (g.hom.lTensor 𝕜) :=
    LinearMap.lTensor_injective_of_exact_of_flat f.hom hf g.hom hg H 𝕜
  have hfun : ∀ w : ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj M),
      ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map g).hom w = g.hom.lTensor 𝕜 w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a m => rw [ModuleCat.ExtendScalars.map_tmul, LinearMap.lTensor_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro x y hxy
  exact hl (by rw [← hfun x, ← hfun y, hxy])

/-- **The unit of the adjunction is non-zero on a free generator.**  The auxiliary `φ` is the
coordinate functional provided by `Work.Pi6.EMODD.exists_coord`. -/
lemma unit_app_ne_zero_of_gen (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜]
    (H : ModuleCat.{0} ℤ) (z : ↥H) (φ : H ⟶ ModuleCat.of ℤ ℤ) (hφ : φ.hom z = 1) :
    (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj H) from
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app H z) ≠ 0 := by
  intro h
  have h2 : (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of ℤ ℤ)) from
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app
          (ModuleCat.of ℤ ℤ) (φ.hom z)) = 0 := by
    rw [← extendScalars_map_unit 𝕜 φ z]
    exact congrArg (fun w => ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map φ).hom
      (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj H) from w)) h
  rw [hφ] at h2
  exact unit_app_one_ne_zero 𝕜 h2

/-! ## The coordinate functional of a free generator -/

/-- **A free generator of a `ℤ`-module admits a coordinate functional.**  If every element of `H`
is an integer multiple of `z` and the multiplier is unique, then the map `n ↦ n • z` is a linear
equivalence `ℤ ≅ H`, and its inverse is the required functional. -/
theorem exists_coord (H : ModuleCat.{0} ℤ) (z : ↥H)
    (hgen : ∀ y : ↥H, ∃! n : ℤ, y = n • z) :
    ∃ φ : ↥H →ₗ[ℤ] ℤ, φ z = 1 := by
  let s : ℤ →ₗ[ℤ] ↥H := LinearMap.toSpanSingleton ℤ ↥H z
  have hsz : ∀ n : ℤ, s n = n • z := fun n => Int.cast_smul_eq_zsmul ℤ n z
  have hs1 : s 1 = z := by
    have := hsz 1
    simpa using this
  have hs : Function.Bijective s := by
    constructor
    · intro a b hab
      have h1 : a = (hgen (s a)).exists.choose :=
        ((hgen (s a)).unique (hsz a) (hgen (s a)).exists.choose_spec)
      have h2 : b = (hgen (s b)).exists.choose :=
        ((hgen (s b)).unique (hsz b) (hgen (s b)).exists.choose_spec)
      rw [h1, h2, hab]
    · intro y
      obtain ⟨n, hn, -⟩ := hgen y
      exact ⟨n, by rw [hn]; exact hsz n⟩
  refine ⟨(LinearEquiv.ofBijective s hs).symm.toLinearMap, ?_⟩
  rw [← hs1, LinearEquiv.coe_toLinearMap]
  change (LinearEquiv.ofBijective s hs).symm ((LinearEquiv.ofBijective s hs) 1) = 1
  exact LinearEquiv.symm_apply_apply _ 1

/-! ## A general form of "a vanishing class is a boundary" -/

/-- A cycle of a chain complex of `R`-modules whose homology class vanishes is a boundary. -/
theorem chain_homologypi_eq_zero_gen (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat R) ℕ) [∀ i, K.HasHomology i]
    (n : ℕ) (z : K.cycles n) (h : (K.homologyπ n).hom z = 0) :
    ∃ y : ↥(K.X (n + 1)), (K.d (n + 1) n).hom y = (K.iCycles n).hom z := by
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 := by
    rw [ComplexShape.prev_eq']
    rfl
  let z' : (K.sc n).cycles := z
  have hkey : ∃ w : ↥((K.sc n).X₁), (K.sc n).f.hom w = (K.sc n).iCycles.hom z' := by
    have hzero : (K.sc n).homologyι ((K.sc n).homologyπ z') = 0 := by
      rw [show (K.sc n).homologyπ z' = 0 from h, map_zero]
    have hpop : (K.sc n).pOpcycles ((K.sc n).iCycles.hom z') = 0 := by
      have hh := congrArg (fun (g : (K.sc n).cycles ⟶ (K.sc n).opcycles) => g z')
        (ShortComplex.homology_π_ι (K.sc n))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      rw [← hh]
      exact hzero
    have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc n)
      ((K.sc n).iCycles.hom z')).mp hpop
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hkey
  refine ⟨(K.XIsoOfEq hprev).hom w, ?_⟩
  have hh := congrArg (fun (g : K.X ((ComplexShape.down ℕ).prev n) ⟶ K.X n) =>
    (ConcreteCategory.hom g) w) (HomologicalComplex.XIsoOfEq_hom_comp_d K hprev n)
  rw [show (K.d (n + 1) n).hom ((K.XIsoOfEq hprev).hom w)
      = (K.d ((ComplexShape.down ℕ).prev n) n).hom w from by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh]
  exact hw


/-! ## The main statement -/

/-- The range of the inclusion of the cycles is the kernel of the differential. -/
lemma range_iCycles_eq_ker (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    LinearMap.range (C.iCycles 2).hom = (C.d 2 1).hom.ker := by
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    have h := congrArg (fun (g : C.cycles 2 ⟶ C.X 1) => (ConcreteCategory.hom g) w)
      (HomologicalComplex.iCycles_d C 2 1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    simpa using h
  · intro x hx
    exact ⟨Work.RatHurewicz.Bridge.cycleOf C 2 (by norm_num) x (by simpa using hx),
      Work.RatHurewicz.Bridge.iCycles_cycleOf C 2 (by norm_num) x (by simpa using hx)⟩

/-- **The `ℤ → 𝕜` base change of a generating cycle is non-zero in `H₂`.**  Let `C` be a chain
complex of `ℤ`-modules, `ζ` a `2`-cycle of `C` whose homology class `[ζ]` generates `H₂(C) ≅ ℤ`
freely, and suppose `C₂ ⧸ Z₂` flat over `ℤ`.  Then in the base
changed complex `C ⊗[ℤ] 𝕜`, the class of the cycle whose underlying chain is the image of `ζ`
under the unit `x ↦ 1 ⊗ x` is non-zero. -/
theorem tmulCycleNeZero (𝕜 : Type) [CommRing 𝕜] [Nontrivial 𝕜]
    (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (ζ : C.cycles 2)
    (hgen : ∀ y : C.homology 2, ∃! n : ℤ, y = n • (C.homologyπ 2).hom ζ)
    (hflat : Module.Flat ℤ ↥(LinearMap.range (C.d 2 1).hom))
    (z : (Work.Pi6.SRANGE.baseChange 𝕜 C).cycles 2)
    (hz : ((Work.Pi6.SRANGE.baseChange 𝕜 C).iCycles 2).hom z
        = (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app (C.X 2)
            ((C.iCycles 2).hom ζ)) :
    ((Work.Pi6.SRANGE.baseChange 𝕜 C).homologyπ 2).hom z ≠ 0 := by
  intro hzero
  have hinj : Function.Injective
      ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.iCycles 2)).hom := by
    let P := LinearMap.range (C.d 2 1).hom
    letI : Module ℤ ↥P := P.module
    haveI hfl : Module.Flat ℤ ↥P := by
      convert hflat using 1
      exact Subsingleton.elim _ _
    refine injective_extendScalars_map 𝕜
      (f := ModuleCat.ofHom ((C.d 2 1).hom.codRestrict P (fun x => ⟨x, rfl⟩)))
      ?_ (C.iCycles 2) ?_ ?_
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
    · exact ModuleCat.mono_iff_injective _ |>.mp inferInstance
    · rw [LinearMap.exact_iff, range_iCycles_eq_ker C]
      ext x
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
  obtain ⟨y, hy⟩ := chain_homologypi_eq_zero_gen 𝕜 (Work.Pi6.SRANGE.baseChange 𝕜 C) 2 z hzero
  have hstep : ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.iCycles 2)).hom
        (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.toCycles 3 2)).hom y)
      = ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.iCycles 2)).hom
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app (C.cycles 2) ζ) := by
    rw [extendScalars_map_unit 𝕜 (C.iCycles 2) ζ]
    rw [← hz, ← hy]
    have h1 : ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.toCycles 3 2)) ≫
        ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.iCycles 2))
        = (ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.d 3 2) := by
      rw [← Functor.map_comp, HomologicalComplex.toCycles_i]
    have h2 := congrArg (fun (g : (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.X 3) ⟶
      (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.X 2)) => (ConcreteCategory.hom g) y) h1
    simpa using h2
  have heq : ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.toCycles 3 2)).hom y
      = (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app (C.cycles 2) ζ :=
    hinj hstep
  have hcontra : (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.homology 2)) from
        (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom 𝕜)).unit.app (C.homology 2)
          ((C.homologyπ 2).hom ζ)) = 0 := by
    have h := congrArg (fun w => ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map
      (C.homologyπ 2)).hom
      (show ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.cycles 2)) from w)) heq
    rw [extendScalars_map_unit 𝕜 (C.homologyπ 2) ζ] at h
    have hzero' : ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.homologyπ 2)).hom
        (((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.toCycles 3 2)).hom y) = 0 := by
      have h1 : ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.toCycles 3 2)) ≫
          ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).map (C.homologyπ 2)) = 0 := by
        rw [← Functor.map_comp, HomologicalComplex.toCycles_comp_homologyπ (K := C) 3 2,
          Functor.map_zero]
      have h2 := congrArg (fun (g : (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.X 3) ⟶
        (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (C.homology 2)) =>
          (ConcreteCategory.hom g) y) h1
      simpa using h2
    rw [hzero'] at h
    exact h.symm
  obtain ⟨φ, hφ⟩ := exists_coord (C.homology 2) ((C.homologyπ 2).hom ζ) hgen
  exact unit_app_ne_zero_of_gen 𝕜 (C.homology 2) ((C.homologyπ 2).hom ζ)
    (ModuleCat.ofHom φ) hφ hcontra



/-- Naturality of `homologyπ` under `homologyMap`, for complexes of `R`-modules. -/
theorem homologyMap_homologyπ_gen (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (φ : K ⟶ L) (i : ℕ) (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z)
      = (L.homologyπ i).hom (HomologicalComplex.cyclesMap φ i z) := by
  have h := HomologicalComplex.homologyπ_naturality (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => (ConcreteCategory.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The underlying chain of the `cyclesMap` of a cycle, for complexes of `R`-modules. -/
theorem iCycles_cyclesMap_gen (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (φ : K ⟶ L) (i : ℕ) (z : K.cycles i) :
    (L.iCycles i).hom (HomologicalComplex.cyclesMap φ i z)
      = (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := HomologicalComplex.cyclesMap_i (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.X i) => (ConcreteCategory.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- A cycle of a chain complex of `R`-modules whose differential vanishes. -/
theorem exists_iCycles_eq (R : Type) [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : 1 ≤ n) (x : ↥(K.X n)) (hx : (K.d n (n - 1)).hom x = 0) :
    ∃ z : K.cycles n, (K.iCycles n).hom z = x := by
  have aux : ModuleCat.ofHom (X := (ModuleCat.of R R : ModuleCat.{0} R)) (Y := K.X n)
      (LinearMap.toSpanSingleton R ↥(K.X n) x) ≫ K.d n (n - 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (K.d n (n - 1)).hom ((LinearMap.toSpanSingleton R (K.X n) x) 1) = 0
    rw [LinearMap.toSpanSingleton_apply, one_smul]
    exact hx
  refine ⟨(K.liftCycles (ModuleCat.ofHom (X := (ModuleCat.of R R : ModuleCat.{0} R)) (Y := K.X n)
    (LinearMap.toSpanSingleton R ↥(K.X n) x)) (n - 1)
    ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel hn)))
    aux).hom 1, ?_⟩
  have hlift := HomologicalComplex.liftCycles_i (K := K) (i := n)
    (ModuleCat.ofHom (X := (ModuleCat.of R R : ModuleCat.{0} R)) (Y := K.X n)
      (LinearMap.toSpanSingleton R ↥(K.X n) x)) (n - 1)
    ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk n (n - 1) (Nat.sub_add_cancel hn))) aux
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ K.X n) => (ConcreteCategory.hom g) (1 : R)) hlift
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]
  change (LinearMap.toSpanSingleton R ↥(K.X n) x) 1 = x
  rw [LinearMap.toSpanSingleton_apply, one_smul]


end

end Work.Pi6.EMODD
