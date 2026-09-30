import Mathlib
import Submission.Work.Pi6.EMM2.coeffChangeTF
import Submission.Work.Pi6.SRANGE.homQuot_bridge
import Submission.Work.Cohomology.uctDefs
import Submission.Work.SSS.ExpTens
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-!
# Change of coefficients for a chain complex of free `ℤ`-modules, in one degree

`Work.Pi6.EMM2.expTens_homology_iso`: for a chain complex `K` of free `ℤ`-modules whose `m`-th
homology is torsion-free and any `ℤ`-module `N`, the `(m+1)`-st homology of the coefficient
extension `K ⊗ N` is `N ⊗ H_{m+1}(K)`.

The proof uses the concrete models of the homology: with `Z := ker d_{m+1}`, `B := im d_{m+2}`
inside `K_{m+1}`,

* `H_{m+1}(K ⊗ N) = ker (d_{m+1} ⊗ 1) / im (d_{m+2} ⊗ 1)` (the standard cycles/boundaries model),
* `ker (d_{m+1} ⊗ 1) = Z ⊗ N` by `Work.Pi6.EMM2.ker_rTensor_d_of_torsionFree` (here the
  torsion-freeness of `H_m` enters), `im (d_{m+2} ⊗ 1) = B ⊗ N` by right exactness,
* hence `H_{m+1}(K ⊗ N) ≅ (Z ⊗ N)/(B ⊗ N) ≅ (Z/B) ⊗ N = H_{m+1}(K) ⊗ N` by right exactness again.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

noncomputable section

variable {K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ}

/-! ## 1. The differential and the cycles/boundaries of `expTens` -/

/-- The differential of the coefficient extension `expTens K N` is `d ⊗ 1`. -/
theorem expTens_d_rTensor (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (N : ModuleCat.{0, 0} ℤ)
    (n : ℕ) :
    ((Work.SSS.expTens K N).d (n + 1) n).hom =
      LinearMap.rTensor ↥N ((K.d (n + 1) n).hom) := by
  rw [Work.SSS.expTens_d]
  rfl

/-- The cycles of `expTens K N` in degree `m+1` are the kernel of `d_{m+1} ⊗ 1`. -/
theorem uctZ_expTens' (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (N : ModuleCat.{0, 0} ℤ)
    (m : ℕ) :
    Work.Cohomology.uctZ (Work.SSS.expTens K N) (m + 1) =
      LinearMap.ker (LinearMap.rTensor ↥N ((K.d (m + 1) m).hom)) := by
  rw [Work.Cohomology.uctZ, show m + 1 - 1 = m from rfl, expTens_d_rTensor]

/-- The boundaries of `expTens K N` in degree `m+1` are the range of `d_{m+2} ⊗ 1`. -/
theorem uctB_expTens' (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (N : ModuleCat.{0, 0} ℤ)
    (m : ℕ) :
    Work.Cohomology.uctB (Work.SSS.expTens K N) (m + 1) =
      LinearMap.range (LinearMap.rTensor ↥N ((K.d (m + 2) (m + 1)).hom)) := by
  rw [Work.Cohomology.uctB, show m + 1 + 1 = m + 2 from rfl, expTens_d_rTensor]

/-- **The range of `d_{m+2} ⊗ 1` is the range of `B_{m+1} ⊗ 1`**, where `B_{m+1}` is the range of
`d_{m+2}`: right exactness of the tensor product. -/
theorem range_rTensor_d_eq (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (N : ModuleCat.{0, 0} ℤ)
    (m : ℕ) :
    LinearMap.range (LinearMap.rTensor ↥N ((K.d (m + 2) (m + 1)).hom)) =
      LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctB K (m + 1)).subtype) := by
  set g : ↥(K.X (m + 2)) →ₗ[ℤ] ↥(Work.Cohomology.uctB K (m + 1)) :=
    ((K.d (m + 2) (m + 1)).hom).codRestrict (Work.Cohomology.uctB K (m + 1))
      (fun x => ⟨x, rfl⟩) with hg
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, Subtype.ext rfl⟩
  have hfact : (K.d (m + 2) (m + 1)).hom =
      (Work.Cohomology.uctB K (m + 1)).subtype ∘ₗ g := by ext x; rfl
  have hcomp : LinearMap.rTensor ↥N ((K.d (m + 2) (m + 1)).hom) =
      LinearMap.rTensor ↥N (Work.Cohomology.uctB K (m + 1)).subtype ∘ₗ
        LinearMap.rTensor ↥N g := by
    rw [← LinearMap.rTensor_comp]
    exact congrArg (LinearMap.rTensor ↥N) hfact
  rw [hcomp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective ↥N hgsurj), Submodule.map_top]

/-! ## 2. A quotient of a range by a range -/

universe u

variable {M N P : Type u} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  [AddCommGroup P] [Module ℤ P]

/-- **Quotients of ranges.**  For an injective `f : M →ₗ N` and any `h : P →ₗ M`, the quotient of
the range of `f` by the image of the range of `h` is the quotient `M ⧸ range h`: the map `f`
identifies `M` with its range and `range h` with its image. -/
theorem quot_range_range (f : M →ₗ[ℤ] N) (hinj : Function.Injective f) (h : P →ₗ[ℤ] M) :
    Nonempty ((↥(LinearMap.range f) ⧸
        (LinearMap.range (f ∘ₗ h)).comap (LinearMap.range f).subtype) ≃ₗ[ℤ]
      (M ⧸ LinearMap.range h)) := by
  have hle : LinearMap.range h ≤ Submodule.comap f.rangeRestrict
      ((LinearMap.range (f ∘ₗ h)).comap (LinearMap.range f).subtype) := by
    rintro - ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  let q : Submodule ℤ ↥(LinearMap.range f) :=
    (LinearMap.range (f ∘ₗ h)).comap (LinearMap.range f).subtype
  let Ψ : (M ⧸ LinearMap.range h) →ₗ[ℤ] (↥(LinearMap.range f) ⧸ q) :=
    (LinearMap.range h).mapQ q f.rangeRestrict hle
  have hker_le : Submodule.comap f.rangeRestrict q ≤ LinearMap.range h := by
    intro x hx
    change f.rangeRestrict x ∈
      (LinearMap.range (f ∘ₗ h)).comap (LinearMap.range f).subtype at hx
    rw [Submodule.mem_comap, LinearMap.mem_range] at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨w, hinj ?_⟩
    simpa using hw
  have hker : LinearMap.ker Ψ = ⊥ := by
    rw [Submodule.ker_mapQ, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (Submodule.Quotient.eq (p := LinearMap.range h)).mpr (by simpa using hker_le hy)
  have hrange : LinearMap.range Ψ = ⊤ := by
    rw [Submodule.range_mapQ, LinearMap.range_rangeRestrict, Submodule.map_top,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective q)]
  exact ⟨(LinearEquiv.ofBijective Ψ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩).symm⟩

/-- The inclusion `Z ⊗ N → K ⧸ Z` stays injective after tensoring, `K` having free terms. -/
theorem rTensor_uctZ_subtype_injective (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i, Module.Free ℤ (K.X i)) (N : ModuleCat.{0, 0} ℤ) :
    Function.Injective (LinearMap.rTensor ↥N (Work.Cohomology.uctZ K m).subtype) := by
  haveI hXm : Module.IsTorsionFree ℤ ↥(K.X m) := inferInstance
  haveI : Module.IsTorsionFree ℤ
      (↥(K.X m) ⧸ LinearMap.range (Work.Cohomology.uctZ K m).subtype) := by
    rw [Submodule.range_subtype]
    exact isTorsionFree_quot_uctZ K m hfree
  haveI : Module.Flat ℤ
      (↥(K.X m) ⧸ LinearMap.range (Work.Cohomology.uctZ K m).subtype) := inferInstance
  have hl : Function.Injective ((Work.Cohomology.uctZ K m).subtype.lTensor ↥N) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (f := Submodule.mkQ (LinearMap.range (Work.Cohomology.uctZ K m).subtype))
      (Submodule.mkQ_surjective _) (Work.Cohomology.uctZ K m).subtype
      (Submodule.subtype_injective _) (by rw [LinearMap.exact_iff]; simp) ↥N
  exact ((Work.Cohomology.uctZ K m).subtype.lTensor_inj_iff_rTensor_inj ↥N).mp hl

/-- The range of `B ↪ Z` (the boundaries inside the cycles) is `uctH`. -/
theorem range_inclusion_eq_uctH (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ) :
    LinearMap.range (Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K m)) =
      Work.Cohomology.uctH K m := by
  rw [Work.Cohomology.uctH_eq_comap, Submodule.inclusion, LinearMap.range_codRestrict,
    Submodule.range_subtype]

/-! ## 3. The change of coefficients in one degree -/

/-- The range of `rTensor N f` does not change if `f` is replaced by the inclusion of its range. -/
theorem range_rTensor_eq_range_rTensor_rangeRestrict {B Z : Type*} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup Z] [Module ℤ Z] (ι : B →ₗ[ℤ] Z) {N : Type*} [AddCommGroup N] [Module ℤ N] :
    LinearMap.range (LinearMap.rTensor N ι) =
      LinearMap.range (LinearMap.rTensor N ι.range.subtype) := by
  conv_lhs => rw [show ι = ι.range.subtype ∘ₗ ι.rangeRestrict from
    (LinearMap.subtype_comp_rangeRestrict ι).symm]
  rw [LinearMap.rTensor_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective N (LinearMap.surjective_rangeRestrict ι)),
    Submodule.map_top]

/-- **The `(m+1)`-cycles of `expTens K N` are the image of the cycles of `K` tensored with
`N`.** -/
theorem mem_cycles_expTens (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i)) (hTF : Module.IsTorsionFree ℤ (K.homology m))
    (N : ModuleCat.{0, 0} ℤ) (y : ↥(Work.Cohomology.uctZ K (m + 1)) ⊗[ℤ] ↥N) :
    LinearMap.rTensor ↥N (Work.Cohomology.uctZ K (m + 1)).subtype y ∈
      LinearMap.ker (((Work.SSS.expTens K N).d (m + 1) m).hom) := by
  rw [expTens_d_rTensor, LinearMap.mem_ker]
  change (LinearMap.rTensor ↥N ((K.d (m + 1) m).hom) ∘ₗ
    LinearMap.rTensor ↥N (Work.Cohomology.uctZ K (m + 1)).subtype) y = 0
  rw [← LinearMap.rTensor_comp]
  have h0 : (K.d (m + 1) m).hom ∘ₗ (Work.Cohomology.uctZ K (m + 1)).subtype = 0 := by
    ext x
    exact x.2
  rw [h0, LinearMap.rTensor_zero]
  rfl

/-- **Every `(m+1)`-cycle of `expTens K N` is the image of a cycle of `K`** (this is where
torsion-freeness of `H_m` enters, through
`Work.Pi6.EMM2.ker_rTensor_d_of_torsionFree`). -/
theorem mem_range_cycles_expTens (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i)) (hTF : Module.IsTorsionFree ℤ (K.homology m))
    (N : ModuleCat.{0, 0} ℤ) (z : ↥((Work.SSS.expTens K N).X (m + 1)))
    (hz : z ∈ LinearMap.ker (((Work.SSS.expTens K N).d (m + 1) m).hom)) :
    z ∈ LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctZ K (m + 1)).subtype) := by
  have hz' : z ∈ LinearMap.ker (LinearMap.rTensor ↥N ((K.d (m + 1) m).hom)) := by
    rw [← expTens_d_rTensor K N m]
    exact hz
  rw [ker_rTensor_d_of_torsionFree K m hfree hTF N] at hz'
  exact hz'

/-- **The `(m+1)`-boundaries of `expTens K N` are the image of the boundaries of `K` tensored
with `N`.** -/
theorem mem_range_bounds_expTens (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (N : ModuleCat.{0, 0} ℤ) (y : ↥(K.X (m + 1)) ⊗[ℤ] ↥N) :
    y ∈ LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctB K (m + 1)).subtype) ↔
      y ∈ LinearMap.range (((Work.SSS.expTens K N).d (m + 2) (m + 1)).hom) := by
  have h1 : LinearMap.range (((Work.SSS.expTens K N).d (m + 2) (m + 1)).hom) =
      LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctB K (m + 1)).subtype) := by
    rw [← Work.Cohomology.uctB, uctB_expTens', range_rTensor_d_eq]
  rw [h1]

/-- **`H_{m+1}(K ⊗ N) ≅ H_{m+1}(K) ⊗ N`** for a chain complex `K` of free `ℤ`-modules whose `m`-th
homology is torsion-free. -/
theorem expTens_homology_iso (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i : ℕ, Module.Free ℤ (K.X i)) (hTF : Module.IsTorsionFree ℤ (K.homology m))
    (N : ModuleCat.{0, 0} ℤ) :
    Nonempty ((Work.SSS.expTens K N).homology (m + 1) ≅
      ModuleCat.of ℤ (↥N ⊗[ℤ] ↥(K.homology (m + 1)))) := by
  obtain ⟨eK⟩ := Work.Cohomology.homology_iso_H K (m + 1)
  set ι : ↥(Work.Cohomology.uctB K (m + 1)) →ₗ[ℤ] ↥(Work.Cohomology.uctZ K (m + 1)) :=
    Submodule.inclusion (Work.Cohomology.uctB_le_uctZ K (m + 1)) with hιdef
  set f : (↥(Work.Cohomology.uctZ K (m + 1)) ⊗[ℤ] ↥N) →ₗ[ℤ]
      (↥(K.X (m + 1)) ⊗[ℤ] ↥N) :=
    LinearMap.rTensor ↥N (Work.Cohomology.uctZ K (m + 1)).subtype with hfdef
  have hfinj : Function.Injective f := by
    rw [hfdef]; exact rTensor_uctZ_subtype_injective K (m + 1) hfree N
  have hιsub : (Work.Cohomology.uctB K (m + 1)).subtype =
      (Work.Cohomology.uctZ K (m + 1)).subtype ∘ₗ ι := by
    rw [hιdef]; ext x; rfl
  -- the image of the boundary inclusion is the image of the range inclusion under `f`
  have hmap : LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctB K (m + 1)).subtype) =
      Submodule.map f (LinearMap.range (LinearMap.rTensor ↥N ι)) := by
    rw [hιsub, LinearMap.rTensor_comp, LinearMap.range_comp, hfdef]
  -- the map from the cycles of `K` tensored with `N` to the homology of `expTens K N`
  let Ψ : (↥(Work.Cohomology.uctZ K (m + 1)) ⊗[ℤ] ↥N) →ₗ[ℤ]
      Work.Pi6.SRANGE.homQuot ℤ (Work.SSS.expTens K N) (m + 1) :=
    (Submodule.mkQ _).comp (f.codRestrict (Work.Pi6.SRANGE.cycKer (Work.SSS.expTens K N) (m + 1))
      (fun y => mem_cycles_expTens K m hfree hTF N y))
  have hker : LinearMap.ker Ψ = LinearMap.range (LinearMap.rTensor ↥N ι) := by
    ext y
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk
        (f.codRestrict (Work.Pi6.SRANGE.cycKer (Work.SSS.expTens K N) (m + 1))
          (fun y => mem_cycles_expTens K m hfree hTF N y) y) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    change f y ∈ LinearMap.range (((Work.SSS.expTens K N).d (m + 2) (m + 1)).hom) ↔ _
    rw [(mem_range_bounds_expTens K m N (f y)).symm, hmap]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
      rwa [hfinj hxy] at hx
    · intro hy
      exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have hsurj_mk : ∀ z : ↥(Work.Pi6.SRANGE.cycKer (Work.SSS.expTens K N) (m + 1)),
      ∃ y, Ψ y = Submodule.Quotient.mk z := by
    intro z
    obtain ⟨y, hy⟩ := mem_range_cycles_expTens K m hfree hTF N z.val z.2
    refine ⟨y, ?_⟩
    show Submodule.Quotient.mk (f.codRestrict _ _ y) = Submodule.Quotient.mk z
    exact congrArg Submodule.Quotient.mk (Subtype.ext (by simpa [hfdef] using hy))
  have hsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (p := (LinearMap.range (((Work.SSS.expTens K N).d (m + 2) (m + 1)).hom)).comap
        (Work.Pi6.SRANGE.cycKer (Work.SSS.expTens K N) (m + 1)).subtype) w
    exact hsurj_mk z
  -- the quotient by the kernel
  have hstepA : ((↥(Work.Cohomology.uctZ K (m + 1)) ⊗[ℤ] ↥N) ⧸
      LinearMap.range (LinearMap.rTensor ↥N ι)) ≃ₗ[ℤ]
      Work.Pi6.SRANGE.homQuot ℤ (Work.SSS.expTens K N) (m + 1) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective Ψ hsurj)
  -- `(Z ⊗ N)/(B ⊗ N) ≅ (Z/B) ⊗ N`
  have hstepB : ((↥(Work.Cohomology.uctZ K (m + 1)) ⊗[ℤ] ↥N) ⧸
      LinearMap.range (LinearMap.rTensor ↥N ι)) ≃ₗ[ℤ]
      ((↥(Work.Cohomology.uctZ K (m + 1)) ⧸ Work.Cohomology.uctH K (m + 1)) ⊗[ℤ] ↥N) := by
    have hS : LinearMap.range (LinearMap.rTensor ↥N ι) =
        LinearMap.ker (LinearMap.rTensor ↥N (Submodule.mkQ (Work.Cohomology.uctH K (m + 1)))) := by
      have hr : (Work.Cohomology.uctH K (m + 1)) = ι.range := by
        rw [hιdef]
        exact (range_inclusion_eq_uctH K (m + 1)).symm
      rw [rTensor_mkQ (Q := ↥N), hr, ← range_rTensor_eq_range_rTensor_rangeRestrict ι]
    exact (Submodule.quotEquivOfEq _ _ hS).trans
      (LinearMap.quotKerEquivOfSurjective _
        (LinearMap.rTensor_surjective ↥N (Submodule.mkQ_surjective _)))
  -- the homology of `K`
  have hstepC : ((↥(Work.Cohomology.uctZ K (m + 1)) ⧸ Work.Cohomology.uctH K (m + 1)) ⊗[ℤ] ↥N)
      ≃ₗ[ℤ] (↥(K.homology (m + 1)) ⊗[ℤ] ↥N) :=
    (Work.Pi6.SRANGE.isoToLinearEquiv eK).symm.rTensor ↥N
  have hcomp : ↥((Work.SSS.expTens K N).homology (m + 1)) ≃ₗ[ℤ]
      (↥N ⊗[ℤ] ↥(K.homology (m + 1))) :=
    ((Work.Pi6.SRANGE.homQuotEquiv (Work.SSS.expTens K N) (m + 1)).symm.trans hstepA.symm).trans
      (hstepB.trans (hstepC.trans (TensorProduct.comm ℤ ↥(K.homology (m + 1)) ↥N)))
  exact ⟨LinearEquiv.toModuleIso hcomp⟩
end

end Work.Pi6.EMM2
