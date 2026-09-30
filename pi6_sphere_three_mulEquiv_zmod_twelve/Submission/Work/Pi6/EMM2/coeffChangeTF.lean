import Mathlib
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Pi6.SRANGE.rTensor_injective_of_torsionFree_quotient
import Submission.Work.Pi6.SRANGE.homQuot_bridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-!
# Change of coefficients `ℤ → 𝕜` for a chain complex whose homology is torsion-free

For a chain complex `K` of `ℤ`-modules with *free* terms and a degree `m` in which the homology
`H_m(K)` is torsion-free, the `(m+1)`-st homology of the coefficient extension `K ⊗ N` is the
extension of scalars of `H_{m+1}(K)`:

`H_{m+1}(K ⊗ N) ≅ H_{m+1}(K) ⊗ N`.

This file proves the two structural ingredients:

* `Work.Pi6.EMM2.ker_rTensor_d_of_torsionFree` — the kernel of `d ⊗ 1` in degree `m+1` is the
  tensor of the cycles `Z_{m+1} ⊗ N`, *without* assuming that `H_m(K)` vanishes: only that it is
  torsion-free (equivalently flat over `ℤ`);
* the flatness/torsion-freeness lemmas on the quotients `K_m ⧸ Z_m` and `Z_m ⧸ B_m` that the proof
  needs.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

/-! ## 1. Torsion-freeness of the structural quotients -/

/-- A submodule of a torsion-free `ℤ`-module is torsion-free (restrict an injective `r • ·`). -/
theorem isTorsionFree_subtype {B : Type*} [AddCommGroup B] [Module ℤ B]
    [Module.IsTorsionFree ℤ B] (S : Submodule ℤ B) : Module.IsTorsionFree ℤ ↥S := by
  refine ⟨fun r hr => ?_⟩
  have h := (‹Module.IsTorsionFree ℤ B›).isSMulRegular hr
  intro x y hxy
  apply Subtype.ext
  apply h
  simpa using congrArg (fun z : ↥S => (z : B)) hxy

/-- Torsion-freeness transfers along a linear equivalence. -/
theorem isTorsionFree_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree ℤ M :=
  Function.Injective.moduleIsTorsionFree e e.injective e.map_smul

/-- **`K_m ⧸ Z_m` is torsion-free** for a chain complex with free terms: it is isomorphic to the
range of the `m`-th differential, a submodule of the free module `K_{m-1}`. -/
theorem isTorsionFree_quot_uctZ (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i, Module.Free ℤ (K.X i)) :
    Module.IsTorsionFree ℤ (↥(K.X m) ⧸ Work.Cohomology.uctZ K m) := by
  haveI := hfree (m - 1)
  haveI : Module.IsTorsionFree ℤ ↥(LinearMap.range (K.d m (m - 1)).hom) :=
    isTorsionFree_subtype _
  exact isTorsionFree_of_linearEquiv (LinearMap.quotKerEquivRange (K.d m (m - 1)).hom)

/-- **`Z_m ⧸ B_m` is torsion-free when `H_m(K)` is**: it *is* `H_m(K)`, by
`Work.Cohomology.homology_iso_H`. -/
theorem isTorsionFree_quot_uctH (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) :
    Module.IsTorsionFree ℤ (↥(Work.Cohomology.uctZ K m) ⧸ Work.Cohomology.uctH K m) := by
  haveI : Module.IsTorsionFree ℤ ↥(K.homology m) := hTF
  obtain ⟨e⟩ := Work.Cohomology.homology_iso_H K m
  exact isTorsionFree_of_linearEquiv (Work.Pi6.SRANGE.isoToLinearEquiv e).symm

/-! ## 2. The kernel of `d ⊗ 1` in degree `m+1` -/

/-- **The tensored kernel is the tensor of the kernel**, given directly the injectivity of
`f ⊗ 1` on the range of `f` (the `N`-flatness input of the usual statement). -/
theorem ker_rTensor_eq_range_subtype_of_injective {A : Type*} [AddCommGroup A] [Module ℤ A]
    {B : Type*} [AddCommGroup B] [Module ℤ B] {N : Type*} [AddCommGroup N] [Module ℤ N]
    (f : A →ₗ[ℤ] B)
    (hinj : Function.Injective (LinearMap.rTensor N (LinearMap.range f).subtype)) :
    LinearMap.ker (LinearMap.rTensor N f) =
      LinearMap.range (LinearMap.rTensor N (LinearMap.ker f).subtype) := by
  set g : A →ₗ[ℤ] ↥(LinearMap.range f) := f.codRestrict (LinearMap.range f) fun x => ⟨x, rfl⟩
    with hg
  have hgker : LinearMap.ker g = LinearMap.ker f := by
    ext x
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  have hgsurj : Function.Surjective g := fun y => by
    obtain ⟨a, ha⟩ := y.2
    exact ⟨a, Subtype.ext ha⟩
  have hfact : f = (LinearMap.range f).subtype ∘ₗ g := by ext x; rfl
  have hkerbot : LinearMap.ker (LinearMap.rTensor N (LinearMap.range f).subtype) = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hinj
  have hex : LinearMap.ker (LinearMap.rTensor N g) =
      LinearMap.range (LinearMap.rTensor N (LinearMap.ker g).subtype) := by
    have h2 : Function.Exact (LinearMap.rTensor N (LinearMap.ker g).subtype)
        (LinearMap.rTensor N g) :=
      _root_.rTensor_exact N (LinearMap.exact_subtype_ker_map g) hgsurj
    exact LinearMap.exact_iff.mp h2
  have hcomp : LinearMap.rTensor N f =
      LinearMap.rTensor N (LinearMap.range f).subtype ∘ₗ LinearMap.rTensor N g := by
    rw [← LinearMap.rTensor_comp]
    exact congrArg (LinearMap.rTensor N) hfact
  have hA : LinearMap.ker (LinearMap.rTensor N (LinearMap.range f).subtype ∘ₗ
        LinearMap.rTensor N g) =
      LinearMap.range (LinearMap.rTensor N (LinearMap.ker g).subtype) := by
    rw [LinearMap.ker_comp, hkerbot, Submodule.comap_bot]
    exact hex
  have hmain : LinearMap.ker (LinearMap.rTensor N f) =
      LinearMap.range (LinearMap.rTensor N (LinearMap.ker g).subtype) := by
    rw [hcomp, hA]
  rw [hmain, hgker]

/-- **`B_m ⊗ N → K_m ⊗ N` is injective when `H_m(K)` is torsion-free.**  The inclusion of the
`m`-boundaries in `K_m` factors as `B_m ↪ Z_m ↪ K_m`; the first factor is injective after tensoring
because `Z_m ⧸ B_m ≅ H_m(K)` is torsion-free, the second because `K_m ⧸ Z_m` is torsion-free
(it is the range of the `m`-th differential, inside the free module `K_{m-1}`). -/
theorem rTensor_uctB_subtype_injective (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i, Module.Free ℤ (K.X i))
    (hTF : Module.IsTorsionFree ℤ (K.homology m)) (N : ModuleCat.{0, 0} ℤ) :
    Function.Injective (LinearMap.rTensor ↥N (Work.Cohomology.uctB K m).subtype) := by
  have hle : Work.Cohomology.uctB K m ≤ Work.Cohomology.uctZ K m :=
    Work.Cohomology.uctB_le_uctZ K m
  set ι : ↥(Work.Cohomology.uctB K m) →ₗ[ℤ] ↥(Work.Cohomology.uctZ K m) :=
    Submodule.inclusion hle with hιdef
  have hιinj : Function.Injective ι := by
    intro x y hxy
    have h := congrArg (fun z : ↥(Work.Cohomology.uctZ K m) => (z : ↥(K.X m))) hxy
    simpa [hιdef] using h
  haveI : Module.IsTorsionFree ℤ ↥(Work.Cohomology.uctZ K m) := isTorsionFree_subtype _
  have hrange : LinearMap.range ι = Work.Cohomology.uctH K m := by
    rw [Work.Cohomology.uctH_eq_comap, hιdef, Submodule.inclusion, LinearMap.range_codRestrict,
      Submodule.range_subtype]
  haveI hq : Module.IsTorsionFree ℤ (↥(Work.Cohomology.uctZ K m) ⧸ Work.Cohomology.uctH K m) :=
    isTorsionFree_quot_uctH K m hTF
  haveI : Module.IsTorsionFree ℤ (↥(Work.Cohomology.uctZ K m) ⧸ LinearMap.range ι) :=
    isTorsionFree_of_linearEquiv (Submodule.quotEquivOfEq _ _ hrange)
  have hinj₁ : Function.Injective (LinearMap.rTensor ↥N ι) := by
    haveI : Module.Flat ℤ (↥(Work.Cohomology.uctZ K m) ⧸ LinearMap.range ι) := inferInstance
    have hl : Function.Injective (ι.lTensor ↥N) :=
      LinearMap.lTensor_injective_of_exact_of_flat (f := Submodule.mkQ (LinearMap.range ι))
        (Submodule.mkQ_surjective _) ι hιinj (by rw [LinearMap.exact_iff]; simp) ↥N
    exact (ι.lTensor_inj_iff_rTensor_inj ↥N).mp hl
  haveI hXm : Module.IsTorsionFree ℤ ↥(K.X m) := inferInstance
  haveI : Module.IsTorsionFree ℤ
      (↥(K.X m) ⧸ LinearMap.range (Work.Cohomology.uctZ K m).subtype) := by
    rw [Submodule.range_subtype]
    exact isTorsionFree_quot_uctZ K m hfree
  have hinj₂ : Function.Injective (LinearMap.rTensor ↥N (Work.Cohomology.uctZ K m).subtype) := by
    haveI : Module.Flat ℤ
        (↥(K.X m) ⧸ LinearMap.range (Work.Cohomology.uctZ K m).subtype) := inferInstance
    have hl : Function.Injective ((Work.Cohomology.uctZ K m).subtype.lTensor ↥N) :=
      LinearMap.lTensor_injective_of_exact_of_flat
        (f := Submodule.mkQ (LinearMap.range (Work.Cohomology.uctZ K m).subtype))
        (Submodule.mkQ_surjective _) (Work.Cohomology.uctZ K m).subtype
        (Submodule.subtype_injective _) (by rw [LinearMap.exact_iff]; simp) ↥N
    exact ((Work.Cohomology.uctZ K m).subtype.lTensor_inj_iff_rTensor_inj ↥N).mp hl
  have hcomp : (Work.Cohomology.uctB K m).subtype =
      (Work.Cohomology.uctZ K m).subtype ∘ₗ ι := by
    ext x
    simp [hιdef]
  rw [hcomp, LinearMap.rTensor_comp]
  exact hinj₂.comp hinj₁

/-- **The kernel of `d ⊗ 1` in degree `m+1`**, under the hypothesis that `H_m(K)` is torsion-free
(rather than zero): it is the tensor of the `(m+1)`-cycles. -/
theorem ker_rTensor_d_of_torsionFree (K : ChainComplex (ModuleCat.{0, 0} ℤ) ℕ) (m : ℕ)
    (hfree : ∀ i, Module.Free ℤ (K.X i)) (hTF : Module.IsTorsionFree ℤ (K.homology m))
    (N : ModuleCat.{0, 0} ℤ) :
    LinearMap.ker (LinearMap.rTensor ↥N ((K.d (m + 1) m).hom)) =
      LinearMap.range (LinearMap.rTensor ↥N (Work.Cohomology.uctZ K (m + 1)).subtype) := by
  refine ker_rTensor_eq_range_subtype_of_injective (K.d (m + 1) m).hom ?_
  exact rTensor_uctB_subtype_injective K m hfree hTF N

end

end Work.Pi6.EMM2
