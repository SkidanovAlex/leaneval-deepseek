import Mathlib
import Submission.Work.DSG4a.CSB_Defs
import Submission.Work.DSG4a.chainSplitBC.bridge
import Submission.Work.DSG4a.chainSplitBC.chainSplit_condition_transfer
import Submission.Work.DSG4a.isUnimodular_tmul_presentMk_iff

/-!
# DSG4a / `chainSplit_ccBase_iff`

The chain-level splitting condition for the base-changed coaugmentation
`ccBase P cc : A'[0] ⟶ P ⊗[A] A'` is equivalent to the unimodularity of the base-changed model
element `1 ⊗ modelElem P cc` in `A' ⊗[A] (P.X 0 ⧸ im d⁻¹)`.

The proof is a chain of equivalences.

* `Criterion.ChainSplit C γ` unfolds to the existence of an `A'`-linear functional `s` on
  `C.X 0` which kills the differential `d⁻¹` and takes the value `1` at the unit
  `coaugElem C γ`; for `C = baseChangeComplex P` and `γ = ccBase P cc` that unit is
  `1 ⊗ coaugElem P cc` (`coaugElem_ccBase`).
* The carrier of `(baseChangeComplex P).X 0` is the "compHom" tensor product
  `↥((restrictScalars (algebraMap A A')).obj (of A' A')) ⊗[A] ↥(P.X 0)`; the flavour bridge
  `extTensorEquiv` of `Submission.Work.DSG4a.chainSplitBC.bridge` identifies it `A'`-linearly
  with the algebra tensor `A' ⊗[A] ↥(P.X 0)`, and
  `chainSplit_condition_transfer` transfers the whole `∃ s` condition along it (using the
  generator values of the differential, `bridge.baseChangeComplex_d_tmul`).
* Tensor–hom adjunction for the extension of scalars `A → A'` (`ccAux.exists_ext_linearMap_iff`)
  turns an `A'`-linear functional on `A' ⊗[A] M` into an `A`-linear functional on `M`.
* Functionals on `M` killing `im d` are functionals on `M ⧸ im d`
  (`ccAux.exists_dual_iff`, the quotient/dual correspondence).
* Finally `Work.DSG4a.isUnimodular_tmul_iff` identifies the functional form of the
  unimodularity of `1 ⊗ e`, and `TensorProduct.mk_apply` matches the exact term of the goal.
-/

namespace Work.DSG4a.chainSplitBC

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct
open TensorProduct

set_option backward.isDefEq.respectTransparency false
universe u

namespace ccAux

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']

/-- **Tensor–hom adjunction for extension of scalars.** An `A'`-linear functional on
`A' ⊗[A] M₀` killing the base change of `d : M₁ →ₗ[A] M₀` and taking the value `1` at the pure
tensor `1 ⊗ e` is the same thing as an `A`-linear functional on `M₀` killing `d` and taking the
value `1` at `e`.

* forward: restrict scalars along `A → A'` and precompose with `m ↦ 1 ⊗ m`;
* backward: extend scalars by `a ⊗ m ↦ a • g m`, using `TensorProduct.AlgebraTensorModule.lift`.
-/
theorem exists_ext_linearMap_iff {M₁ M₀ : Type u} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₀] [Module A M₀] (d : M₁ →ₗ[A] M₀) (e : M₀) :
    (∃ s : (A' ⊗[A] M₀) →ₗ[A'] A',
        s.comp (d.baseChange A') = 0 ∧ s ((1 : A') ⊗ₜ[A] e) = 1) ↔
      ∃ g : M₀ →ₗ[A] A', g.comp d = 0 ∧ g e = 1 := by
  have lift_tmul : ∀ (g : M₀ →ₗ[A] A') (a : A') (m : M₀),
      (TensorProduct.AlgebraTensorModule.lift (A := A') (M := A') (N := M₀) (P := A')
        (({ toFun := fun d => d • g
            map_add' := fun d₁ d₂ => by simp [add_smul]
            map_smul' := fun d₁ d₂ => by simp [mul_smul] } : A' →ₗ[A'] (M₀ →ₗ[A] A'))))
        (a ⊗ₜ[A] m) = a • g m := by
    intro g a m
    rw [TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul]
    rfl
  constructor
  · rintro ⟨s, hs1, hs2⟩
    refine ⟨(LinearMap.restrictScalars A s).comp (TensorProduct.mk A A' M₀ (1 : A')), ?_, ?_⟩
    · refine LinearMap.ext (fun n => ?_)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, TensorProduct.mk_apply,
        LinearMap.restrictScalars_apply]
      rw [← LinearMap.baseChange_tmul (f := d) (a := (1 : A')) (x := n)]
      have := LinearMap.congr_fun hs1 ((1 : A') ⊗ₜ[A] n)
      simpa using this
    · simpa only [LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply]
        using hs2
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨TensorProduct.AlgebraTensorModule.lift (A := A') (M := A') (N := M₀) (P := A')
      ({ toFun := fun a => a • g
         map_add' := fun a₁ a₂ => by simp [add_smul]
         map_smul' := fun a₁ a₂ => by simp [mul_smul] } : A' →ₗ[A'] (M₀ →ₗ[A] A')), ?_, ?_⟩
    · refine LinearMap.ext (fun z => ?_)
      refine TensorProduct.inductionOn z (fun a m => ?_) (fun z₁ z₂ h₁ h₂ => ?_)
      · rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.baseChange_tmul, lift_tmul]
        have h0 : g (d m) = 0 := by
          have := LinearMap.congr_fun hg1 m
          simpa using this
        rw [h0, smul_zero]
      · simp only [map_add, h₁, h₂, LinearMap.zero_apply, add_zero]
    · rw [lift_tmul, one_smul, hg2]

/-- **Functionals on a quotient.** An `A`-linear functional on `M` with values in an `A`-module
`N`, killing a submodule `p` and taking the value `y` at `e`, is the same thing as an `A`-linear
functional on `M ⧸ p` taking the value `y` at the class of `e` (the `Submodule.liftQ` /
`Submodule.mkQ` adjunction). -/
theorem quotient_dual_iff {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (p : Submodule A M) (e : M) (y : N) :
    (∃ f : M ⧸ p →ₗ[A] N, f (Submodule.mkQ p e) = y) ↔
      ∃ s : M →ₗ[A] N, p ≤ LinearMap.ker s ∧ s e = y := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.comp (Submodule.mkQ p), ?_, ?_⟩
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply]
      show f (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero p).mpr hx, map_zero]
    · simpa [Submodule.mkQ_apply] using hf
  · rintro ⟨s, hs, hse⟩
    refine ⟨p.liftQ s hs, ?_⟩
    simpa [Submodule.mkQ_apply] using hse

/-- Functionals on `M₀` killing `d` and taking the value `1` at `e` are functionals on
`M₀ ⧸ im d` taking the value `1` at the class of `e`. -/
theorem exists_dual_iff {M₁ M₀ : Type u} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₀] [Module A M₀] (d : M₁ →ₗ[A] M₀) (e : M₀) :
    (∃ g : M₀ →ₗ[A] A', g.comp d = 0 ∧ g e = 1) ↔
      ∃ τ : M₀ ⧸ LinearMap.range d →ₗ[A] A',
        τ (Submodule.mkQ (LinearMap.range d) e) = 1 := by
  rw [quotient_dual_iff (LinearMap.range d) e (1 : A')]
  refine exists_congr (fun s => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(LinearMap.range_le_ker_iff (f := d) (g := s)).mpr h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(LinearMap.range_le_ker_iff (f := d) (g := s)).mp h1, h2⟩

end ccAux

theorem chainSplit_ccBase_iff {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (P : CochainComplex (ModuleCat.{u} A) ℤ) (cc : Work.DSG4a.singleZ A ⟶ P) :
    Work.DSG4a.Criterion.ChainSplit (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P)
        (Work.DSG4a.ccBase P cc) ↔
      Module.IsUnimodular A' (TensorProduct.mk A A' (Work.DSG4a.Criterion.modelModule P) 1
        (Work.DSG4a.Criterion.modelElem P cc)) := by
  have hstep : Work.DSG4a.Criterion.ChainSplit (Work.DSG4a.baseChangeComplex (A := A) (A' := A') P)
        (Work.DSG4a.ccBase P cc) ↔
      ∃ s : ↥((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).X 0) →ₗ[A'] A',
        s.comp ((Work.DSG4a.baseChangeComplex (A := A) (A' := A') P).d (-1) 0).hom = 0 ∧
          s ((1 : A') ⊗ₜ[A, algebraMap A A'] (Work.DSG4a.Criterion.coaugElem P cc)) = 1 := by
    rw [Work.DSG4a.Criterion.ChainSplit, Work.DSG4a.coaugElem_ccBase]
    rfl
  rw [hstep]
  rw [chainSplit_condition_transfer P (Work.DSG4a.Criterion.coaugElem P cc)]
  rw [ccAux.exists_ext_linearMap_iff (A := A) (A' := A')
    (M₁ := ↥(P.X (-1))) (M₀ := ↥(P.X 0)) (P.d (-1) 0).hom
    (Work.DSG4a.Criterion.coaugElem P cc)]
  rw [ccAux.exists_dual_iff (A := A) (A' := A')
    (M₁ := ↥(P.X (-1))) (M₀ := ↥(P.X 0)) (P.d (-1) 0).hom
    (Work.DSG4a.Criterion.coaugElem P cc)]
  rw [TensorProduct.mk_apply]
  rw [Work.DSG4a.isUnimodular_tmul_iff (A := A) (A' := A')
    (M := Work.DSG4a.Criterion.modelModule P) (Work.DSG4a.Criterion.modelElem P cc)]
  rw [Work.DSG4a.Criterion.modelElem]

end Work.DSG4a.chainSplitBC
