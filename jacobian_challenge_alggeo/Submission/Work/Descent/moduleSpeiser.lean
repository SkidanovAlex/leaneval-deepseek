/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Speiser's lemma for modules (Galois descent for `k'`-modules)

For a finite Galois extension `k'/k` with Galois group `Γ = Gal k k'` and a `k'`-module `V`
equipped with a semilinear action of `Γ`, the comparison map

`V^Γ ⊗_k k' → V,  v ⊗ c ↦ c • v`

is bijective.  This is *Speiser's lemma* (the module/vector-space form of Galois descent); the
algebra form is `Work.Descent.SemilinearAction.speiserHomK` in `Submission/Work/Descent/Basic.lean`.

## Proof

The input from linear algebra is

* `exists_coeffs_left` : for every `σ₀ : Γ` there are `l : Γ → k'` with
  `∑ τ, l τ * σ (galoisBasis k k' τ) = if σ = σ₀ then 1 else 0` (`speiserCoeffs_delta`), and
* `exists_coeffs_right` : for every `τ₀ : Γ` there are `m : Γ → k'` with
  `∑ σ, m σ * σ (galoisBasis k k' τ) = if τ = τ₀ then 1 else 0`.

*Surjectivity*: for `v : V` the element `∑ τ, (∑ σ, σ (l τ) • A.act σ v) ⊗ c τ` (with `l` the
coefficients for `σ₀ = 1`, see `speiserWitness`) is fixed in the first variable
(`speiserActSum_mem_fixed`) and maps to `∑ σ, (∑ τ, c τ * σ (l τ)) • A.act σ v = A.act 1 v = v`.

*Injectivity*: using the `k`-basis `(c τ)` of `k'`, every `t : V^Γ ⊗_k k'` is of the shape
`∑ τ, w τ ⊗ c τ` with `w τ ∈ V^Γ` (`TensorProduct.equivFinsuppOfBasisRight`).  If `t` maps to
`0`, then `∑ τ, c τ • w τ = 0`, and applying `A.act σ` (which fixes each `w τ`) gives
`∑ τ, σ (c τ) • w τ = 0` for every `σ`, whence `w τ₀ = ∑ σ, m σ • (∑ τ, σ (c τ) • w τ) = 0` using
the right dual coefficients.
-/
import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.GaloisBasis
import Submission.Work.Descent.exists_coeffs_left
import Submission.Work.Descent.exists_coeffs_right
import Submission.Work.Descent.dedekind_module
import Submission.Work.Descent.exists_trace_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open scoped Classical

/-! ## Dual coefficients for the Galois basis -/

section Coeffs

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [IsGalois k k']

/-- Dual coefficients to the `k`-basis `galoisBasis k k'` of `k'` indexed by the Galois group, on
the `σ₀ = 1` side: `∑ τ, speiserCoeffs τ * σ (galoisBasis k k' τ)` is `1` for `σ = 1` and `0`
otherwise. -/
noncomputable def speiserCoeffs (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] : Gal k k' → k' :=
  (exists_coeffs_left (galoisBasis k k') 1).choose

lemma speiserCoeffs_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] :
    (∑ τ, speiserCoeffs k k' τ * galoisBasis k k' τ = 1) ∧
      ∀ σ : Gal k k', σ ≠ 1 →
        ∑ τ, speiserCoeffs k k' τ * σ (galoisBasis k k' τ) = 0 := by
  have h := (exists_coeffs_left (galoisBasis k k') 1).choose_spec
  exact ⟨by simpa [speiserCoeffs] using h.1,
    by intro σ hσ; simpa [speiserCoeffs] using h.2 σ hσ⟩

/-- The `δ`-form of the defining property of `speiserCoeffs`. -/
lemma speiserCoeffs_delta (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (ρ : Gal k k') :
    ∑ τ, speiserCoeffs k k' τ * ρ (galoisBasis k k' τ) = if ρ = 1 then 1 else 0 := by
  by_cases h : ρ = 1
  · subst h; simpa using (speiserCoeffs_spec k k').1
  · simpa [h] using (speiserCoeffs_spec k k').2 ρ h

/-- The dual coefficients, paired with the basis element on the left: this is the identity used in
the surjectivity computation.  It is obtained from `speiserCoeffs_delta` by applying `σ⁻¹` and
commuting the product in `k'`. -/
lemma speiserCoeff_basis_mul (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (σ : Gal k k') :
    ∑ τ, galoisBasis k k' τ * σ (speiserCoeffs k k' τ) = if σ = 1 then 1 else 0 := by
  have key : σ (∑ τ, speiserCoeffs k k' τ * σ⁻¹ (galoisBasis k k' τ))
      = ∑ τ, σ (speiserCoeffs k k' τ) * galoisBasis k k' τ := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul]
    simp
  have key2 : ∑ τ, σ (speiserCoeffs k k' τ) * galoisBasis k k' τ
      = ∑ τ, galoisBasis k k' τ * σ (speiserCoeffs k k' τ) :=
    Finset.sum_congr rfl fun τ _ => mul_comm _ _
  rw [← key2, ← key, speiserCoeffs_delta k k' σ⁻¹]
  by_cases h : σ = 1
  · simp [h]
  · have h' : σ⁻¹ ≠ 1 := fun hc => h (inv_eq_one.mp hc)
    simp [h, h']

/-- Dual coefficients on the `τ₀` side: for every `τ₀` there are `m : Γ → k'` with
`∑ σ, m σ * σ (galoisBasis k k' τ) = if τ = τ₀ then 1 else 0`. -/
lemma exists_coeffs_right_delta (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (τ₀ : Gal k k') : ∃ m : Gal k k' → k',
    ∀ τ : Gal k k', ∑ σ, m σ * σ (galoisBasis k k' τ) = if τ = τ₀ then 1 else 0 := by
  obtain ⟨m, hm1, hm0⟩ := exists_coeffs_right (galoisBasis k k') τ₀
  refine ⟨m, fun τ => ?_⟩
  by_cases h : τ = τ₀
  · subst h; simpa using hm1
  · simpa [h] using hm0 τ h

end Coeffs

/-! ## The module-theoretic Speiser lemma -/

section ModuleSpeiser

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [IsGalois k k']
  {V : Type u} [AddCommGroup V] [Module k' V] [Module k V] [IsScalarTower k k' V]

/-- The auxiliary `k`-linear map `v ↦ ∑ σ, σ a • A.act σ v`.  Its values are fixed by the action
(`speiserActSum_mem_fixed`), and it is the basic building block of the section of the Speiser
comparison map. -/
noncomputable def speiserActSum (A : SemilinearActionModule k k' V) (a : k') : V →ₗ[k] V where
  toFun v := ∑ σ : Gal k k', σ a • A.act σ v
  map_add' v w := by
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm]

omit [IsGalois k k'] in
@[simp] lemma speiserActSum_apply (A : SemilinearActionModule k k' V) (a : k') (v : V) :
    speiserActSum A a v = ∑ σ : Gal k k', σ a • A.act σ v := rfl

omit [IsGalois k k'] in
/-- `∑ σ, σ a • A.act σ v` is fixed by the Galois action: this is a change of variable in the
Galois group, using semilinearity of the action. -/
lemma speiserActSum_mem_fixed (A : SemilinearActionModule k k' V) (a : k') (v : V) :
    speiserActSum A a v ∈ A.fixed := by
  intro ρ
  rw [speiserActSum_apply, map_sum]
  have h : (∑ σ : Gal k k', A.act ρ (σ a • A.act σ v)) =
      ∑ σ : Gal k k', (ρ * σ) a • A.act (ρ * σ) v := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [A.act_smul, AlgEquiv.mul_apply]
    congr 1
    rw [map_mul, LinearEquiv.mul_apply]
  rw [h]
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun ν : Gal k k' => ν a • A.act ν v)

/-- An explicit preimage of `v` under the Speiser comparison map, using the dual coefficients
`speiserCoeffs` for `σ₀ = 1`. -/
noncomputable def speiserWitness (A : SemilinearActionModule k k' V) (v : V) :
    A.fixed ⊗[k] k' :=
  ∑ τ : Gal k k', (⟨speiserActSum A (speiserCoeffs k k' τ) v,
      speiserActSum_mem_fixed A (speiserCoeffs k k' τ) v⟩ : A.fixed) ⊗ₜ[k] galoisBasis k k' τ

/-- The Speiser comparison map is surjective. -/
theorem speiserMapK_surjective (A : SemilinearActionModule k k' V) :
    Function.Surjective A.speiserMapK := by
  intro v
  refine ⟨speiserWitness A v, ?_⟩
  simp only [speiserWitness, map_sum, SemilinearActionModule.speiserMapK_tmul,
    speiserActSum_apply]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  have h1 : (∑ σ : Gal k k', ∑ τ : Gal k k',
        galoisBasis k k' τ • (σ (speiserCoeffs k k' τ) • A.act σ v))
      = ∑ σ : Gal k k', (∑ τ : Gal k k',
          galoisBasis k k' τ * σ (speiserCoeffs k k' τ)) • A.act σ v := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => smul_smul _ _ _
  rw [h1]
  simp only [speiserCoeff_basis_mul k k', ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, SemilinearActionModule.act_one]
  simp

/-- The Speiser comparison map is injective. -/
theorem speiserMapK_injective (A : SemilinearActionModule k k' V) :
    Function.Injective A.speiserMapK := by
  intro t t' h
  have hx : A.speiserMapK (t - t') = 0 := by rw [map_sub, h, sub_self]
  have key : t - t' = 0 := by
    let F : Gal k k' →₀ A.fixed :=
      TensorProduct.equivFinsuppOfBasisRight (galoisBasis k k') (t - t')
    have hexp : t - t' = ∑ τ : Gal k k', (F τ) ⊗ₜ[k] galoisBasis k k' τ := by
      rw [show t - t' = (TensorProduct.equivFinsuppOfBasisRight (galoisBasis k k')).symm F from
        (LinearEquiv.symm_apply_apply _ (t - t')).symm]
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
        Finsupp.sum_fintype F (fun τ m => m ⊗ₜ[k] galoisBasis k k' τ) (by intro i; simp)]
    have hw : ∑ τ : Gal k k', galoisBasis k k' τ • (F τ : V) = 0 := by
      have h1 : A.speiserMapK (t - t')
          = ∑ τ : Gal k k', galoisBasis k k' τ • (F τ : V) := by
        rw [hexp, map_sum]
        simp only [SemilinearActionModule.speiserMapK_tmul]
      exact h1.symm.trans hx
    have hsigma : ∀ σ : Gal k k',
        ∑ τ : Gal k k', σ (galoisBasis k k' τ) • (F τ : V) = 0 := by
      intro σ
      have h3 := congrArg (A.act σ) hw
      simp only [map_sum, map_zero] at h3
      rw [← h3]
      exact Finset.sum_congr rfl fun τ _ => by rw [A.act_smul, (F τ).2]
    have hFzero : F = 0 := by
      ext τ₀
      obtain ⟨m, hm⟩ := exists_coeffs_right_delta k k' τ₀
      have hdelta : (∑ τ : Gal k k',
            (if τ = τ₀ then (1 : k') else 0) • (F τ : V)) = (F τ₀ : V) := by
        have step : (∑ τ : Gal k k', (if τ = τ₀ then (1 : k') else 0) • (F τ : V))
            = ∑ τ : Gal k k', (if τ = τ₀ then (F τ : V) else 0) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [ite_smul, one_smul, zero_smul]
        rw [step, Finset.sum_ite_eq' Finset.univ τ₀ (fun τ => (F τ : V))]
        simp
      have hmeq : (∑ τ : Gal k k',
            (∑ σ : Gal k k', m σ * σ (galoisBasis k k' τ)) • (F τ : V))
          = ∑ τ : Gal k k', (if τ = τ₀ then (1 : k') else 0) • (F τ : V) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [hm τ]
      have hA : (∑ τ : Gal k k',
            (∑ σ : Gal k k', m σ * σ (galoisBasis k k' τ)) • (F τ : V)) = 0 := by
        have hstep : (∑ τ : Gal k k',
              (∑ σ : Gal k k', m σ * σ (galoisBasis k k' τ)) • (F τ : V))
            = ∑ τ : Gal k k', ∑ σ : Gal k k',
                (m σ * σ (galoisBasis k k' τ)) • (F τ : V) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Finset.sum_smul]
        rw [hstep, Finset.sum_comm]
        refine Finset.sum_eq_zero fun σ _ => ?_
        trans m σ • ∑ τ : Gal k k', σ (galoisBasis k k' τ) • (F τ : V)
        · rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun τ _ => (smul_smul _ _ _).symm
        · rw [hsigma σ, smul_zero]
      have hzero : (F τ₀ : V) = 0 := by
        rw [← hdelta, ← hmeq, hA]
      simpa using hzero
    rw [hexp, hFzero]
    simp
  exact sub_eq_zero.mp key

end ModuleSpeiser

/-- Speiser's descent result for modules: for a `k'`-module `V` with a semilinear action of the
Galois group of a finite Galois extension `k'/k`, the comparison map `V^Γ ⊗_k k' → V`,
`v ⊗ c ↦ c • v`, is bijective. -/
theorem moduleSpeiser {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsGalois k k'] {V : Type u} [AddCommGroup V] [Module k' V] [Module k V]
    [IsScalarTower k k' V] (A : SemilinearActionModule k k' V) :
    Function.Bijective A.speiserMapK :=
  ⟨speiserMapK_injective A, speiserMapK_surjective A⟩

end Work.Descent
