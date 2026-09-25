/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation of the ramification filtration by a `K`-algebra isomorphism

Let `L/K` and `L₂/K` be field extensions, `A ⊆ L` and `A₂ ⊆ L₂` valuation subrings which are
matched by a `K`-algebra isomorphism `e : L ≃ₐ[K] L₂` (hypothesis `hA : ∀ x, x ∈ A ↔ e x ∈ A₂`),
and let `i : ℕ`.  Then conjugation by `e` is a group isomorphism
`A.decompositionSubgroup K ≃* A₂.decompositionSubgroup K` under which the `i`-th higher
ramification subgroup `G_i` of `A` corresponds to the `i`-th higher ramification subgroup of `A₂`.

This is the compatibility of the ramification filtration with isomorphisms of the ambient local
field, used whenever the filtration of a local field is transported across an identification of
that field with a standard model (e.g. a completion).
-/
import Mathlib
import Submission.NK.Ramification.Defs

open scoped Pointwise

namespace NK.Ramification

noncomputable section

variable {K L L₂ : Type*} [Field K] [Field L] [Algebra K L] [Field L₂] [Algebra K L₂]

/-! ## Conjugation of the Galois group -/

/-- Conjugation by a `K`-algebra isomorphism `e : L ≃ₐ[K] L₂`, viewed as a group isomorphism
between the automorphism groups of `L` and of `L₂` over `K`. -/
noncomputable def conjugationMulEquiv (e : L ≃ₐ[K] L₂) : (L ≃ₐ[K] L) ≃* (L₂ ≃ₐ[K] L₂) where
  toFun f := (e.symm.trans f).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' f g := by ext x; simp

theorem conjugationMulEquiv_eq (e : L ≃ₐ[K] L₂) (f : L ≃ₐ[K] L) (y : L₂) :
    conjugationMulEquiv e f y = e (f (e.symm y)) := by simp [conjugationMulEquiv]

theorem conjugationMulEquiv_apply_apply (e : L ≃ₐ[K] L₂) (f : L ≃ₐ[K] L) (x : L) :
    conjugationMulEquiv e f (e x) = e (f x) := by simp [conjugationMulEquiv]

/-! ## The decomposition subgroups -/

/-- Membership in the decomposition subgroup of `A` is the condition that `σ` preserves `A`. -/
theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ ∀ x : L, x ∈ A ↔ σ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  have hmem : ∀ x : L, (x ∈ σ • A) ↔ σ⁻¹ x ∈ A := by
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz, hz'⟩
      rw [← hz']
      simpa using hz
    · intro hx
      exact ⟨σ⁻¹ x, hx, by simp⟩
  constructor
  · intro h x
    have h1 : ∀ y : L, y ∈ A ↔ σ⁻¹ y ∈ A :=
      fun y => (by rw [h] : y ∈ A ↔ y ∈ σ • A).trans (hmem y)
    simpa using (h1 (σ x)).symm
  · intro h
    ext x
    rw [hmem x]
    simpa using h (σ⁻¹ x)

/-- Conjugation by `e` carries the decomposition subgroup of `A` onto the decomposition subgroup
of `A₂`. -/
theorem conjugationMulEquiv_mem_decompositionSubgroup_iff (A : ValuationSubring L)
    (A₂ : ValuationSubring L₂) (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂)
    (σ : L ≃ₐ[K] L) :
    conjugationMulEquiv e σ ∈ A₂.decompositionSubgroup K ↔ σ ∈ A.decompositionSubgroup K := by
  rw [mem_decompositionSubgroup_iff A₂ (conjugationMulEquiv e σ),
    mem_decompositionSubgroup_iff A σ]
  constructor
  · intro h x
    have h2 : e x ∈ A₂ ↔ conjugationMulEquiv e σ (e x) ∈ A₂ := h (e x)
    rw [conjugationMulEquiv_apply_apply] at h2
    exact (hA x).trans (h2.trans (hA (σ x)).symm)
  · intro h y
    have h1 : y ∈ A₂ ↔ e.symm y ∈ A := by simpa using (hA (e.symm y)).symm
    have h3 : σ (e.symm y) ∈ A ↔ e (σ (e.symm y)) ∈ A₂ := hA (σ (e.symm y))
    rw [conjugationMulEquiv_eq]
    exact (h1.trans (h (e.symm y))).trans h3

/-! ## The isomorphism of valuation rings induced by `e` -/

/-- The ring isomorphism `A ≃+* A₂` induced by `e` and `hA`. -/
noncomputable def ringEquivOfMap (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂) : A ≃+* A₂ where
  toFun x := ⟨e x, (hA x).mp x.2⟩
  invFun y := ⟨e.symm y, (hA (e.symm y)).mpr (by simpa using y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/-- A ring isomorphism carries the powers of the maximal ideal to the powers of the maximal
ideal. -/
theorem mem_maximalIdeal_pow_map (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (eA : A ≃+* A₂) (i : ℕ) (x : A) :
    x ∈ IsLocalRing.maximalIdeal A ^ i ↔ eA x ∈ IsLocalRing.maximalIdeal A₂ ^ i := by
  constructor
  · intro hx
    have h : eA x ∈ (IsLocalRing.maximalIdeal A ^ i).map (eA : A →+* A₂) :=
      Ideal.mem_map_of_mem _ hx
    have h2 : (IsLocalRing.maximalIdeal A ^ i).map (eA : A →+* A₂) =
        IsLocalRing.maximalIdeal A₂ ^ i := by
      rw [Ideal.map_pow]
      exact congrArg (· ^ i) (IsLocalRing.map_ringEquiv_maximalIdeal eA)
    rwa [h2] at h
  · intro hx
    have h : eA.symm (eA x) ∈ (IsLocalRing.maximalIdeal A₂ ^ i).map (eA.symm : A₂ →+* A) :=
      Ideal.mem_map_of_mem _ hx
    have h2 : (IsLocalRing.maximalIdeal A₂ ^ i).map (eA.symm : A₂ →+* A) =
        IsLocalRing.maximalIdeal A ^ i := by
      rw [Ideal.map_pow]
      exact congrArg (· ^ i) (IsLocalRing.map_ringEquiv_maximalIdeal eA.symm)
    rw [h2] at h
    simpa using h

/-! ## The isomorphism of decomposition subgroups -/

/-- Conjugation by `e` as an isomorphism of the decomposition subgroups of `A` and `A₂`. -/
noncomputable def decompMulEquiv (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂) :
    A.decompositionSubgroup K ≃* A₂.decompositionSubgroup K where
  toFun σ := ⟨conjugationMulEquiv e σ,
    (conjugationMulEquiv_mem_decompositionSubgroup_iff A A₂ e hA σ).mpr σ.2⟩
  invFun τ := ⟨(conjugationMulEquiv e).symm τ,
    (conjugationMulEquiv_mem_decompositionSubgroup_iff A A₂ e hA _).mp (by simpa using τ.2)⟩
  left_inv σ := Subtype.ext (by simp)
  right_inv τ := Subtype.ext (by simp)
  map_mul' σ τ := Subtype.ext (by simp)

/-- `decompMulEquiv` is conjugation by `e` on the underlying automorphisms. -/
theorem decompMulEquiv_coe (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂)
    (σ : A.decompositionSubgroup K) :
    ((decompMulEquiv A A₂ e hA σ : A₂.decompositionSubgroup K) : L₂ ≃ₐ[K] L₂) =
      conjugationMulEquiv e σ := rfl

/-- The isomorphism of decomposition subgroups is compatible with the ring isomorphism
`ringEquivOfMap A A₂ e hA` of valuation rings. -/
theorem decompMulEquiv_smul (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂)
    (σ : A.decompositionSubgroup K) (x : A) :
    (decompMulEquiv A A₂ e hA σ) • (ringEquivOfMap A A₂ e hA x) =
      ringEquivOfMap A A₂ e hA (σ • x) := by
  apply Subtype.ext
  show (conjugationMulEquiv e (σ : L ≃ₐ[K] L)) (e (x : L)) = e (((σ • x : A)) : L)
  rw [conjugationMulEquiv_apply_apply]
  rfl

/-! ## The main statement -/

theorem ramificationSubgroup_map_conj {K L L₂ : Type*} [Field K] [Field L] [Algebra K L]
    [Field L₂] [Algebra K L₂] (A : ValuationSubring L) (A₂ : ValuationSubring L₂)
    (e : L ≃ₐ[K] L₂) (hA : ∀ x : L, x ∈ A ↔ e x ∈ A₂) (i : ℕ) :
    ∃ φ : A.decompositionSubgroup K ≃* A₂.decompositionSubgroup K,
      ∀ σ : A.decompositionSubgroup K,
        (σ ∈ NK.Ramification.ramificationSubgroup (K := K) A i ↔
          φ σ ∈ NK.Ramification.ramificationSubgroup (K := K) A₂ i) := by
  refine ⟨decompMulEquiv A A₂ e hA, fun σ => ?_⟩
  rw [mem_ramificationSubgroup_iff, mem_ramificationSubgroup_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := (ringEquivOfMap A A₂ e hA).surjective y
    rw [decompMulEquiv_smul A A₂ e hA σ x, ← map_sub]
    exact (mem_maximalIdeal_pow_map A A₂ (ringEquivOfMap A A₂ e hA) (i + 1)
      (σ • x - x)).mp (h x)
  · intro h x
    have hx : (decompMulEquiv A A₂ e hA σ) • (ringEquivOfMap A A₂ e hA x) -
        (ringEquivOfMap A A₂ e hA x) ∈ IsLocalRing.maximalIdeal A₂ ^ (i + 1) :=
      h (ringEquivOfMap A A₂ e hA x)
    rw [decompMulEquiv_smul A A₂ e hA σ x, ← map_sub] at hx
    exact (mem_maximalIdeal_pow_map A A₂ (ringEquivOfMap A A₂ e hA) (i + 1)
      (σ • x - x)).mpr hx

end

end NK.Ramification
