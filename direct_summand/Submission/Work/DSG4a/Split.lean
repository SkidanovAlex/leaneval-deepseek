import Mathlib

/-!
# DSG4a: the splitting ideal of an element of a module

This file is the abstract algebra layer of subproject **DSG4a** (area `G4a`, the
local-to-global step for the derived direct summand theorem).  The point of the area is
that the derived splitting condition `DSplit A X f` is, once a finite free model of
`RΓ(X, 𝒪)` is available, *equivalent* to the purely algebraic statement that a certain
element of a finitely presented module is **unimodular** (Mathlib's `Module.IsUnimodular`),
and that this condition is local on `Spec A`.  This file sets up the algebraic notion and
its basic API; the flat base-change theorem is in `Submission.Work.DSG4a.Flat` and the
local-to-global theorem in `Submission.Work.DSG4a.LocalGlobal`.

## Conventions

* `splitIdeal A e` is the ideal of all `σ e`, `σ : M →ₗ[A] A` (the "trace ideal" of `e`).
  The ring `A` is an *explicit* argument, because for the base change `A' ⊗[A] M` the
  module carries two module structures and the ring has to be pinned down.
* `Module.IsUnimodular A e` (Mathlib) means `∃ σ : M →ₗ[A] A, σ e = 1`; we prove it is
  equivalent to `splitIdeal A e = ⊤`.
* Base change is along an `A`-algebra `A'`, and we use the tensor product `A' ⊗[A] M`
  (Mathlib's `LinearMap.baseChange` conventions); the base-changed element is `1 ⊗ₜ[A] e`.
-/

namespace Work.DSG4a

open TensorProduct

universe u v v' w

section Abstract

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- The **splitting ideal** of `e : M`: the ideal of all values `σ e` at `e` of `A`-linear
functionals `σ : M →ₗ[A] A`.  Its being the unit ideal is equivalent to `M` splitting at
`e` (`Module.IsUnimodular A e`). -/
abbrev splitIdeal (A : Type u) [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (e : M) : Ideal A := LinearMap.range (LinearMap.applyₗ (M₂ := A) e)

lemma mem_splitIdeal {e : M} {x : A} : x ∈ splitIdeal A e ↔ ∃ σ : M →ₗ[A] A, σ e = x := by
  rw [splitIdeal, LinearMap.mem_range]
  simp only [LinearMap.applyₗ_apply_apply]

lemma one_mem_splitIdeal_iff {e : M} : (1 : A) ∈ splitIdeal A e ↔ Module.IsUnimodular A e := by
  rw [mem_splitIdeal, Module.isUnimodular_iff]

lemma splitIdeal_eq_top_iff {e : M} : splitIdeal A e = ⊤ ↔ Module.IsUnimodular A e :=
  (Ideal.eq_top_iff_one _).trans one_mem_splitIdeal_iff

lemma isUnimodular_iff_splitIdeal_eq_top {e : M} : Module.IsUnimodular A e ↔ splitIdeal A e = ⊤ :=
  splitIdeal_eq_top_iff.symm

lemma splitIdeal_le_iff {e : M} {I : Ideal A} : splitIdeal A e ≤ I ↔ ∀ σ : M →ₗ[A] A, σ e ∈ I := by
  constructor
  · intro h σ
    exact h (mem_splitIdeal.mpr ⟨σ, rfl⟩)
  · intro h
    rintro x ⟨σ, rfl⟩
    exact h σ

variable {M' : Type v'} [AddCommGroup M'] [Module A M']

/-- Pulling back along a linear map only shrinks the splitting ideal. -/
lemma splitIdeal_le_splitIdeal_apply (f : M →ₗ[A] M') (e : M) :
    splitIdeal A (f e) ≤ splitIdeal A e := by
  rintro x ⟨σ, rfl⟩
  exact mem_splitIdeal.mpr ⟨σ ∘ₗ f, rfl⟩

lemma isUnimodular_of_isUnimodular_apply (f : M →ₗ[A] M') {e : M}
    (h : Module.IsUnimodular A (f e)) : Module.IsUnimodular A e := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ ∘ₗ f, hσ⟩

/-- The splitting ideal is invariant under linear isomorphisms. -/
lemma splitIdeal_linearEquiv (F : M ≃ₗ[A] M') (e : M) :
    splitIdeal A (F e) = splitIdeal A e := by
  refine le_antisymm (splitIdeal_le_splitIdeal_apply F.toLinearMap e) ?_
  have h := splitIdeal_le_splitIdeal_apply (A := A) (M := M') (M' := M) F.symm.toLinearMap (F e)
  simpa using h

lemma isUnimodular_apply_iff (F : M ≃ₗ[A] M') (e : M) :
    Module.IsUnimodular A (F e) ↔ Module.IsUnimodular A e := by
  rw [isUnimodular_iff_splitIdeal_eq_top, isUnimodular_iff_splitIdeal_eq_top,
    splitIdeal_linearEquiv]

end Abstract

/-! ## Base change

For an `A`-algebra `A'` and `e : M`, the base change of `e` is `1 ⊗ₜ[A] e` in the `A'`-module
`A' ⊗[A] M`.  The easy direction of the base-change theory — a splitting over `A` gives one
over `A'` — is proved here; the converse, for finitely presented `M` and flat `A'`, is
`one_mem_map_splitIdeal_of_isUnimodular_tmul` (module
`Submission.Work.DSG4a.one_mem_map_splitIdeal_of_isUnimodular_tmul`). -/

section BaseChange

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
variable {A' : Type w} [CommRing A'] [Algebra A A']

/-- The `A'`-linear functional on `A' ⊗[A] M` induced by an `A`-linear functional on `M`. -/
noncomputable def baseChangeDual (A' : Type w) [CommRing A'] [Algebra A A']
    (σ : M →ₗ[A] A) : (A' ⊗[A] M) →ₗ[A'] A' :=
  (AlgebraTensorModule.rid A A' A').toLinearMap ∘ₗ σ.baseChange A'

lemma baseChangeDual_tmul (σ : M →ₗ[A] A) (a : A') (m : M) :
    baseChangeDual A' σ (a ⊗ₜ[A] m) = a * algebraMap A A' (σ m) := by
  show AlgebraTensorModule.rid A A' A' ((LinearMap.baseChange A' σ) (a ⊗ₜ[A] m)) = _
  rw [LinearMap.baseChange_tmul, AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

/-- **Base change of the splitting ideal**, easy direction. -/
lemma splitIdeal_map_le_splitIdeal_tmul (e : M) :
    (splitIdeal A e).map (algebraMap A A') ≤ splitIdeal A' ((1 : A') ⊗ₜ[A] e) := by
  rw [Ideal.map, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨σ, rfl⟩ := mem_splitIdeal.mp hy
  refine mem_splitIdeal.mpr ⟨baseChangeDual A' σ, ?_⟩
  simpa using baseChangeDual_tmul (A' := A') σ (1 : A') e

/-- A splitting over `A` base changes to a splitting over any `A`-algebra `A'`. -/
lemma isUnimodular_tmul (e : M) (h : Module.IsUnimodular A e) :
    Module.IsUnimodular A' ((1 : A') ⊗ₜ[A] e) := by
  rw [← one_mem_splitIdeal_iff] at h ⊢
  refine splitIdeal_map_le_splitIdeal_tmul (A' := A') e ?_
  simpa using Ideal.mem_map_of_mem (algebraMap A A') h

end BaseChange

end Work.DSG4a
