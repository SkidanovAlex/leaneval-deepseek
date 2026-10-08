import Mathlib
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.orthonormal_phi
import Submission.Work.Coherence.cfInner_span_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Extending an isometry on `ℤ[S]^0` to an isometry on the whole lattice `ℤ[S]`

Let `S` be an orthonormal finite set of class functions on a finite group `H`, all of the same
degree `x 1 = x₀ 1` with `x₀ 1 ≠ 0`, and let `τ : ℤ[H → ℂ] → ℤ[G → ℂ]` be an integral linear
map which is an isometry on the degree-zero part `ℤ[S]^0` of the lattice it spans.  Given a map
`φ` which on `S` equals `τ` up to a *constant* shift and which reproduces the inner products of
the base point `x₀` (`⟨φ x₀, φ x⟩ = ⟨x₀, x⟩`), `orthonormal_phi` shows that `φ` is orthonormal
on `S`.  Then

`τ' α = τ α + (α 1 / x₀ 1) • (φ x₀ - τ x₀)`

is an integral linear map which agrees with `φ` on `S`, with `τ` on `ℤ[S]^0`, and which is an
isometry on the whole lattice `ℤ[S]` (both `S` and `φ '' S` are orthonormal with the same
"identity" Gram matrix, so the two double sums over the integral coordinates coincide).

This is the extension step in Feit–Thompson's coherence theorem (Definition 10.1): a
`φ`-compatible extension of the Dade isometry on `ℤ[S]^0` exists.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

section ExtensionMap

variable {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]

/-- The `ℤ`-linear functional `α ↦ α 1 / x₀ 1`, i.e. the degree of `α` normalised by the degree
of the base point `x₀`.  On `ℤ[S]`, when every element of `S` has degree `x₀ 1 ≠ 0`, it is the
coordinate of `α` along `x₀` in the decomposition `ℤ[S] = ℤ[S]^0 ⊕ ℤ x₀`. -/
def degScalar (x₀ : H → ℂ) : (H → ℂ) →ₗ[ℤ] ℂ where
  toFun α := (x₀ 1)⁻¹ * α 1
  map_add' α β := by simp [Pi.add_apply, mul_add]
  map_smul' n α := by
    show (x₀ 1)⁻¹ * (n • α) 1 = n • ((x₀ 1)⁻¹ * α 1)
    simp only [Pi.smul_apply, zsmul_eq_mul]
    ring

/-- The candidate extension of `τ`: `α ↦ τ α + (α 1 / x₀ 1) • (φ x₀ - τ x₀)`. -/
def extendMap (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) (x₀ : H → ℂ) (φ : (H → ℂ) → (G → ℂ)) :
    (H → ℂ) →ₗ[ℤ] (G → ℂ) :=
  τ + (degScalar x₀).smulRight (φ x₀ - τ x₀)

theorem extendMap_apply (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) (x₀ : H → ℂ) (φ : (H → ℂ) → (G → ℂ))
    (α : H → ℂ) :
    extendMap τ x₀ φ α = τ α + ((x₀ 1)⁻¹ * α 1) • (φ x₀ - τ x₀) := rfl

/-- `extendMap` does not change elements of degree zero. -/
theorem extendMap_apply_of_deg_zero (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) (x₀ : H → ℂ)
    (φ : (H → ℂ) → (G → ℂ)) {α : H → ℂ} (h : α 1 = 0) :
    extendMap τ x₀ φ α = τ α := by
  rw [extendMap_apply, h, mul_zero, zero_smul, add_zero]

/-- `extendMap` agrees with `φ` on a set `S` all of whose elements have degree `x₀ 1`, provided
`φ` differs from `τ` on `S` by the constant `φ x₀ - τ x₀`. -/
theorem extendMap_apply_of_mem (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) {S : Finset (H → ℂ)}
    {x₀ : H → ℂ} (hdeg : ∀ x ∈ S, x 1 = x₀ 1) (hd : x₀ 1 ≠ 0)
    {φ : (H → ℂ) → (G → ℂ)} (hφshift : ∀ x ∈ S, φ x - τ x = φ x₀ - τ x₀) :
    ∀ x ∈ S, extendMap τ x₀ φ x = φ x := by
  intro x hx
  rw [extendMap_apply, hdeg x hx, inv_mul_cancel₀ hd, one_smul, ← hφshift x hx]
  abel

/-- The value of an integral linear map on an integral combination of the elements of `S`, given
its values on `S`. -/
theorem map_sum_smul_mem {S : Finset (H → ℂ)} {τ' : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    {φ : (H → ℂ) → (G → ℂ)} (hφ : ∀ x ∈ S, τ' x = φ x) (c : ↥S → ℤ) :
    τ' (∑ x : ↥S, (c x : ℂ) • (x : H → ℂ)) = ∑ x : ↥S, (c x : ℂ) • φ (x : H → ℂ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Int.cast_smul_eq_zsmul, map_zsmul, hφ _ x.2, Int.cast_smul_eq_zsmul]

end ExtensionMap

theorem isometryOnAll_extend {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Orthonormal S) {x₀ : H → ℂ} (hx₀ : x₀ ∈ S) (hdeg : ∀ x ∈ S, x 1 = x₀ 1)
    (hd : x₀ 1 ≠ 0) (hτ : IsometryOn S τ) {φ : (H → ℂ) → (G → ℂ)}
    (hφorth : ∀ x ∈ S, cfInner (φ x₀) (φ x) = cfInner x₀ x)
    (hφshift : ∀ x ∈ S, φ x - τ x = φ x₀ - τ x₀) :
    ∃ τ' : (H → ℂ) →ₗ[ℤ] (G → ℂ),
      (∀ α ∈ ZSpan0 S, τ' α = τ α) ∧ IsometryOnAll S τ' ∧ ∀ x ∈ S, τ' x = φ x := by
  classical
  refine ⟨extendMap τ x₀ φ, ?_, ?_, extendMap_apply_of_mem τ hdeg hd hφshift⟩
  · intro α hα
    exact extendMap_apply_of_deg_zero τ x₀ φ hα.2
  · -- both `S` and `φ ∘ S` are orthonormal, with the same (identity) Gram matrix, so the
    -- extension preserves the inner product on `ℤ[S]`
    have hφmem : ∀ x ∈ S, extendMap τ x₀ φ x = φ x := extendMap_apply_of_mem τ hdeg hd hφshift
    have hdiagφ : ∀ x : ↥S, cfInner (φ (x : H → ℂ)) (φ (x : H → ℂ)) = 1 := by
      intro x
      rw [orthonormal_phi hS hx₀ hdeg hτ hφorth hφshift _ x.2 _ x.2]
      simp
    have hoffφ : ∀ x y : ↥S, x ≠ y → cfInner (φ (x : H → ℂ)) (φ (y : H → ℂ)) = 0 := by
      intro x y hxy
      rw [orthonormal_phi hS hx₀ hdeg hτ hφorth hφshift _ x.2 _ y.2]
      have hxy' : ¬ ((x : H → ℂ) = (y : H → ℂ)) := fun h => hxy (Subtype.ext h)
      simp [hxy']
    have hdiagS : ∀ x : ↥S, cfInner ((x : H → ℂ)) ((x : H → ℂ)) = 1 := by
      intro x; rw [hS _ x.2 _ x.2]; simp
    have hoffS : ∀ x y : ↥S, x ≠ y → cfInner ((x : H → ℂ)) ((y : H → ℂ)) = 0 := by
      intro x y hxy
      rw [hS _ x.2 _ y.2]
      have hxy' : ¬ ((x : H → ℂ) = (y : H → ℂ)) := fun h => hxy (Subtype.ext h)
      simp [hxy']
    refine ⟨fun α hα β hβ => ?_⟩
    obtain ⟨c, rfl⟩ := mem_zSpan.mp hα
    obtain ⟨d, rfl⟩ := mem_zSpan.mp hβ
    rw [map_sum_smul_mem hφmem c, map_sum_smul_mem hφmem d,
      cfInner_span_eq c d (fun x : ↥S => φ (x : H → ℂ)) (fun x : ↥S => φ (x : H → ℂ))
        hdiagφ hoffφ,
      ← cfInner_span_eq c d (fun x : ↥S => (x : H → ℂ)) (fun x : ↥S => (x : H → ℂ))
        hdiagS hoffS]

end Work.Coherence
