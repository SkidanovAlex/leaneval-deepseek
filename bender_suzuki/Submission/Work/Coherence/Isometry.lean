import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The basic API of isometries of character lattices

`IsometryOn S τ` (preservation of the character inner product on `ℤ[S]^0`) and
`IsometryOnAll S τ` (preservation on all of `ℤ[S]`), together with the elementary manipulations:
restriction to a sub-lattice, the identity, and composition of isometries.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

variable {H G K : Type*}

section API

variable [Group H] [Fintype H] [Group G] [Fintype G]

/-- An isometry on all of `ℤ[S]` is in particular an isometry on `ℤ[S]^0`. -/
theorem isometryOnAll_toIsometryOn {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : IsometryOnAll S τ) : IsometryOn S τ :=
  ⟨fun α hα β hβ => h.inner_eq α (zSpan0_le_zSpan S hα) β (zSpan0_le_zSpan S hβ)⟩

/-- An isometry preserves norms of elements of the lattice. -/
theorem IsometryOnAll.inner_self {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : IsometryOnAll S τ) {α : H → ℂ} (hα : α ∈ ZSpan S) :
    cfInner (τ α) (τ α) = cfInner α α := h.inner_eq α hα α hα

/-- **Gram-matrix criterion.**  A `ℤ`-linear map `τ` preserves the inner product on `ℤ[S]` as soon
as it preserves it on the Gram matrix of the spanning set `S`.  No orthonormality is needed: expand
both arguments in the coefficients of the lattice and use bilinearity. -/
theorem isometryOnAll_of_gram {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : ∀ x ∈ S, ∀ y ∈ S, cfInner (τ x) (τ y) = cfInner x y) : IsometryOnAll S τ := by
  have key : ∀ (n : ℤ) (f : H → ℂ), τ ((n : ℂ) • f) = (n : ℂ) • τ f := by
    intro n f
    simp only [Int.cast_smul_eq_zsmul, map_zsmul]
  refine ⟨fun α hα β hβ => ?_⟩
  obtain ⟨c, hc⟩ := mem_zSpan.mp hα
  obtain ⟨d, hd⟩ := mem_zSpan.mp hβ
  rw [hc, hd, map_sum, map_sum]
  simp only [key]
  rw [cfInner_sum_smul, cfInner_sum_smul]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [h x x.2 y y.2]

/-- `τ` preserves the inner product on `ℤ[S]` if and only if it preserves the Gram matrix of
`S`. -/
theorem isometryOnAll_iff_gram {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)} :
    IsometryOnAll S τ ↔ ∀ x ∈ S, ∀ y ∈ S, cfInner (τ x) (τ y) = cfInner x y :=
  ⟨fun h x hx y hy => h.inner_eq x (self_mem_zSpan hx) y (self_mem_zSpan hy),
   isometryOnAll_of_gram⟩

/-- The identity is an isometry. -/
theorem isometryOnAll_id (S : Finset (G → ℂ)) :
    IsometryOnAll S (LinearMap.id : (G → ℂ) →ₗ[ℤ] (G → ℂ)) :=
  ⟨fun _ _ _ _ => rfl⟩

theorem IsometryOnAll.mono {S T : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : IsometryOnAll S τ) (hTS : T ⊆ S) : IsometryOnAll T τ :=
  ⟨fun α hα β hβ => h.inner_eq α (zSpan_mono hTS hα) β (zSpan_mono hTS hβ)⟩

theorem IsometryOn.mono {S T : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : IsometryOn S τ) (hTS : T ⊆ S) : IsometryOn T τ :=
  ⟨fun α hα β hβ => h.inner_eq α (zSpan0_mono hTS hα) β (zSpan0_mono hTS hβ)⟩

end API

section Comp

variable [Group H] [Fintype H] [Group G] [Fintype G] [Group K] [Fintype K]

/-- A composition of isometries on lattices is an isometry. -/
theorem IsometryOnAll.comp {S : Finset (H → ℂ)} {T : Finset (G → ℂ)}
    {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)} {σ : (G → ℂ) →ₗ[ℤ] (K → ℂ)}
    (hσ : IsometryOnAll T σ) (hτ : IsometryOnAll S τ)
    (hmaps : ∀ α ∈ ZSpan S, τ α ∈ ZSpan T) : IsometryOnAll S (σ.comp τ) :=
  ⟨fun α hα β hβ => by
    simp only [LinearMap.comp_apply]
    rw [hσ.inner_eq (τ α) (hmaps α hα) (τ β) (hmaps β hβ), hτ.inner_eq α hα β hβ]⟩

end Comp

end Work.Coherence
