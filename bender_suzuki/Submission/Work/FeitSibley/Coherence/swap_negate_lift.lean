import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end


namespace Work.FeitSibley.Coherence

open Classical

/-- **Swap-negate a coherent lift on a two-element set.**

Let `S = {x₁, x₂}` be an orthonormal set of two functions on `H = ↥h.H`, of the same non-zero
degree `x₁ 1 = x₂ 1 ≠ 0`, and let `τ` be an integral linear map which agrees with `Ind_H^G` on
`ℤ[S]^0`, is an isometry on the whole lattice `ℤ[S]`, and takes virtual-character values on `S`.

Then there is a lift `τ'` with the same three properties whose values on the two elements of `S`
are *swapped and negated*: `τ' x₁ = -τ x₂`, `τ' x₂ = -τ x₁`.

The construction is that of `Work.Coherence.isometryOnAll_extend` for the "signed swap"
`φ x₁ := -τ x₂`, `φ x₂ := -τ x₁`.  The hypotheses of that lemma are verified using only that
`S` is orthonormal of constant non-zero degree: `φ` differs from `τ` on `S` by the constant
`φ x₁ - τ x₁ = -τ x₁ - τ x₂` (the shift condition, which is just commutativity), and reproduces
the inner products against the base point `x₁` because `-τ x₂` and `-τ x₁` are orthonormal with
the same Gram matrix as `x₂` and `x₁`. -/
theorem swap_negate_lift {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {S : Finset (↥h.H → ℂ)} {τ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Work.Coherence.Orthonormal S)
    (hτ0 : ∀ α ∈ Work.Coherence.ZSpan0 S, τ α = Work.FeitSibley.indLin h.H α)
    (hτiso : Work.Coherence.IsometryOnAll S τ)
    (hτV : ∀ χ ∈ S, Work.Coherence.IsVChar (τ χ))
    {x₁ x₂ : ↥h.H → ℂ} (h1 : x₁ ∈ S) (h2 : x₂ ∈ S) (hne : x₁ ≠ x₂)
    (hcover : ∀ χ ∈ S, χ = x₁ ∨ χ = x₂) (hdeg : x₁ 1 = x₂ 1) (hdeg0 : x₁ 1 ≠ 0) :
    ∃ τ' : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ),
      (∀ α ∈ Work.Coherence.ZSpan0 S, τ' α = Work.FeitSibley.indLin h.H α) ∧
      Work.Coherence.IsometryOnAll S τ' ∧
      (∀ χ ∈ S, Work.Coherence.IsVChar (τ' χ)) ∧
      τ' x₁ = -τ x₂ ∧ τ' x₂ = -τ x₁ := by
  classical
  -- `τ` restricts to an isometry on the degree-zero part `ℤ[S]^0`.
  have hτ : Work.Coherence.IsometryOn S τ :=
    ⟨fun α hα β hβ =>
      hτiso.inner_eq α (Work.Coherence.zSpan0_le_zSpan S hα)
        β (Work.Coherence.zSpan0_le_zSpan S hβ)⟩
  -- Every element of `S` has the degree of `x₁` (there are only `x₁` and `x₂`).
  have hdegS : ∀ x ∈ S, x 1 = x₁ 1 := by
    intro x hx
    rcases hcover x hx with hxx | hxx
    · rw [hxx]
    · rw [hxx, hdeg]
  -- The signed swap on `S`: `φ x₁ = -τ x₂`, `φ x₂ = -τ x₁`.
  let φ : (↥h.H → ℂ) → (G → ℂ) := fun x => -τ (x₁ + x₂ - x)
  have hφ1 : φ x₁ = -τ x₂ := by
    simp only [φ]
    rw [show x₁ + x₂ - x₁ = x₂ by abel]
  have hφ2 : φ x₂ = -τ x₁ := by
    simp only [φ]
    rw [show x₁ + x₂ - x₂ = x₁ by abel]
  -- `φ` differs from `τ` on `S` by the constant `φ x₁ - τ x₁`.
  have hφshift : ∀ x ∈ S, φ x - τ x = φ x₁ - τ x₁ := by
    intro x hx
    rcases hcover x hx with hxx | hxx
    · rw [hxx]
    · rw [hxx, hφ2, hφ1]
      abel
  -- `φ` reproduces the inner products of the base point `x₁` against `S`.
  have hφorth : ∀ x ∈ S,
      Work.Coherence.cfInner (φ x₁) (φ x) = Work.Coherence.cfInner x₁ x := by
    intro x hx
    rcases hcover x hx with hxx | hxx
    · rw [hxx, hφ1, Work.Coherence.cfInner_neg_left, Work.Coherence.cfInner_neg_right,
        neg_neg,
        hτiso.inner_eq x₂ (Work.Coherence.self_mem_zSpan h2)
          x₂ (Work.Coherence.self_mem_zSpan h2),
        hS.cfInner_self h2, hS.cfInner_self h1]
    · rw [hxx, hφ1, hφ2, Work.Coherence.cfInner_neg_left, Work.Coherence.cfInner_neg_right,
        neg_neg,
        hτiso.inner_eq x₂ (Work.Coherence.self_mem_zSpan h2)
          x₁ (Work.Coherence.self_mem_zSpan h1),
        hS.cfInner_eq_zero h2 h1 (Ne.symm hne), hS.cfInner_eq_zero h1 h2 hne]
  -- Extend to an isometry of the whole lattice taking the prescribed values on `S`.
  obtain ⟨τ', hτ'0, hτ'iso, hτ'S⟩ :=
    Work.Coherence.isometryOnAll_extend hS h1 hdegS hdeg0 hτ hφorth hφshift
  refine ⟨τ', fun α hα => ?_, hτ'iso, fun χ hχ => ?_, ?_, ?_⟩
  · -- agreement with `Ind_H^G` on `ℤ[S]^0`
    rw [hτ'0 α hα, hτ0 α hα]
  · -- virtual-character values on `S`
    rw [hτ'S χ hχ]
    rcases hcover χ hχ with hχχ | hχχ
    · rw [hχχ, hφ1]; exact (hτV x₂ h2).neg
    · rw [hχχ, hφ2]; exact (hτV x₁ h1).neg
  · -- `τ' x₁ = -τ x₂`
    rw [hτ'S x₁ h1, hφ1]
  · -- `τ' x₂ = -τ x₁`
    rw [hτ'S x₂ h2, hφ2]

end Work.FeitSibley.Coherence
