import Mathlib
import Submission.NK.WeakNU.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.WeakNU

/-- **Fixed-point counts detect conjugacy into a subgroup.**

Let `H₁, H₂ ≤ G` be subgroups of a finite group `G`, and suppose that for every `σ : G` the number
of fixed points of `σ` acting on the left-coset space `G ⧸ H₁` equals the number of fixed points of
`σ` acting on `G ⧸ H₂`.  Then every element of `H₁` is conjugate into `H₂`.

Indeed, `σ` fixes the coset `gH` of `G ⧸ H` exactly when `g⁻¹ * σ * g ∈ H`, so if `x ∈ H₁`, the
element `x⁻¹` fixes the coset `1 * H₁` of `G ⧸ H₁`; by hypothesis `x⁻¹` fixes some coset `q` of
`G ⧸ H₂`, i.e. `q.out⁻¹ * x * q.out ∈ H₂`, which is the required conjugate of `x`. -/
theorem exists_conj_mem_of_fixedCount_coset_eq {G : Type*} [Group G] [Fintype G] (H₁ H₂ : Subgroup G) (h : ∀ σ : G, NK.WeakNU.fixedCount σ (G ⧸ H₁) = NK.WeakNU.fixedCount σ (G ⧸ H₂)) : ∀ x ∈ H₁, ∃ γ : G, γ * x * γ⁻¹ ∈ H₂ := by
  intro x hx
  -- `x⁻¹` fixes the coset of `1` in `G ⧸ H₁`, since `x⁻¹ ∈ H₁`.
  have hpos : 0 < fixedCount x⁻¹ (G ⧸ H₁) := by
    rw [fixedCount]
    rw [Nat.card_pos_iff]
    refine ⟨⟨⟨QuotientGroup.mk (1 : G), ?_⟩⟩, inferInstance⟩
    rw [MulAction.Quotient.smul_mk]
    rw [QuotientGroup.eq]
    simpa using hx
  -- Hence `x⁻¹` fixes some coset of `G ⧸ H₂`.
  have hpos2 : 0 < fixedCount x⁻¹ (G ⧸ H₂) := by
    rw [← h x⁻¹]; exact hpos
  obtain ⟨⟨q, hq⟩, -⟩ := Nat.card_pos_iff.mp hpos2
  refine ⟨q.out⁻¹, ?_⟩
  have h1 : QuotientGroup.mk (x⁻¹ * q.out) = (QuotientGroup.mk q.out : G ⧸ H₂) := by
    have hh := hq
    rw [← QuotientGroup.out_eq' q, MulAction.Quotient.smul_mk] at hh
    exact hh
  have hm : q.out⁻¹ * x * q.out ∈ H₂ := by
    have h2 := QuotientGroup.eq.mp h1
    simpa [mul_inv_rev, mul_assoc, inv_inv] using h2
  simpa using hm

end NK.WeakNU
