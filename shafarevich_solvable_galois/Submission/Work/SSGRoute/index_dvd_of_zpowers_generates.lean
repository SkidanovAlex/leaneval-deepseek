import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If every element of `K` lies in a coset `σ ^ m * H` of the subgroup `H`, and `σ ^ n = 1`,
then the index of `H` divides `n`.

This is the "cyclic coset count" step: the coset space `K ⧸ H` is in bijection with the
quotient `⟨σ⟩ ⧸ (⟨σ⟩ ⊓ H)`, and the index of `⟨σ⟩ ⊓ H` inside the cyclic group `⟨σ⟩`
divides its order, which divides `n` by `orderOf_dvd_iff_pow_eq_one`. -/
theorem index_dvd_of_zpowers_generates {K : Type*} [Group K] (H : Subgroup K) (σ : K) (n : ℕ)
    (hgen : ∀ δ : K, ∃ m : ℤ, δ⁻¹ * σ ^ m ∈ H) (hn : σ ^ n = 1) : H.index ∣ n := by
  have hidx : H.index = H.relIndex (Subgroup.zpowers σ) := by
    set A : Subgroup K := Subgroup.zpowers σ
    let S : Subgroup A := H.subgroupOf A
    -- The inclusion `A ↪ K` induces a well-defined map on the quotients by `A ⊓ H` and `H`.
    let f : A ⧸ S → K ⧸ H :=
      Quotient.map' (fun a : A => (a : K)) (by
        intro a b hab
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        have h : ((a⁻¹ * b : A) : K) ∈ H := Subgroup.mem_subgroupOf.mp hab
        simpa using h)
    -- Injectivity: two elements of `A` which are congruent mod `H` are congruent mod `A ⊓ H`.
    have hf_inj : Function.Injective f := by
      intro x y
      refine Quotient.inductionOn' x (fun a => ?_)
      refine Quotient.inductionOn' y (fun b => ?_)
      intro hxy
      simp only [f, Quotient.map'_mk''] at hxy ⊢
      rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hxy ⊢
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hxy)
    -- Surjectivity: every coset of `H` is of the form `σ ^ m * H`.
    have hf_surj : Function.Surjective f := by
      intro x
      refine Quotient.inductionOn' x (fun δ => ?_)
      obtain ⟨m, hm⟩ := hgen δ
      refine ⟨Quotient.mk'' (⟨σ ^ m, Subgroup.zpow_mem_zpowers σ m⟩ : A), ?_⟩
      simp only [f, Quotient.map'_mk'']
      rw [Quotient.eq'', QuotientGroup.leftRel_apply]
      have h : (δ⁻¹ * σ ^ m)⁻¹ ∈ H := inv_mem hm
      simpa using h
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  rw [hidx]
  -- `H.relIndex ⟨σ⟩` divides `Nat.card ⟨σ⟩ = orderOf σ`, which divides `n`.
  refine dvd_trans (Subgroup.index_dvd_card (H.subgroupOf (Subgroup.zpowers σ))) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_iff_pow_eq_one.mpr hn

end Work.SSGRoute
