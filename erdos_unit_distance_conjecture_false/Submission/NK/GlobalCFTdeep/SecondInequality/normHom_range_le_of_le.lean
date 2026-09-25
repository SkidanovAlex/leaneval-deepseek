import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0

namespace NK.GlobalCFTdeep.SecondInequality

open scoped BigOperators

set_option linter.style.haveILetI false

open NK.GlobalCFTdeep

/-- The range of the norm for `G` is contained in the range of the norm for any subgroup `H ≤ G`:
`N_G x = ∏_{g : G} g • x` factors over a right transversal `T` of `H` as
`∏_{t : ↥T} N_H (t • x)`. -/
theorem normHom_range_le_of_le {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (H : Subgroup G) [Fintype ↥H] :
    (NK.GlobalCFTdeep.normHom G M).range ≤ (NK.GlobalCFTdeep.normHom H M).range := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := QuotientGroup.fintypeQuotientRightRel
  rintro y ⟨x, rfl⟩
  refine ⟨∏ c : Quotient (QuotientGroup.rightRel H), c.out • x, ?_⟩
  -- The right transversal: for each right coset `c` of `H`, the element `c.out` is a
  -- representative, and every `g` lies in the coset `H * c.out`; hence the map
  -- `(c, h) ↦ h * c.out` is a bijection `(G ⧸ H) × ↥H → G`.
  let ψ : Quotient (QuotientGroup.rightRel H) × ↥H → G := fun p => (p.2 : G) * p.1.out
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ heq
      simp only [ψ] at heq
      have hrel : QuotientGroup.rightRel H c₁.out c₂.out := by
        rw [QuotientGroup.rightRel_apply]
        have h2 : c₂.out * c₁.out⁻¹ = (h₂ : G)⁻¹ * (h₁ : G) := by
          have h3 : c₂.out = (h₂ : G)⁻¹ * ((h₁ : G) * c₁.out) := by rw [heq]; group
          rw [h3]; group
        rw [h2]
        exact H.mul_mem (H.inv_mem h₂.2) h₁.2
      have hc : c₁ = c₂ := by
        calc c₁ = Quotient.mk'' c₁.out := (Quotient.out_eq' c₁).symm
          _ = Quotient.mk'' c₂.out := Quotient.sound' hrel
          _ = c₂ := Quotient.out_eq' c₂
      have hh : h₁ = h₂ := by
        have h := heq
        rw [hc] at h
        exact Subtype.ext (mul_right_cancel h)
      rw [hc, hh]
    · intro g
      set c : Quotient (QuotientGroup.rightRel H) := Quotient.mk'' g with hc
      have hrel : QuotientGroup.rightRel H c.out g := by
        apply Quotient.exact'
        rw [Quotient.out_eq', hc]
      rw [QuotientGroup.rightRel_apply] at hrel
      refine ⟨(c, ⟨g * c.out⁻¹, hrel⟩), ?_⟩
      simp only [ψ]
      group
  -- Reindex the defining product of `N_G` along `ψ`, split the product over the product
  -- type, and recognise each inner product as the `H`-norm of `c.out • x`.
  have key : (∏ p : Quotient (QuotientGroup.rightRel H) × ↥H, ψ p • x) =
      normHom G M x := by
    rw [normHom_apply]
    exact Fintype.prod_bijective ψ hψ (fun p => ψ p • x) (fun g => g • x) (fun p => rfl)
  have key2 : normHom H M (∏ c : Quotient (QuotientGroup.rightRel H), c.out • x) =
      ∏ p : Quotient (QuotientGroup.rightRel H) × ↥H, ψ p • x := by
    rw [map_prod, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [normHom_apply]
    refine Finset.prod_congr rfl (fun h _ => ?_)
    simp only [ψ]
    rw [mul_smul]
    rfl
  rw [key2, key]

end NK.GlobalCFTdeep.SecondInequality
