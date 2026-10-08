import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Internal
import Submission.Work.PGroup.Omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

/-- Pulling back along Baer's construction: let `P ≤ U` and `X ≤ U` be subgroups of `Γ`, `U`
normalising `Q` (so `↥U` acts on `↥Q` by conjugation).  Suppose `e : ↥Q ≃ G` intertwines this action
with an action of `↥U` on the group `G` and preserves `orderOf`.  If `g : G` has order `p`, is fixed
by (the image of) `P` and is not fixed by some element of (the image of) `X`, then `e⁻¹ g` is an
element of `Q` of order `p` which commutes with every element of `P` (hence lies in
`Ω₁(Q ⊓ C_Γ(P))`) and does not commute with some element of `X`. -/
theorem exists_not_commute_of_baer {Γ : Type*} [Group Γ] {Q X P U : Subgroup Γ}
    [FT.Normalizes U Q] {p : ℕ} {G : Type*} [Group G] [MulDistribMulAction U G]
    (hPU : P ≤ U) (hXU : X ≤ U)
    (e : Q ≃ G) (he : ∀ q : Q, orderOf (e q) = orderOf q)
    (heq : ∀ (a : U) (q : Q), e (a • q) = a • e q)
    (g : G) (hord : orderOf g = p)
    (hPfix : ∀ q : P, Subgroup.inclusion hPU q • g = g)
    (hXne : ∃ x : X, Subgroup.inclusion hXU x • g ≠ g) :
    ∃ q ∈ Work.PGroup.omega1 Γ p (Q ⊓ Subgroup.centralizer (P : Set Γ)),
      ∃ x ∈ X, x * q ≠ q * x := by
  -- The witness is the pull-back of `g` along Baer's isomorphism `e`.
  refine ⟨(e.symm g : Q), ?_, ?_⟩
  · -- `e⁻¹ g ∈ Ω₁(Q ⊓ C_Γ(P))`: it has order `p` and commutes with `P`.
    refine Work.PGroup.omega1_subset p ?hQ ?hpow
    · -- commutation with `P`
      refine Subgroup.mem_inf.mpr ⟨(e.symm g).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      -- `a ∈ P` fixes `g`, hence (intertwining) fixes `e⁻¹ g` under conjugation
      have hfix : Subgroup.inclusion hPU ⟨a, ha⟩ • g = g := hPfix ⟨a, ha⟩
      have key : Subgroup.inclusion hPU ⟨a, ha⟩ • (e.symm g) = e.symm g := by
        apply e.injective
        rw [heq, Equiv.apply_symm_apply]
        exact hfix
      have hcoe := congrArg (Subtype.val) key
      simp only [FT.conj_smul_coe, Subgroup.coe_inclusion] at hcoe
      calc a * ↑(e.symm g) = a * ↑(e.symm g) * a⁻¹ * a := by group
        _ = ↑(e.symm g) * a := by rw [hcoe]
    · -- order `p`
      have hord_q : orderOf (e.symm g) = p := by
        rw [← he (e.symm g), Equiv.apply_symm_apply, hord]
      have hq_pow : (e.symm g : Q) ^ p = 1 := by
        rw [← hord_q]; exact pow_orderOf_eq_one _
      have hpow : ((e.symm g : Q) : Γ) ^ p = 1 := by
        rw [← Subgroup.coe_pow]
        exact congrArg (Subtype.val) hq_pow
      exact hpow
  · -- the element of `X` witnessing non-fixation of `g` also fails to commute with `e⁻¹ g`
    obtain ⟨x, hx⟩ := hXne
    refine ⟨x, x.2, ?_⟩
    intro hcomm
    apply hx
    have key : Subgroup.inclusion hXU x • (e.symm g) = e.symm g := by
      apply Subtype.ext
      simp only [FT.conj_smul_coe, Subgroup.coe_inclusion]
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : e (Subgroup.inclusion hXU x • (e.symm g)) = e (e.symm g) := congrArg e key
    rw [heq, Equiv.apply_symm_apply] at h1
    exact h1

end Work.ThreePoints.ThmC
