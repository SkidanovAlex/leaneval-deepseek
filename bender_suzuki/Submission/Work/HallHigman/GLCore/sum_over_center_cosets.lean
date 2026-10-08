import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- Coset decomposition of a sum over a finite group modulo its centre: with `Quotient.out` a
section of `E → E ⧸ Z(E)`, every function `F` on `E` satisfies
`Σ_e F e = Σ_{q : E ⧸ Z(E)} Σ_{z ∈ Z(E)} F (out q * z)`. -/
theorem sum_over_center_cosets {M : Type*} [AddCommMonoid M] {E : Type*} [Group E] [Fintype E]
    [Fintype ↥(Subgroup.center E)] [Fintype (E ⧸ Subgroup.center E)] (F : E → M) :
    ∑ e : E, F e
      = ∑ q : E ⧸ Subgroup.center E, ∑ z : Subgroup.center E, F (Quotient.out q * (z : E)) := by
  classical
  rw [← Fintype.sum_prod_type (fun p : (E ⧸ Subgroup.center E) × Subgroup.center E =>
        F (Quotient.out p.1 * (p.2 : E)))]
  refine (Fintype.sum_bijective
    (fun p : (E ⧸ Subgroup.center E) × Subgroup.center E =>
      Quotient.out p.1 * (p.2 : E))
    ?_ (fun p => F (Quotient.out p.1 * (p.2 : E))) F (fun _ => rfl)).symm
  -- the map `(q, z) ↦ out q * z` is a bijection `(E ⧸ Z) × Z ≃ E`
  have key : ∀ (q : E ⧸ Subgroup.center E) (z : Subgroup.center E),
      ((Quotient.out q * (z : E) : E) : E ⧸ Subgroup.center E) = q := by
    intro q z
    rw [QuotientGroup.mk_mul]
    have hz : (((z : E)) : E ⧸ Subgroup.center E) = 1 := by
      rw [QuotientGroup.eq_one_iff]; exact z.2
    rw [hz, mul_one, QuotientGroup.out_eq']
  refine ⟨?_, ?_⟩
  · rintro ⟨q, z⟩ ⟨q', z'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((Quotient.out q * (z : E) : E) : E ⧸ Subgroup.center E)
          = ((Quotient.out q' * (z' : E) : E) : E ⧸ Subgroup.center E) := by rw [h]
      rw [key q z, key q' z'] at h1
      exact h1
    subst hq
    have hz : (z : E) = (z' : E) := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext hz)
  · intro e
    refine ⟨(QuotientGroup.mk e, ⟨(Quotient.out (QuotientGroup.mk e))⁻¹ * e,
        QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk e))⟩), ?_⟩
    exact mul_inv_cancel_left _ _

end Work.HallHigman.GLCore
