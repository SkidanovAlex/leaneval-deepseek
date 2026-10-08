import Mathlib
import Submission.Work.Clifford.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- For a normal subgroup `N ≤ G`, left multiplication by an element of `N` does not change the
class in `G ⧸ N`: `mk (n * g) = mk g` for `n ∈ N`. -/
private theorem mk_mul_mem_left {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] {n : G}
    (hn : n ∈ N) (g : G) :
    QuotientGroup.mk (s := N) (n * g) = QuotientGroup.mk (s := N) g := by
  rw [QuotientGroup.eq]
  have h : (n * g)⁻¹ * g = g⁻¹ * n⁻¹ * g := by group
  rw [h]
  exact hN.conj_mem' (n⁻¹) (N.inv_mem hn) g

theorem sum_G_eq_sum_quotient_mul {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] [Fintype (G ⧸ N)] (F : G → ℂ) :
    ∑ g : G, F g = ∑ x : G ⧸ N, ∑ n : N, F ((n : G) * Quotient.out x) := by
  classical
  -- The map `(x, n) ↦ n * out x` is a bijection `(G ⧸ N) × N ≃ G`: it enumerates each coset
  -- `x` exactly once, through the section `Quotient.out`.
  have hbij : Function.Bijective
      (fun p : (G ⧸ N) × N => (p.2 : G) * Quotient.out p.1) := by
    constructor
    · rintro ⟨x1, n1⟩ ⟨x2, n2⟩ h
      change (n1 : G) * Quotient.out x1 = (n2 : G) * Quotient.out x2 at h
      have hx : x1 = x2 := by
        have hmk : QuotientGroup.mk (s := N) ((n1 : G) * Quotient.out x1) =
            QuotientGroup.mk (s := N) ((n2 : G) * Quotient.out x2) := by rw [h]
        rw [mk_mul_mem_left n1.2, mk_mul_mem_left n2.2, QuotientGroup.out_eq',
          QuotientGroup.out_eq'] at hmk
        exact hmk
      have hnn : n1 = n2 := by
        apply Subtype.ext
        rw [← hx] at h
        have hn := congrArg (fun t : G => t * (Quotient.out x1)⁻¹) h
        simpa using hn
      exact Prod.ext hx hnn
    · intro g
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
      refine ⟨(QuotientGroup.mk g, ⟨g * (h : G)⁻¹ * g⁻¹, ?_⟩), ?_⟩
      · exact (inferInstance : N.Normal).conj_mem (h⁻¹) (N.inv_mem h.2) g
      · show (g * (h : G)⁻¹ * g⁻¹) * Quotient.out (QuotientGroup.mk (s := N) g) = g
        rw [hh]
        group
  have key : (∑ p : (G ⧸ N) × N, F ((p.2 : G) * Quotient.out p.1)) = ∑ g : G, F g :=
    Fintype.sum_bijective (fun p : (G ⧸ N) × N => (p.2 : G) * Quotient.out p.1) hbij
      (fun p => F ((p.2 : G) * Quotient.out p.1)) F (fun p => rfl)
  rw [Fintype.sum_prod_type] at key
  exact key.symm

end Work.Clifford
