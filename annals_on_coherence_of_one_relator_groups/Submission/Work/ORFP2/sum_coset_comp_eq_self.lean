import Mathlib
import Submission.Work.ORFP2.CosetProj

namespace Work.ORFP2

open MonoidAlgebra

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- Coefficient of an element of `k[H]`, regarded as an element of `k[G]` via `transferHom`,
at a group element `g ∈ H`. -/
lemma transferHom_coeff_of_mem (H : Subgroup G) (b : MonoidAlgebra k H) (g : G)
    (hg : g ∈ H) : (transferHom k H b).coeff g = b.coeff ⟨g, hg⟩ := by
  rw [transferHom, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_apply_of_injective (fun a b h => Subtype.ext h) b.coeff ⟨g, hg⟩

/-- The coefficient of `transferHom b` at a group element `g ∉ H` vanishes. -/
lemma transferHom_coeff_of_notMem (H : Subgroup G) (b : MonoidAlgebra k H) (g : G)
    (hg : g ∉ H) : (transferHom k H b).coeff g = 0 := by
  rw [transferHom, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
  refine Finsupp.mapDomain_of_notMem_range b.coeff g ?_
  rintro ⟨h, rfl⟩
  exact hg h.2

/-- Two group elements lie in the same left coset `q` of `H` iff the corresponding quotient
classes agree; explicitly `q = gH` records as `(Quotient.out q)⁻¹ * g ∈ H`. -/
lemma mk_eq_out_inv_mul_mem (H : Subgroup G) (q : G ⧸ H) (g : G) :
    (QuotientGroup.mk g = q) ↔ (Quotient.out q)⁻¹ * g ∈ H := by
  rw [← Quotient.out_eq q, QuotientGroup.eq]
  constructor
  · intro h
    have h' := H.inv_mem h
    simpa using h'
  · intro h
    have h' := H.inv_mem h
    simpa using h'

/-- The coefficient at `g` of `single (out q) 1 * z` is the coefficient of `z` at
`(out q)⁻¹ * g`. -/
lemma coeff_single_out_mul_transferHom (H : Subgroup G) (q : G ⧸ H) (b : MonoidAlgebra k H)
    (g : G) :
    (MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H b).coeff g
      = (transferHom k H b).coeff ((Quotient.out q)⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]

/-- The `q`-th summand has coefficient `x.coeff g` at a point `g` of the coset `q`. -/
lemma coeff_coset_term_of_eq (H : Subgroup G) (x : MonoidAlgebra k G) (q : G ⧸ H) (g : G)
    (hq : QuotientGroup.mk g = q) :
    (MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H (comp k H q x)).coeff g
      = x.coeff g := by
  rw [coeff_single_out_mul_transferHom]
  have hy : (Quotient.out q)⁻¹ * g ∈ H := (mk_eq_out_inv_mul_mem H q g).mp hq
  rw [transferHom_coeff_of_mem k H _ _ hy, comp_coeff k H q x ⟨(Quotient.out q)⁻¹ * g, hy⟩]
  congr 1
  group

/-- The `q`-th summand has coefficient `0` at any point `g` outside the coset `q`. -/
lemma coeff_coset_term_of_ne (H : Subgroup G) (x : MonoidAlgebra k G) (q : G ⧸ H) (g : G)
    (hq : QuotientGroup.mk g ≠ q) :
    (MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H (comp k H q x)).coeff g
      = 0 := by
  rw [coeff_single_out_mul_transferHom]
  exact transferHom_coeff_of_notMem k H _ _ (fun h => hq ((mk_eq_out_inv_mul_mem H q g).mpr h))

/-- **The coset decomposition of `k[G]` over `k[H]`.**  Writing `x` coset by coset with
respect to the subgroup `H ≤ G`, the component of `x` on a left coset `q` is
`single (out q) 1 * transferHom (comp q x)`, and summing these over the cosets meeting the
support of `x` recovers `x`. -/
theorem sum_coset_comp_eq_self (k : Type*) [CommRing k] {G : Type*} [Group G] (H : Subgroup G)
    (x : MonoidAlgebra k G) :
    ∑ q ∈ cosetSupport k H x,
        MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H (comp k H q x) = x := by
  classical
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (QuotientGroup.mk g)]
  · exact coeff_coset_term_of_eq k H x (QuotientGroup.mk g) g rfl
  · intro q _ hqne
    exact coeff_coset_term_of_ne k H x q g (Ne.symm hqne)
  · intro hg
    have hgs : g ∉ x.coeff.support :=
      fun hgs => hg ((mem_cosetSupport k).mpr ⟨g, hgs, rfl⟩)
    rw [coeff_coset_term_of_eq k H x (QuotientGroup.mk g) g rfl]
    exact (Finsupp.notMem_support_iff (f := x.coeff) (a := g)).mp hgs

end Work.ORFP2
