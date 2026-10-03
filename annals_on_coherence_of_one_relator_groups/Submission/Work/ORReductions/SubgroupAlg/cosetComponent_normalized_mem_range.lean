import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

namespace Work.ORReductions.SubgroupAlg

/-- If the support of `y : K[G]` is contained in the subgroup `H`, then `y` lies in the range of
the canonical inclusion `K[H] →+* K[G]`. -/
theorem mem_range_subgroupAlgMap_of_support_subset {G : Type*} [Group G] (H : Subgroup G)
    (K : Type*) [Semiring K] (y : MonoidAlgebra K G) (h : ↑y.coeff.support ⊆ (H : Set G)) :
    y ∈ Set.range (Work.ORReductions.subgroupAlgMap H K) := by
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.subtypeDomain (fun g => g ∈ H) y.coeff), ?_⟩
  rw [show (Work.ORReductions.subgroupAlgMap H K)
        (MonoidAlgebra.ofCoeff (Finsupp.subtypeDomain (fun g => g ∈ H) y.coeff))
      = MonoidAlgebra.ofCoeff (Finsupp.mapDomain (⇑H.subtype)
          (Finsupp.subtypeDomain (fun g => g ∈ H) y.coeff)) from rfl]
  apply MonoidAlgebra.ext
  rw [MonoidAlgebra.coeff_ofCoeff, MonoidAlgebra.coeff_ofCoeff]
  ext g
  by_cases hg : g ∈ H
  · change (Finsupp.mapDomain (⇑H.subtype)
        (Finsupp.subtypeDomain (fun g => g ∈ H) y.coeff)) (⇑H.subtype ⟨g, hg⟩) = y.coeff g
    rw [Finsupp.mapDomain_apply_of_injective H.subtype_injective]
    exact Finsupp.subtypeDomain_apply
  · rw [Finsupp.mapDomain_of_notMem_range]
    · exact (Finsupp.notMem_support_iff.mp (fun hmem => hg (h hmem))).symm
    · rintro ⟨g', hg'⟩
      exact hg (hg' ▸ g'.2)

/-- The left coset of `H` containing `Quotient.out q * g` equals `q` exactly when `g ∈ H`. -/
theorem quotientMk_out_mul_eq_iff {G : Type*} [Group G] (H : Subgroup G) (q : G ⧸ H) (g : G) :
    (Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q * g) : G ⧸ H) = q ↔ g ∈ H := by
  have key : (Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q * g) : G ⧸ H)
      = (Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q) : G ⧸ H) ↔ g ∈ H := by
    rw [QuotientGroup.eq]
    rw [show (Quotient.out q * g)⁻¹ * Quotient.out q = g⁻¹ by group]
    exact Subgroup.inv_mem_iff H
  rwa [Quotient.out_eq q] at key

/-- Normalizing the `q`-coset component of `x : K[G]` by the inverse of a representative of `q`
kills all coefficients outside `H`. -/
theorem coeff_single_inv_mul_cosetComponent_eq_zero {G : Type*} [Group G] (H : Subgroup G)
    (K : Type*) [Semiring K] (q : G ⧸ H) (x : MonoidAlgebra K G) (g : G) (hg : g ∉ H) :
    (MonoidAlgebra.single (Quotient.out q)⁻¹ 1 *
        Work.ORReductions.cosetComponent H K q x).coeff g = 0 := by
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul, inv_inv]
  show (Work.ORReductions.cosetComponent H K q x).coeff (Quotient.out q * g) = 0
  rw [Work.ORReductions.cosetComponent, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]
  rw [if_neg]
  intro hp
  exact hg ((quotientMk_out_mul_eq_iff H q g).mp hp)

theorem cosetComponent_normalized_mem_range {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (q : G ⧸ H) (x : MonoidAlgebra K G) :
    MonoidAlgebra.single (Quotient.out q)⁻¹ 1 * Work.ORReductions.cosetComponent H K q x ∈
      Set.range (Work.ORReductions.subgroupAlgMap H K) := by
  apply mem_range_subgroupAlgMap_of_support_subset
  intro g hmem
  by_contra hgH
  exact (Finsupp.mem_support_iff.mp hmem)
    (coeff_single_inv_mul_cosetComponent_eq_zero H K q x g hgH)

end Work.ORReductions.SubgroupAlg
