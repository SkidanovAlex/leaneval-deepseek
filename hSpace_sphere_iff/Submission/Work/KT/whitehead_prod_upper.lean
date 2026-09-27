import Mathlib
import Submission.Work.KT.WhiteheadSetup

namespace Work.KT

open Matrix

/-- The product `∏_{i,j} (1 + E^{ij})` of the elementary matrices `E^{ij}` supported in the
top-right block of `Fin n ⊕ Fin n` (with entries `X i j`) equals the block matrix `[[1, X], [0, 1]]`.

This is Whitehead's lemma in its "upper" block form: the elementary matrices `E^{ij}` supported in
the top-right block pairwise multiply to zero (their "middle" indices `inr j` and `inl k` can never
agree), so the product of the `1 + E^{ij}` collapses to `1 + ∑_{i,j} E^{ij}`, and the sum of the
`E^{ij}` is exactly the top-right block `X`. -/
theorem whitehead_prod_upper {R : Type} [Ring R] {n : ℕ} (X : Matrix (Fin n) (Fin n) R) :
    ((Finset.univ : Finset (Fin n × Fin n)).toList.map
      (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
        + Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2))).prod
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) X 0 1 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  -- Two elementary matrices supported in the top-right block multiply to zero.
  have hmul : ∀ p q : Fin n × Fin n,
      (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
      (Matrix.single (Sum.inl q.1) (Sum.inr q.2) (X q.1 q.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) = 0 := by
    intro p q
    rw [Matrix.single_mul_single_of_ne]
    exact Sum.inr_ne_inl
  have hpair : ∀ a ∈ (Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)),
      ∀ b ∈ (Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)), a * b = 0 := by
    intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨p, _, rfl⟩ := ha
    obtain ⟨q, _, rfl⟩ := hb
    exact hmul p q
  -- The product of the `1 + E` collapses to `1 + ∑ E`.
  have hprod : ((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
          + Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2))).prod
      = 1 + ((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))).sum := by
    have h := Whitehead.list_prod_one_add_of_pairwise_mul_eq_zero hpair
    rw [List.map_map] at h
    simpa only [Function.comp_def] using h
  -- The sum of the elementary matrices is the top-right block.
  have hsum : ((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))).sum
      = Matrix.fromBlocks 0 X 0 0 := by
    rw [Whitehead.finset_sum_toList]
    exact Whitehead.sum_single_inl_inr_fromBlocks X
  rw [hprod, hsum]
  have h1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
      = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 1 := Matrix.fromBlocks_one.symm
  rw [h1, Matrix.fromBlocks_add]
  simp only [add_zero, zero_add]

end Work.KT
