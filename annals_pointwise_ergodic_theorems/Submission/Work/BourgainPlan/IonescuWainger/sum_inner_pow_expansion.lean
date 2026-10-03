import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Expansion of the `r`-th power of the inner product of a sum with itself as a sum over
`r`-tuples of pairs of indices. -/
theorem sum_inner_pow_expansion {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : ℕ) (u : ι → E) :
    (inner ℂ (∑ i, u i) (∑ i, u i)) ^ r
      = ∑ q : Fin r → ι × ι, ∏ k : Fin r, inner ℂ (u (q k).1) (u (q k).2) := by
  have hbase : inner ℂ (∑ i, u i) (∑ i, u i) = ∑ p : ι × ι, inner ℂ (u p.1) (u p.2) := by
    rw [sum_inner]
    simp only [inner_sum]
    exact (Fintype.sum_prod_type (γ := ℂ) (fun p : ι × ι => inner ℂ (u p.1) (u p.2))).symm
  rw [hbase, Fintype.sum_pow]

end Work.BourgainPlan.IonescuWainger
