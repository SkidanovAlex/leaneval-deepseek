import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace Commons.Analysis.InnerProduct

/-- **Weak convergence implies norm convergence in finite dimensions.**  If for
every vector `v` the scalar functions `t ↦ ⟪f t, v⟫` tend to `0` along a filter
`l`, then `f` itself tends to `0` along `l`.

Proof: fix an orthonormal basis `B` of the finite-dimensional real inner
product space `E`.  Expanding `f t = ∑ i, ⟪f t, B i⟫ • B i`, each coefficient
tends to `0` by hypothesis, hence each summand `⟪f t, B i⟫ • B i` tends to `0`,
and a finite sum of null sequences is null. -/
theorem tendsto_zero_of_forall_inner_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {f : α → E}
    (h : ∀ v : E, Filter.Tendsto (fun t : α => inner ℝ (f t) v) l (nhds 0)) :
    Filter.Tendsto f l (nhds 0) := by
  let B := stdOrthonormalBasis ℝ E
  have hrepr : f = fun t : α => ∑ i, inner ℝ (f t) (B i) • B i := by
    funext t
    have h1 : ∑ i, ⟪B i, f t⟫_ℝ • B i = f t := OrthonormalBasis.sum_repr' B (f t)
    have h2 : ∑ i, ⟪B i, f t⟫_ℝ • B i = ∑ i, inner ℝ (f t) (B i) • B i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_comm]
    rw [h2] at h1
    exact h1.symm
  rw [hrepr]
  have h0 : ∀ i, Filter.Tendsto (fun t : α => inner ℝ (f t) (B i) • B i) l (nhds 0) := by
    intro i
    have hh := (h (B i)).smul_const (B i)
    simpa using hh
  have hsum := tendsto_finsetSum (Finset.univ) (fun i _ => h0 i)
  simpa using hsum

end Commons.Analysis.InnerProduct