import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- For an orthonormal family `u`, the squared norm of the linear combination
`∑ i, a i • u i` equals the sum of the squares of the coefficients. -/
lemma orthonormal_normSq_sum_smul {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : ι → E) (hu : Orthonormal ℝ u)
    (a : ι → ℝ) :
    ‖(Finset.univ.sum fun i => a i • u i)‖ ^ 2 =
      Finset.univ.sum (fun i => (a i) ^ 2) := by
  classical
  calc
    ‖(Finset.univ.sum fun i => a i • u i)‖ ^ 2
        = inner ℝ (Finset.univ.sum fun i => a i • u i) (Finset.univ.sum fun i => a i • u i) := by
            rw [← real_inner_self_eq_norm_sq]
    _ = ∑ i ∈ Finset.univ, a i * a i := by
            simpa using (Orthonormal.inner_sum (𝕜 := ℝ) hu a a Finset.univ)
    _ = Finset.univ.sum (fun i => (a i) ^ 2) := by
            simp [pow_two]

end Commons.Analysis.InnerProductSpace
