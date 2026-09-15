import Mathlib
import Submission.Commons.Analysis.MomentCurve.transversality_det

open scoped BigOperators

namespace Commons.Analysis.MomentCurve

/-- The Gram matrix of the basis vectors `γ^{(1)}(t),…,γ^{(k)}(t)` (whose `(i,j)` entry is
`∑ l, γ^{(i+1)}(t)_l · γ^{(j+1)}(t)_l`) equals `Bᵀ · B`, where `B = Bmat k t` is the matrix
whose columns are those vectors. -/
lemma gramDeriv_eq_transpose_mul (k : ℕ) (t : ℝ) :
    (fun i j : Fin k => ∑ l : Fin k, gam k t (i.val + 1) l * gam k t (j.val + 1) l)
      = Matrix.transpose (Bmat k t) * Bmat k t := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Bmat, Matrix.of_apply]

/-- The determinant of the Gram matrix of the derivative vectors `γ^{(1)}(t),…,γ^{(k)}(t)`
is the constant `(∏_{i<k} (i+1)!)²`, independent of `t`. -/
lemma gramDeriv_det (k : ℕ) (t : ℝ) :
    Matrix.det (fun i j : Fin k => ∑ l : Fin k, gam k t (i.val + 1) l * gam k t (j.val + 1) l)
      = (∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ)) ^ 2 := by
  rw [gramDeriv_eq_transpose_mul, Matrix.det_mul, Matrix.det_transpose, det_Bmat]
  ring

/-- The Gram determinant of the derivative vectors `γ^{(1)}(t),…,γ^{(k)}(t)` of the moment curve
`Commons.Analysis.MomentCurve.gam k` (with respect to the Euclidean inner product on `Fin k → ℝ`)
is bounded below by a positive constant on `[0,1]`.

Here the Gram matrix is written out explicitly, so that the statement only uses `Matrix.det`. -/
theorem gam_gram_det_lower (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c ≤ Matrix.det (fun i j : Fin k => ∑ l : Fin k,
        Commons.Analysis.MomentCurve.gam k t (i.val + 1) l
          * Commons.Analysis.MomentCurve.gam k t (j.val + 1) l) := by
  refine ⟨(∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ)) ^ 2, ?_, ?_⟩
  · have hprod : 0 < ∏ i : Fin k, (((i.val + 1).factorial : ℕ) : ℝ) := by
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.factorial_pos (i.val + 1)
    positivity
  · intro t _
    rw [gramDeriv_det]

end Commons.Analysis.MomentCurve
