import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.PosSemidefOfQuadform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.Frame

open Matrix

theorem psd_form_re_nonneg {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A : ι → ι → ℝ} (hsym : ∀ i j, A i j = A j i)
    (hquad : ∀ v : ι → ℝ, 0 ≤ ∑ i : ι, ∑ j : ι, v i * A i j * v j)
    (u : ι → H) :
    0 ≤ ∑ i : ι, ∑ j : ι, A i j * (inner ℂ (u i) (u j)).re := by
  -- `A` is a positive semidefinite real matrix (given by its quadratic form) …
  have hA : (Matrix.of A).PosSemidef := Work.BoseB4.PosSemidefOfQuadform A hsym hquad
  -- … and so is the real part of the Gram matrix of the family `u`.
  have hB : (Matrix.of fun i j => (inner ℂ (u i) (u j)).re).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.of_apply, star_trivial]
      simpa only [Complex.conj_re] using congrArg Complex.re (inner_conj_symm (u i) (u j))
    · intro x
      -- the quadratic form of the Gram matrix is `‖∑ᵢ xᵢ uᵢ‖²`
      have key : star x ⬝ᵥ ((Matrix.of fun i j => (inner ℂ (u i) (u j)).re) *ᵥ x)
          = (inner ℂ (∑ i, ((x i : ℝ) : ℂ) • u i) (∑ j, ((x j : ℝ) : ℂ) • u j)).re := by
        trans ∑ i, ∑ j, x i * (inner ℂ (u i) (u j)).re * x j
        · simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
        · rw [sum_inner]
          simp only [inner_sum]
          simp only [Complex.re_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
            Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, zero_mul, sub_zero, mul_assoc]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
      rw [key, ← RCLike.re_to_complex, inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact sq_nonneg _
  -- Schur's product theorem: the entrywise product of `A` and the Gram matrix is PSD;
  -- evaluate its quadratic form at the all-ones vector.
  have h1 := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ : ι => (1 : ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard, Matrix.of_apply, Finset.mul_sum, mul_assoc] using h1

end Work.BoseBoxFock.Frame
