import Mathlib
import Submission.Work.ORVonNeumann.Basic

/-!
# The conjugate-transpose involution on `Matₙ(R)` is proper when `R` has no
non-trivial sums of squares

If `R` is a `*`-ring with no non-trivial sums of squares (`HasNoNontrivialSquares R`),
then the conjugate-transpose involution on `Matₙ(R)` is proper: `M * Mᴴ = 0` forces
`M = 0`.

Indeed `(M * Mᴴ) i i = ∑ k, M i k * (M i k)⋆`, so `M * Mᴴ = 0` gives
`∑ k, M i k * (M i k)⋆ = 0` for every row `i`; `HasNoNontrivialSquares` then forces every
entry of the matrix to vanish.
-/

set_option autoImplicit false

namespace Work.ORVonNeumann.Regular

open Matrix

/-- The `(i,i)`-entry of `M * Mᴴ` is the sum of squares `∑ k, M i k * (M i k)⋆`. -/
private lemma mul_star_apply_self {R : Type*} [Ring R] [StarRing R]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (M * star M) i i = ∑ k : Fin n, M i k * star (M i k) := by
  simp [Matrix.mul_apply, Matrix.star_apply]

/-- The conjugate-transpose involution on `Matₙ(R)` is proper whenever `R` has no
non-trivial sums of squares. -/
theorem matrix_isProperStar {R : Type*} [Ring R] [StarRing R] (hsq : Work.ORVonNeumann.HasNoNontrivialSquares R) (n : ℕ) : Work.ORVonNeumann.IsProperStar (Matrix (Fin n) (Fin n) R) := by
  intro M hM
  ext i j
  have hii : (∑ k : Fin n, M i k * star (M i k)) = 0 := by
    rw [← mul_star_apply_self M i]
    have := congrFun (congrFun hM i) i
    simpa using this
  exact hsq n (fun k => M i k) hii j

end Work.ORVonNeumann.Regular
