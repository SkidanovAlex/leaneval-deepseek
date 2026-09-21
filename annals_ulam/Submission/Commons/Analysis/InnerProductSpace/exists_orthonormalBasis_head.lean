import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.exists_linearIsometryEquiv_of_norm_eq

namespace Commons.Analysis.InnerProductSpace

/-- In a finite-dimensional real inner product space of dimension `n + 1`, any unit vector can be
chosen as the first (`0`-th) element of an orthonormal basis indexed by `Fin (n + 1)`. -/
theorem exists_orthonormalBasis_head {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hdim : Module.finrank ℝ E = n + 1) (e : E) (he : ‖e‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ E, b 0 = e := by
  have hcard : Module.finrank ℝ E = Fintype.card (Fin (n + 1)) := by
    rw [hdim, Fintype.card_fin]
  exact exists_orthonormalBasis_apply_eq_of_norm_eq_one hcard 0 he

end Commons.Analysis.InnerProductSpace
