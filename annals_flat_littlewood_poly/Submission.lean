import ChallengeDeps
import Submission.Agg

open FlatLittlewoodPoly
open scoped Polynomial

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 :
    ∃ Δ δ : ℝ, Δ > δ ∧ δ > 0 ∧ ∀ n ≥ 2,
      ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = n ∧
      ∀ z : ℂ, ‖z‖ = 1 → δ * √n ≤ ‖P.eval z‖ ∧
      ‖P.eval z‖ ≤ Δ * √n := by
  exact theorem_1_1_final

end Submission
