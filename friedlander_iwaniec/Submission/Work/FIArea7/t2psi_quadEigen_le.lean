import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.normQuadEigenLe

namespace Work.FIArea7

/-- The quadratic eigenvalue (23.1) is bounded by four times the divisor function:
`‖λ(n)‖ ≤ #{primary z : |z|² = n} ≤ r₂(n) ≤ 4·d(n)`, using `‖psi‖ ≤ 1` and `‖JKSym z‖ ≤ 1`
(`Work.FIArea7.norm_JKSym_le_one`) and `quadEigen_eq_sum` plus `mem_gBox_of_gnorm_eq`. -/
theorem t2psi_quadEigen_le (psi : GaussianInt → ℂ) (hpsi : ∀ z, ‖psi z‖ ≤ 1) (n : ℕ) :
    ‖Work.FIArea7.quadEigen psi n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
  normQuadEigenLe psi hpsi n

end Work.FIArea7
