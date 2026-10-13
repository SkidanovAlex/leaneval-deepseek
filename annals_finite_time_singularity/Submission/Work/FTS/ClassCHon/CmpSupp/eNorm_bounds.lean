/-
# `eNorm_bounds` — the two sided size bounds for the mode norm `eNorm`

`Work.EllipticEst.ModalSolution.eNorm m = ∫_{Iθ} eFam m θ ^ 2 · cos θ dθ` is the squared
`L²(Iθ, cos θ dθ)`-norm of the `m`-th Dirichlet eigenfunction.  Its value is known
(`Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts`):

  `eNorm m = ((2m+2)(2m+3))/(4m+5)`,

and this file extracts the two crude consequences needed downstream, namely
`1 ≤ eNorm m` and `m ≤ eNorm m`.  Both are the elementary estimates

  `(2m+2)(2m+3) - (4m+5) = 4m² + 6m + 1 > 0`   and
  `(2m+2)(2m+3) - m(4m+5) = 5m + 6 ≥ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.ClassCHon.CmpSupp

/-- Closed form of the modal norm: `eNorm m = ((2m+2)(2m+3))/(4m+5)`. -/
theorem eNorm_eq (m : ℕ) :
    Work.EllipticEst.ModalSolution.eNorm m
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]

/-- The closed form is always at least `1`, since `(2m+2)(2m+3) - (4m+5) = 4m² + 6m + 1`. -/
theorem one_le_eNorm_closed (m : ℕ) :
    1 ≤ ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith [sq_nonneg ((m : ℝ) + 1), (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- The closed form dominates `m`, since `(2m+2)(2m+3) - m(4m+5) = 5m + 6 ≥ 0`. -/
theorem cast_le_eNorm_closed (m : ℕ) :
    (m : ℝ) ≤ ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

theorem eNorm_bounds (m : ℕ) :
    1 ≤ Work.EllipticEst.ModalSolution.eNorm m
      ∧ (m : ℝ) ≤ Work.EllipticEst.ModalSolution.eNorm m := by
  rw [eNorm_eq m]
  exact ⟨one_le_eNorm_closed m, cast_le_eNorm_closed m⟩

end Work.FTS.ClassCHon.CmpSupp
