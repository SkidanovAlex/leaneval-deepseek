import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.L1Tails.latDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails

theorem latCoeff_mul_conj (ℓ : ℝ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) (n : Fin 3 → ℤ) :
    Work.BoseBoxFock.L1Tails.latCoeff ℓ W n * (starRingEnd ℂ)
        (Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (Work.BoseBoxFock.kappaL ℓ n))
      = ((‖Submission.BoseGases.kinFT (fun y => (W y : ℂ)) (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
          / ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 : ℝ) : ℂ) := by
  -- `latCoeff ℓ W n` is `Ŵ(κ_n)/‖κ_n‖²` by definition, so the product with `conj Ŵ(κ_n)` is
  -- `|Ŵ(κ_n)|²/‖κ_n‖²`; the degenerate case `‖κ_n‖ = 0` gives `0 = 0` on both sides.
  unfold Work.BoseBoxFock.L1Tails.latCoeff
  rw [div_mul_eq_mul_div, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_div]

end Work.BoseBoxFock.L1Tails
