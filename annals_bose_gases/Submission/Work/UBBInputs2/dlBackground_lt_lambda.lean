import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.UBBInputs2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

/-- The elementary background estimate behind FS `eq:aprioriPsi`: if
`C (ρA³)^{η₀} < lhyC + K_B³` — exactly the hypothesis under which FS place the
a-priori threshold `J = C(ρA³)^{η₀}` below `lhyC + K_B³` — then the background
`−4πρ²A(1 + K_B³√(ρA³))` lies strictly below the target `Lambda A C η₀ ρ`.

Indeed, `(ρA³)^{1/2+η₀} = √(ρA³)·(ρA³)^{η₀}`, so the claim is the algebraic
inequality `C(ρA³)^{η₀} < lhyC + K_B³` multiplied by `√(ρA³) > 0` and by
`4πρ²A > 0`. -/
theorem dlBackground_lt_lambda {A C η₀ ρ K_B : ℝ} (hA : 0 < A) (hρ : 0 < ρ)
    (hη₀ : 0 < η₀) (h : C * (ρ * A ^ 3) ^ η₀ < Work.UBB.lhyC + K_B ^ 3) :
    -(4 * Real.pi * ρ ^ 2 * A * (1 + K_B ^ 3 * Real.sqrt (ρ * A ^ 3)))
      < Work.UBB.Lambda A C η₀ ρ := by
  have hP : 0 < ρ * A ^ 3 := by positivity
  have hF : 0 < 4 * Real.pi * ρ ^ 2 * A := by positivity
  have hs : 0 < Real.sqrt (ρ * A ^ 3) := Real.sqrt_pos.2 hP
  have hrw : (ρ * A ^ 3) ^ (1 / 2 + η₀) = Real.sqrt (ρ * A ^ 3) * (ρ * A ^ 3) ^ η₀ := by
    rw [Real.rpow_add hP, ← Real.sqrt_eq_rpow]
  have hmain : C * (ρ * A ^ 3) ^ (1 / 2 + η₀)
      < Work.UBB.lhyC * Real.sqrt (ρ * A ^ 3) + K_B ^ 3 * Real.sqrt (ρ * A ^ 3) := by
    rw [hrw]
    nlinarith [mul_lt_mul_of_pos_right h hs]
  simp only [Work.UBB.Lambda]
  nlinarith [hmain, hF]

end Work.UBBInputs2
