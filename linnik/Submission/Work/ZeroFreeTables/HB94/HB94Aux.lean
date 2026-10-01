import Mathlib
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.HB94

/-- `Ksum`, unfolded (local copy of `Work.ZeroFreeTables.Ksum_def'`, which lives in
`HBTheorem1_complex_h4.lean`; this file keeps the `HB94` development independent of that
in-flight file). -/
theorem Ksum_def_aux (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L : ℝ) (s : ℂ)
    (χ : DirichletCharacter ℂ q) :
    Work.ZeroFreeTables.Ksum q f L s χ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) := rfl

/-- `χ.primitiveCharacter ≠ 1` for `χ ≠ 1` (local copy of `Work.ZeroFreeTables.primitive_ne_one_aux`
from `HBTheorem1_complex_h4.lean`). -/
theorem primitive_ne_one_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- A `zeroMult` zero in the ball is a divisor zero of the primitive completed `L`-function
(local copy of `Work.ZeroFreeTables.divisor_ne_zero_of_zeroMult_aux`). -/
theorem divisor_ne_zero_of_zeroMult_aux {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (hzm : zeroMult χ u ≠ 0) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0 := by
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction
      (primitive_ne_one_aux χ hχ)).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 R)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u ≠ 0 := by
    revert hzm
    simp only [zeroMult]
    intro h; exact h
  intro h0
  rw [hcast] at h0
  exact hnat (by exact_mod_cast h0)

end Work.ZeroFreeTables.HB94
