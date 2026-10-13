import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SinPowIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

theorem SinPowIntegralPiO {γ : ℝ} (h1 : 1 < γ) (h2 : γ ≤ 2) {a b : ℝ}
    (ha : Real.pi / 4 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) ≤ (100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1) := by
  have hγ1 : 0 < γ - 1 := by linarith
  -- Substitution `x ↦ π/2 - x`, under which `sin (2 x) ↦ sin (π - 2 x) = sin (2 x)`.
  have hsym : (∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2))
      = ∫ x in (Real.pi / 2 - b)..(Real.pi / 2 - a), (Real.sin (2 * x)) ^ (γ - 2) := by
    rw [← intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => (Real.sin (2 * x)) ^ (γ - 2)) (a := a) (b := b) (Real.pi / 2)]
    apply intervalIntegral.integral_congr
    intro x _
    show (Real.sin (2 * x)) ^ (γ - 2) = (Real.sin (2 * (Real.pi / 2 - x))) ^ (γ - 2)
    have harg : 2 * (Real.pi / 2 - x) = Real.pi - 2 * x := by ring
    rw [harg, Real.sin_pi_sub]
  -- The reflected interval lies in `[0, π/4]`, where the sibling estimate applies.
  have h0 : (0 : ℝ) ≤ Real.pi / 2 - b := by linarith
  have hle : Real.pi / 2 - b ≤ Real.pi / 2 - a := by linarith
  have hq : Real.pi / 2 - a ≤ Real.pi / 4 := by linarith
  have hbnd := SinPowIntegral (γ := γ) h1 h2 h0 hle hq
  have harg2 : 2 * (Real.pi / 2 - a) = Real.pi - 2 * a := by ring
  rw [harg2, Real.sin_pi_sub] at hbnd
  rw [hsym]
  exact hbnd

end Work.FTS.StrongEps.EpsLocalPStar
