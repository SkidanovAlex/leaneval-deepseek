import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- Diagonal `wip`-inner products against a weight that is nonnegative on the angular
interval `Iθ` are nonnegative.  This is the only positivity input needed for
`H1IP_nonneg`: the integrand is `g z θ * g z θ * ρ z θ`, a square times the weight. -/
theorem wip_self_nonneg {ρ g : ℝ → ℝ → ℝ} (hρ : ∀ z θ, θ ∈ Spaces.Iθ → 0 ≤ ρ z θ) :
    0 ≤ wip ρ g g := by
  unfold wip
  refine setIntegral_nonneg ?_ ?_
  · simp only [Spaces.Iz]; exact measurableSet_Ici
  · intro z _
    refine setIntegral_nonneg ?_ ?_
    · simp only [Spaces.Iθ]; exact measurableSet_Icc
    · intro θ hθ
      exact mul_nonneg (mul_self_nonneg (g z θ)) (hρ z θ hθ)

theorem H1IP_nonneg (α : ℝ) (h : ℝ → ℝ → ℝ) : 0 ≤ Work.Coercivity.H1IP α h h := by
  have hsin : ∀ θ ∈ Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    simp only [Spaces.Iθ, mem_Icc] at hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2])
  have hDz : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Spaces.Dz h) (Spaces.Dz h) :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hEta : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)) h h :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  have hW : 0 ≤ wip (fun z _ => Spaces.w z ^ 2) h h :=
    wip_self_nonneg (fun z _ _ => sq_nonneg _)
  have hDth : 0 ≤ wip (fun z θ => Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Spaces.Dth h) (Spaces.Dth h) :=
    wip_self_nonneg (fun z θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin θ hθ) _))
  unfold H1IP
  have e1 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hDz
  have e2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 10) hEta
  have e3 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 17) hW
  have e4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 21) hDth
  linarith

end Work.Coercivity
