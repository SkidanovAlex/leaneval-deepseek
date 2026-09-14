import Submission.NBody.FirstVariation
import Submission.NBody.ActionTau
import Mathlib

/-!
# The same-ball estimate for the action potential (Maderna)

Maderna's *same-ball estimate* states that if two configurations `x`, `y` are contained in a ball
of radius `R`, then for every `τ > 0` there is an absolutely continuous curve joining them in time
`τ` whose action is at most `α R²/τ + β τ/R`, with constants depending only on the number of
bodies and their masses.  This is the analytic core of the Hölder estimate for `φ_h`
(`thm-phih.estim` of Maderna–Venturelli).

This file starts the chapter.  The first ingredient is the bridge from an estimate on the *real*
integral of the Lagrangian (`∫ (½∑mᵢ‖γ̇ᵢ‖² + U(γ))`) to an estimate on the action potential.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Bridge from a real-integral bound to the action potential.**  If `γ` joins `x` to `y` in
time `τ`, is absolutely continuous, avoids collisions almost everywhere, and its real Lagrangian
integral is at most `B`, then `φ(x,y,τ) ≤ B`. -/
theorem actionPotTau_le_ofReal_of_integral_lagR {m : Fin N → ℝ} {x y : EN E N} {τ B : ℝ}
    (hτ : 0 < τ) (hm : ∀ i, 0 ≤ m i) {γ : ℝ → EN E N}
    (h0 : γ 0 = x) (h1 : γ τ = y) (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hnc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ → WithoutCollisions (γ t))
    (hint : Integrable (fun t => lagR m 0 (γ t) (deriv γ t)) (volume.restrict (Set.Ioc 0 τ)))
    (hbound : ∫ t in (0 : ℝ)..τ, lagR m 0 (γ t) (deriv γ t) ≤ B) :
    actionPotTau m x y τ ≤ ENNReal.ofReal B := by
  refine (actionPotTau_le_of (m := m) (x := x) (y := y) (τ := τ) h0 h1 hac).trans ?_
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)),
      (0 : ℝ) ≤ lagR m 0 (γ t) (deriv γ t) :=
    Eventually.of_forall fun t => by
      have hR : lagR m 0 (γ t) (deriv γ t)
          = (1 / 2) * ∑ i, m i * ‖deriv γ t i‖ ^ 2 + U m (γ t) := by
        unfold lagR; ring
      rw [hR]
      have hK : 0 ≤ (1 / 2) * ∑ i, m i * ‖(deriv γ t) i‖ ^ 2 := by
        refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
        exact mul_nonneg (hm i) (sq_nonneg _)
      have hU := U_nonneg hm (γ t)
      linarith
  have hae : (fun t => lagrangian m 0 (γ t) (deriv γ t))
      =ᵐ[volume.restrict (Set.Ioc 0 τ)]
        fun t => ENNReal.ofReal (lagR m 0 (γ t) (deriv γ t)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hnc] with t ht
    intro hmem
    exact lagrangian_eq_ofReal_lagR (ht hmem)
  rw [actionOn, lintegral_congr_ae hae,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le hτ.le]
  exact ENNReal.ofReal_le_ofReal hbound

end Submission.NBody
