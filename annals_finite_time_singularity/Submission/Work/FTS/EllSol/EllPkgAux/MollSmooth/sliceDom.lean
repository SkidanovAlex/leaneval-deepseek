import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont
import Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_int_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The slice is dominated by the two data values plus the weighted second-derivative
functional.**  For `G` smooth on the open quadrant and honestly slice-integrable
(`SliceHonestOpen`), and every `w > 0`, the whole angular slice `τ ↦ G w τ` on `(0, π/2)` is
bounded by `MG G w`.

The proof is the second-order Taylor formula at the interior base point `θ = π/4`,
`f τ = f (π/4) + (τ - π/4) f' (π/4) + ∫_{π/4}^{τ} (τ - t) f'' t dt`,
together with the interval Cauchy–Schwarz bound `∫ |f''| ≤ √(length) √(∫ f''²)`; the
remaining second-derivative mass is upgraded to the weighted functional `E2sl G w` because
`σ_η = sin(2θ)^{-η} ≥ 1` on `(0, π/2)`.  The numerical constants are harmless:
`|τ - π/4| ≤ π/4 < 1` and `(π/4)·√(π/4) ≤ 1`. -/
theorem sliceDom (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hH : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
  intro w hw τ hτ
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < Real.pi / 2 := hτ.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the slice at radius `w` is `C²` on the open angular interval
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hS.curry_θ hw).of_le hsmo
  have ha0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have ha1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have ha_mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha0, ha1⟩
  -- integrability of the weighted square of the second derivative
  have hHint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
      rw [Work.Spaces.w]; positivity
    have h0 := hH.1 w hw
    have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      intro θ
      rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
            * Work.FTS.EllipticEst.thEta θ) from by ring]
      exact inv_mul_cancel_left₀ (ne_of_gt hc) _
    rw [show (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
          (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ) from funext (fun θ => (hEq θ).symm)]
    exact h0.const_mul _
  -- the Taylor formula at the base point `π/4`
  have hT := slice_taylor_two hf2 ha_mem hτ
  -- the bound on the integral part
  have hTail : |∫ t in (Real.pi / 4)..τ,
        (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t|
      ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rcases le_total (Real.pi / 4) τ with hle | hle
    · -- `π/4 ≤ τ`: apply the estimate on `[π/4, τ]`
      have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc (Real.pi / 4) τ) := slice_dd_cont hf2 ha_mem hτ
      have hc : ∀ t ∈ Set.Icc (Real.pi / 4) τ, |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      exact slice_int_bound hle ha0 hτ1 (by linarith) hcont hc hHint
    · -- `τ ≤ π/4`: flip the interval
      have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc τ (Real.pi / 4)) := slice_dd_cont hf2 hτ ha_mem
      have hc : ∀ t ∈ Set.Icc τ (Real.pi / 4), |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.2]
      have h := slice_int_bound hle hτ0 ha1 (by linarith) hcont hc hHint
      rw [intervalIntegral.integral_symm, abs_neg]
      exact h
  -- the final assembly
  have hMG : Work.FTS.EllSol.EllPkgAux.MG G w
      = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
  rw [hMG]
  have habs : |τ - Real.pi / 4| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_le_four, Real.pi_pos]
  have hdnn : (0 : ℝ) ≤ |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| := abs_nonneg _
  have hcoef : (Real.pi / 4) * Real.sqrt (Real.pi / 4) ≤ 1 := by
    have h1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_le_four]
    have h2 : Real.sqrt (Real.pi / 4) ≤ 1 := Real.sqrt_le_one.mpr h1
    nlinarith [Real.sqrt_nonneg (Real.pi / 4)]
  have hsnn : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_nonneg _
  calc |G w τ|
      = |G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4)
          + ∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        rw [hT]
    _ ≤ |G w (Real.pi / 4)| + |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + |∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        have h1 := abs_add_le
          (G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
          (∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t)
        have h2 := abs_add_le (G w (Real.pi / 4))
          ((τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
        rw [abs_mul] at h2
        linarith [h1, h2]
    _ ≤ |G w (Real.pi / 4)| + 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        have hmul : |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
            ≤ 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| :=
          mul_le_mul_of_nonneg_right habs hdnn
        have hc2 : (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
              Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            ≤ 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_right hcoef hsnn
        linarith [hmul, hc2, hTail]
    _ = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
          + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        rw [one_mul, one_mul]
        rfl

end Work.FTS.EllSol.EllPkgAux.MollSmooth
