/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary helpers for angular `×` radial products in the weighted space `ℋ⁴`

This module collects the small facts that the two lemmas about
`HkMem α 4 (fun z θ => a θ * r z)` need:

* the two squared-weight identities, in the **nonnegative** form needed on the whole
  angular interval `Iθ = [0,π/2]` (where `sin(2θ)` may *vanish*; the versions in
  `Work.FTS.Nonlinear.RadialProd` require `0 < sin(2θ)` and are therefore unusable at the
  endpoints `θ = 0, π/2`):

  `(A · w z / sin(2θ)^{η/2})² = A² w(z)² σ(θ)`,  `(A · Wt α z θ)² = A² w(z)² τ(α,θ)`

  with `σ = smE`, `τ = smG` the two angular weights;

* `SmoothOpen (fun z θ => a θ * r z)` for `SmoothOpen` factors (`a` angular, `r` radial);

* `IntegrableOn (Rint r) Iz` for an honest `ℋ⁴`-radial function `r`, obtained from
  `∫_θ HkIntegrand α 4 (fun z _ => r z) z θ = Rint r z * Kth` (`Kth ≥ 1`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.AuxAngRad

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The squared light weight, without a strict positivity hypothesis.**
`(A · w z / sin(2θ)^{η/2})² = A² w(z)² σ(θ)` for `0 ≤ sin(2θ)`.

The proof avoids `Real.rpow_add` (which needs `sin(2θ) > 0`) and uses only
`Real.rpow_mul` and `Real.rpow_neg`, both of which hold for `0 ≤ x`. -/
theorem light_sq_nn (A z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (A * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2,
      ← Real.rpow_mul hs]
    congr 1
    push_cast
    ring
  rw [mul_pow, div_pow, h1, Work.FTS.Nonlinear.RadialProd.smE, div_eq_mul_inv,
    ← Real.rpow_neg hs]
  ring

/-- **The squared heavy weight, without a strict positivity hypothesis.**
`(A · Wt α z θ)² = A² w(z)² τ(α,θ)` for `0 ≤ sin(2θ)`. -/
theorem heavy_sq_nn (α A z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (A * Work.Spaces.Wt α z θ) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs]
    congr 1
    push_cast
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Work.FTS.Nonlinear.RadialProd.smG, mul_pow,
    mul_pow, h1]
  ring

/-- The product of an angular and a radial `SmoothOpen` function is `SmoothOpen` on the open
quadrant.  (The uncurried product is the product of the two uncurried factors.) -/
theorem smoothOpen_ang_rad {a r : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun _ (θ : ℝ) => a θ)).mp ha n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z _ => r z)).mp hr n
  have hfun : Function.uncurry (fun z θ : ℝ => a θ * r z)
      = fun p : ℝ × ℝ => a p.2 * r p.1 := rfl
  rw [hfun]
  exact h1.mul h2

/-- The radial density `Rint r` of an honest `ℋ⁴`-function is integrable on `Iz`, because its
`θ`-integral is `∫_θ HkIntegrand α 4 r z θ = Rint r z · Kth` with `Kth ≥ 1`. -/
theorem integrableOn_Rint_of_HkMem {α : ℝ} {r : ℝ → ℝ}
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.Nonlinear.RadialProd.Rint r z)
      Work.Spaces.Iz := by
  have hKth : Work.FTS.Nonlinear.RadialProd.Kth ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one Work.FTS.Nonlinear.RadialProd.one_le_Kth)
  have h : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.Nonlinear.RadialProd.Rint r z * Work.FTS.Nonlinear.RadialProd.Kth)
      Work.Spaces.Iz := by
    simpa only [Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad] using hrmem.2
  exact MeasureTheory.IntegrableOn.congr_fun (h.div_const Work.FTS.Nonlinear.RadialProd.Kth)
    (fun z _ => mul_div_cancel_right₀ _ hKth) measurableSet_Ici

end Work.FTS.NonlinRows.AuxAngRad
