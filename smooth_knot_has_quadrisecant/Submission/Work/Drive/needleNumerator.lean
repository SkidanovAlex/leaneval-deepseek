import Mathlib
import Submission.Work.Drive.blurAngularVelocity
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.sweepBlurFacts

/-!
# The numerator of the doubly blurred needle

This module starts the **assembly** of `hang` for the needle (the positive angular velocity of the
flattened needle consumed by `Work.Drive.lowEnd_of_projection_starShaped`), following the plan of
`Submission/Work/Drive/ANGVEL_NOTES.md`.  The analytic estimates are in
`Submission/Work/Drive/blurAngularVelocity.lean` (`meanProd_bound`, `meanProd_bound₂`, the sharpened
`mismatchOscBound`) and in `arcProfileMargin.lean` (`arcProf_angVel_margin`, the `(D)` input).  What
this module supplies is the **interface**: the coordinates of the doubly blurred needle
`sweepFam r D lam δ₁ δ₂ ε` (and, from `Work.Drive.sweepFam_double_blur_deriv`, its velocity) are the
iterated weighted averages of the coordinates (resp. velocities) of the individual chamfered loops
`sweepLoopChamfer r D lam (ε - δ₂ v) (t - δ₁ u)` over the two-dimensional window.

With that interface, `meanProd_bound₂` turns the numerator `A B' - B A'` of the needle into the
weighted average of the numerators of the loops plus a mismatch bounded by the *oscillations* of the
loop coordinates over the window — exactly the estimate whose remaining input is the quantitative
profile bound (`arcProf_angVel_margin` for the diagonal) and the oscillation bounds.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

variable {r : ℝ → Space} {d : BandArcData}

/-- **The coordinates of the needle are the double averages of the coordinates of the loops.**
For any vector `u`, the `u`-coordinate of the doubly blurred needle `sweepFam r D lam δ₁ δ₂ ε t`
about a point `c'` is the iterated weighted average of the `u`-coordinates of the individual
chamfered loops over the window `(u', v') ∈ [-1,1]²`, with the product bump weight.

The two integrability hypotheses are the ones consumed by
`ContinuousLinearMap.intervalIntegral_comp_comm`; for a fixed `t` both integrands are bounded and
piecewise continuous, so they hold (`MeasureTheory.IntegrableOn.of_bound`). -/
theorem sweepFam_coord_eq_doubleAverage (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (c' u : Space)
    (t : ℝ)
    (hout : IntervalIntegrable
      (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t)
      MeasureTheory.volume (-1) 1)
    (houtc : IntervalIntegrable
      (fun v : ℝ => sweepBump v * inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u)
      MeasureTheory.volume (-1) 1)
    (hinn : ∀ v : ℝ, IntervalIntegrable
      (fun s : ℝ => sweepBump s • sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s))
      MeasureTheory.volume (-1) 1)
    (hinnc : ∀ v : ℝ, IntervalIntegrable
      (fun s : ℝ => sweepBump s *
        inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u)
      MeasureTheory.volume (-1) 1) :
    inner ℝ (sweepFam r D lam δ₁ δ₂ ε t - c') u
      = ∫ v in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1,
          sweepBump v * sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u := by
  -- the inner integral
  have hinner : ∀ v : ℝ, inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t - c') u
      = ∫ s in (-1 : ℝ)..1, sweepBump s *
          inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u := by
    intro v
    have h1 : inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t - c') u
        = inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u - inner ℝ c' u := by
      rw [inner_sub_left]
    have h2 : inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u
        = ∫ s in (-1 : ℝ)..1, sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u := by
      rw [real_inner_comm, sweepSmoothT, ← innerSL_apply_apply (𝕜 := ℝ) (v := u),
        ← (innerSL ℝ u).intervalIntegral_comp_comm (hinn v)]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      show (innerSL ℝ u) (sweepBump s • sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s))
        = sweepBump s * inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u
      rw [innerSL_apply_apply, inner_smul_right, real_inner_comm]
    have hconst : (∫ s in (-1 : ℝ)..1, sweepBump s * inner ℝ c' u) = inner ℝ c' u := by
      rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
    have h3 : (∫ s in (-1 : ℝ)..1, sweepBump s *
          (inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u - inner ℝ c' u))
        = (∫ s in (-1 : ℝ)..1, sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u) - inner ℝ c' u := by
      have hA : IntervalIntegrable
          (fun s : ℝ => sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u)
          MeasureTheory.volume (-1) 1 := hinnc v
      have hB : IntervalIntegrable (fun s : ℝ => sweepBump s * inner ℝ c' u)
          MeasureTheory.volume (-1) 1 :=
        Continuous.intervalIntegrable (sweepBump_continuous.mul continuous_const) _ _
      rw [show (fun s : ℝ => sweepBump s *
            (inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u - inner ℝ c' u))
          = (fun s : ℝ => sweepBump s *
              inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u
            - sweepBump s * inner ℝ c' u) from by funext s; ring]
      rw [intervalIntegral.integral_sub hA hB, hconst]
    have h4 : (∫ s in (-1 : ℝ)..1, sweepBump s *
          (inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s)) u - inner ℝ c' u))
        = ∫ s in (-1 : ℝ)..1, sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u :=
      intervalIntegral.integral_congr (fun s _ => by rw [inner_sub_left])
    rw [h1, h2, ← h3, h4]
  -- the outer integral
  have h1 : inner ℝ (sweepFam r D lam δ₁ δ₂ ε t - c') u
      = inner ℝ (sweepFam r D lam δ₁ δ₂ ε t) u - inner ℝ c' u := by
    rw [inner_sub_left]
  have h2 : inner ℝ (sweepFam r D lam δ₁ δ₂ ε t) u
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u := by
    rw [real_inner_comm, sweepFam, ← innerSL_apply_apply (𝕜 := ℝ) (v := u),
      ← (innerSL ℝ u).intervalIntegral_comp_comm hout]
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    show (innerSL ℝ u) (sweepBump v • sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t)
      = sweepBump v * inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u
    rw [innerSL_apply_apply, inner_smul_right, real_inner_comm]
  have hconst : (∫ v in (-1 : ℝ)..1, sweepBump v * inner ℝ c' u) = inner ℝ c' u := by
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  have h3 : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u - inner ℝ c' u))
      = (∫ v in (-1 : ℝ)..1, sweepBump v *
          inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u) - inner ℝ c' u := by
    have hA : IntervalIntegrable
        (fun v : ℝ => sweepBump v * inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u)
        MeasureTheory.volume (-1) 1 := houtc
    have hB : IntervalIntegrable (fun v : ℝ => sweepBump v * inner ℝ c' u)
        MeasureTheory.volume (-1) 1 :=
      Continuous.intervalIntegrable (sweepBump_continuous.mul continuous_const) _ _
    rw [show (fun v : ℝ => sweepBump v *
          (inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u - inner ℝ c' u))
        = (fun v : ℝ => sweepBump v * inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u
          - sweepBump v * inner ℝ c' u) from by funext v; ring]
    rw [intervalIntegral.integral_sub hA hB, hconst]
  have h4 : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t) u - inner ℝ c' u))
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          (inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t - c') u) :=
    intervalIntegral.integral_congr (fun v _ => by rw [inner_sub_left])
  have h5 : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (inner ℝ (sweepSmoothT r D lam δ₁ (ε - δ₂ * v) t - c') u))
      = ∫ v in (-1 : ℝ)..1, sweepBump v *
          (∫ s in (-1 : ℝ)..1, sweepBump s *
            inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u) :=
    intervalIntegral.integral_congr (fun v _ => by rw [hinner v])
  have h6 : (∫ v in (-1 : ℝ)..1, sweepBump v *
        (∫ s in (-1 : ℝ)..1, sweepBump s *
          inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u))
      = ∫ v in (-1 : ℝ)..1, ∫ s in (-1 : ℝ)..1, sweepBump v * sweepBump s *
          inner ℝ (sweepLoopChamfer r D lam (ε - δ₂ * v) (t - δ₁ * s) - c') u := by
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [h1, h2, ← h3, h4, h5, h6]

end Work.Drive
