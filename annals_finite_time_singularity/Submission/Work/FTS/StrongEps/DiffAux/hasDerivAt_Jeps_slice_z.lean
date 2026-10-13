import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Commute
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

/-- **`E1`, the `z`-slice form, `HasDerivAt` version.**  For a profile `g` which is `C^n` on the
open quadrant for every `n`, the `z`-slice `z' ↦ J_ε g z' θ` of the mollifier is differentiable
at every interior point `z > 0` with derivative the `p`-integral of the derivative of the
integrand, i.e. the kernel against `e^{-p₁} ∂_z g` at the shifted point.

The proof is a wrapper around the two `Commute.lean` results: `hasDerivAt_integral_Jeps_z`
differentiates the `p`-integral form under the integral (over the ball of radius `ε`, where the
kernel lives), `setIntegral_eq_integral_of_forall_compl_eq_zero` removes the restriction to that
ball, `Jeps_eq_integral` identifies the slice near `z` with the integral, and `Jeps_deriv_z`
supplies the value of the derivative.  The hypothesis `hg` only has to be fed at the two orders
`1` (`C¹` of `g`) and `2` (which gives, through `uncurry_partial_c1`, the continuity of `∂_z g`
on the quadrant). -/
theorem hasDerivAt_Jeps_slice_z (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ)
      (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Real.exp (-p.1) * Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))) z := by
  have hf : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad := hg 1
  have hdf : ContinuousOn (Function.uncurry (Work.Spaces.pz g)) Work.FTS.StrongEps.Quad :=
    ((Work.Spaces.uncurry_partial_c1 Work.FTS.StrongEps.isOpen_Quad (hg 2)).1).continuousOn
  -- the restricted integral of `hasDerivAt_integral_Jeps_z` is the full integral: the kernel
  -- vanishes off the ball of radius `ε`
  have hball : (fun z' => ∫ p : ℝ × ℝ in Metric.closedBall (0 : ℝ × ℝ) ε,
        Work.FTS.StrongEps.Jker ρ ε p * g (Work.FTS.StrongEps.zShift z' p.1)
          (Work.FTS.StrongEps.thShift θ p.2))
      = fun z' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g
          (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    funext z'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p * g
        (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  -- near `z` the `z`-slice of `Jeps` is the `p`-integral of the shifted profile
  have hev : (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ)
      =ᶠ[𝓝 z] fun z' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g
          (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.StrongEps.Jeps_eq_integral ρ ε g hz' hθ
  have hdiff : DifferentiableAt ℝ (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ) z := by
    have h0 := Work.FTS.StrongEps.hasDerivAt_integral_Jeps_z (ρ := ρ) hρ hε hf hdf hz hθ
    rw [hball] at h0
    exact hev.differentiableAt_iff.mpr h0.differentiableAt
  rw [← Work.FTS.StrongEps.Jeps_deriv_z hρ hε hf hdf hz hθ]
  exact hdiff.hasDerivAt

end Work.FTS.StrongEps.DiffAux
