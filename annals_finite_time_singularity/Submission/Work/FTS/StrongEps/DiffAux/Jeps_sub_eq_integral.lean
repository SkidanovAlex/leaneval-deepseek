/-
Copyright: work module for the Elgindi finite-time singularity project.

# `J_ε g - g` as an integral against the mean-one kernel

Since the rescaled kernel `Jker ρ ε` has total mass one (`Jker_integral_eq_one`) and
`J_ε` is, in the log coordinates, the convolution with `Jker ρ ε` (`Jeps_eq_integral`),
the difference `J_ε g - g` is the `p`-integral of `Jker ρ ε p` against the *difference*
`g(shift p) - g(z,θ)`:

  `Jeps ρ ε g z θ - g z θ = ∫ p, Jker ρ ε p * (g (zShift z p.1) (thShift θ p.2) - g z θ)`.

This is the form in which the mollifier error is estimated in the `E1`/`E5` chapter: the
first-order Taylor remainder `g(shift) - g(z,θ)` can be bounded by the shifted derivatives
(`FTS/StrongEps/DiffAux/shiftPath_sub.lean`).

The only non-trivial input is *integrability* of `p ↦ Jker ρ ε p * g (zShift z p.1)
(thShift θ p.2)`: it is continuous (the shift stays in the open quadrant, where `g` is
continuous) with compact support (the kernel vanishes off the ball of radius `ε`), hence
Bochner-integrable; this is what lets `integral_sub` split the two terms.
-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

theorem Jeps_sub_eq_integral (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε g z θ - g z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) - g z θ) := by
  -- the shifted point stays in the open quadrant, whatever the shift `p`
  have hmem : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad :=
    fun _ => ⟨zShift_pos hz, thShift_mem hθ⟩
  -- hence the `p ↦ g (zShift z p.1) (thShift θ p.2)` is continuous on all of `ℝ²`
  have hcont_g : Continuous fun p : ℝ × ℝ => g (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hg.comp_continuous (continuous_shift_pair z θ) hmem
  -- the product is continuous with compact support (the kernel is supported in the ball
  -- of radius `ε`), so it is integrable
  have hInt : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_g).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  have hInt2 : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g z θ :=
    (Jker_integrable hρ hε).mul_const _
  -- the kernel has mass one
  have hc : ∫ p : ℝ × ℝ, Jker ρ ε p * g z θ = g z θ := by
    rw [integral_mul_const, Jker_integral_eq_one ρ hρ hε, one_mul]
  -- `J_ε g` is the convolution `∫ p, Jker ρ ε p * g (shift p)`
  rw [Jeps_eq_integral ρ ε g hz hθ]
  refine Eq.symm ?_
  conv_rhs => rw [← hc]
  rw [← integral_sub hInt hInt2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end Work.FTS.StrongEps.DiffAux
