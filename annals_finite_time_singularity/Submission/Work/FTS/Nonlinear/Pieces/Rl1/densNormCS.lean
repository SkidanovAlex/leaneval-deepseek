import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.CS1D
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.Pieces.slots
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densN1Sum
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

/-! ## Cauchy–Schwarz for the `L₁₂` density

The a.e. domination `‖L₁₂dens h s‖ ≤ A s · B s` by a product of two nonnegative `L²((0,∞))`
functions gives the factorised `L¹`-bound
`∫₀^∞ ‖L₁₂dens h s‖ ≤ √(∫₀^∞ A²) · √(∫₀^∞ B²)`.

This is `Work.FTS.H2.CS1D` (one-dimensional Cauchy–Schwarz with the *unconditional*
integrability convention: when `‖L₁₂dens h‖` fails to be integrable, its integral is the junk
value `0` and the inequality is trivial) applied to the nonnegative function
`fun s => ‖L₁₂dens h s‖`, whose absolute value is itself.  The only point requiring care is
that the left-hand side of the goal is `∫ ‖…‖` and not `|∫ ‖…‖|`; they agree because
`∫ ‖…‖ ≥ 0` (`MeasureTheory.integral_nonneg`, no integrability needed). -/

theorem densNormCS {h : ℝ → ℝ → ℝ} {A B : ℝ → ℝ}
    (hA : MeasureTheory.MemLp A 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hB : MeasureTheory.MemLp B 2 (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hA0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] A)
    (hB0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] B)
    (hbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Construction.L12dens h s‖ ≤ A s * B s) :
    (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens h s‖)
      ≤ Real.sqrt (∫ s in Set.Ioi (0 : ℝ), A s ^ 2)
        * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), B s ^ 2) := by
  have hbd' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      |‖Work.Construction.L12dens h s‖| ≤ A s * B s := by
    filter_upwards [hbd] with s hs
    simpa only [Real.norm_eq_abs, abs_abs] using hs
  have hcs := Work.FTS.H2.CS1D (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (g := fun s => ‖Work.Construction.L12dens h s‖) hA hB hA0 hB0 hbd'
  have hnn : 0 ≤ ∫ s, ‖Work.Construction.L12dens h s‖
      ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.integral_nonneg (fun s => norm_nonneg (Work.Construction.L12dens h s))
  rw [abs_of_nonneg hnn] at hcs
  simpa using hcs

end Work.FTS.Nonlinear.Pieces.Rl1
