/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the `H^k` integrand on the quadrant

The `H^k` integrand `HkIntegrand α k f z θ` is built from the weighted derivatives
`D_z^i f · w/ sin(2θ)^{η/2}` and `D_z^j D_θ^i f · W`; it is a finite sum of squares of
such expressions.  Two facts are used:

* `continuousOn_HkIntegrand_Qd`: if `F` is `C^∞` on the open quadrant
  `quadU = (-1,∞) × (0,π/2)`, then `(z,θ) ↦ HkIntegrand α k F z θ` is continuous on
  the open square `Qd = (0,∞) × (0,π/2)`, where both weights are honest continuous
  functions (`z > 0` keeps `w = (1+z)²/z²` finite, `0 < θ < π/2` keeps
  `sin 2θ > 0`);

* `aesm_of_continuousOn_Qd` / `aesm_slice_of_continuousOn_Qd`: continuity on the
  open square upgrades to a.e. strong measurability for the restricted measures
  `volume.restrict Iz`, `volume.restrict Iθ` and their product, because the
  complement of `Qd` inside `Iz × Iθ` is contained in the three null segments
  `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`.

At `z = 0` the whole integrand vanishes identically (the radial weight `w` is `0`
there), which covers the single slice that is not handled by the continuity
argument.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- At `z = 0` the whole `H^k` integrand vanishes: the radial weight `w` is `0` at the
origin, and the product weight `W = w · w_θ` too. -/
theorem HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    HkIntegrand α k f 0 θ = 0 := by
  simp [HkIntegrand, w, Wt]

theorem aesm_HkIntegrand_quad (α : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) Work.Spaces.quadU) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Spaces.HkIntegrand α 4 F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 F p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont := continuousOn_HkIntegrand_Qd α 4 F hF
  refine ⟨fun z hz => ?_, aesm_of_continuousOn_Qd _ hcont⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · -- the slice `z = 0`: the integrand vanishes identically
    rw [← h]
    have hzero : (fun θ : ℝ => HkIntegrand α 4 F 0 θ) = fun _ : ℝ => (0 : ℝ) :=
      funext fun θ => HkIntegrand_zero_z α 4 F θ
    rw [hzero]
    exact aestronglyMeasurable_const
  · -- the slice `z > 0` is a slice of a function continuous on the open square
    exact aesm_slice_of_continuousOn_Qd _ hcont h

end Work.Spaces
