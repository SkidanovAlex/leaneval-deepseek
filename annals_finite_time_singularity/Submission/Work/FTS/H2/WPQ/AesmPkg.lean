/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability of the `ℋ^k`-integrand in the interior class

`Work.Spaces.aesm_HkIntegrand_quad` provides the a.e. strong measurability of
`(z,θ) ↦ HkIntegrand α k F z θ` when `F` is `C^∞` *on a neighbourhood of the closed
quadrant* (`ContDiffOn ℝ ⊤`).  The interior class `Work.FTS.LocData.SmoothQuad` is weaker
(smoothness only on the open quadrant), and there the same statement follows from
`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad` (continuity on the open quadrant) plus
the vanishing `HkIntegrand α k F 0 θ = 0` of the degenerate slice `z = 0`.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.WPQ

set_option autoImplicit false

/-- A.e. strong measurability of the `ℋ^k`-integrand of a `SmoothQuad` function: both the
`θ`-slices at every `z ∈ Iz` and the uncurried function are a.e. strongly measurable for the
restricted Lebesgue measures. -/
theorem aesm_HkIntegrand_smoothQuad (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.LocData.SmoothQuad F) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.Spaces.HkIntegrand α k F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k F hF
  refine ⟨fun z hz => ?_, Work.Spaces.aesm_of_continuousOn_Qd _ hcont⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
  · rw [← h]
    have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k F 0 θ) = fun _ : ℝ => (0 : ℝ) :=
      funext fun θ => Work.Spaces.HkIntegrand_zero_z α k F θ
    rw [hzero]
    exact aestronglyMeasurable_const
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont h

end Work.FTS.H2.WPQ
