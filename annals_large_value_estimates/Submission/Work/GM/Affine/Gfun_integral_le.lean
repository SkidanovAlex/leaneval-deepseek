import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.smoothed_psiSmooth_fourier
import Submission.Work.GM.Affine.Gfun_le_gSum
import Submission.Work.GM.Affine.affineSum_sq_le_gSum_sq
import Submission.Work.GM.Affine.cauchy_base

/-!
# `Work.GM.Affine.Gfun_integral_le` (GM §9, region II: `L²` domination of the honest sum)

The pointwise domination `Gfun C₀ T M₂ f u ≤ gSum 1 M₂ M₂ (2C₀M₂+1) f̃ u` of
`Work.GM.Affine.Gfun_le_gSum` (with `f̃ = smoothed psiSmooth T f`) passes to the squares, and
hence to the integrals, because both sides are pointwise non-negative and the majorant is
continuous with compact support (the ranges `R1`, `R2`, `R3ext` are finite, and `f̃` is
continuous with compact support), so its square is integrable.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem Gfun_integral_le {C₀ T M₂ : ℝ} (hC₀ : 0 ≤ C₀) (hT : 0 < T) (hM₂ : 0 < M₂)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hfnn : ∀ u, 0 ≤ f u) :
    ∫ u, (Gfun C₀ T M₂ f u) ^ 2 ≤
      ∫ u, (gSum 1 M₂ M₂ (2 * C₀ * M₂ + 1) (smoothed psiSmooth T f) u) ^ 2 := by
  obtain ⟨hFcont, hFcs, -⟩ := smoothed_psiSmooth_fourier hT hf hcs
  -- the honest sum is pointwise non-negative
  have hGnn : ∀ u, 0 ≤ Gfun C₀ T M₂ f u := by
    intro u
    rw [Gfun]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => smoothed_psiSmooth_nonneg hT hfnn _
  -- pointwise domination by the majorant, with `K = 1`, `M₃ = 2C₀M₂ + 1`
  have hle : ∀ u, Gfun C₀ T M₂ f u ≤
      gSum 1 M₂ M₂ (2 * C₀ * M₂ + 1) (smoothed psiSmooth T f) u := by
    intro u
    exact Gfun_le_gSum (f := f) (K := 1) (C₀ := C₀) (T := T) (M₂ := M₂)
      (r₃ := 2 * C₀ * M₂ + 1) one_pos hC₀ hT hM₂ (by rw [div_one]) hfnn u
  -- the majorant is continuous with compact support, so its square is integrable
  have hBint : Integrable (fun u => (gSum 1 M₂ M₂ (2 * C₀ * M₂ + 1)
      (smoothed psiSmooth T f) u) ^ 2) := by
    have hcont : Continuous (fun u => gSum 1 M₂ M₂ (2 * C₀ * M₂ + 1)
        (smoothed psiSmooth T f) u) :=
      continuous_gSum_real' 1 M₂ M₂ (2 * C₀ * M₂ + 1) hFcont
    have hcsg : HasCompactSupport (fun u => gSum 1 M₂ M₂ (2 * C₀ * M₂ + 1)
        (smoothed psiSmooth T f) u) :=
      hasCompactSupport_gSum_real' 1 M₂ M₂ (2 * C₀ * M₂ + 1) hM₂ hFcs
    exact (hcont.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hcsg)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hBint
    (Filter.Eventually.of_forall fun u => ?_)
  exact pow_le_pow_left₀ (hGnn u) (hle u) 2

end

end Work.GM.Affine
