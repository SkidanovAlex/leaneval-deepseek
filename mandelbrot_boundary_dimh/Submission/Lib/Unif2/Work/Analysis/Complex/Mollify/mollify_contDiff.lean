import Mathlib

/-!
# Smoothness of the mollification of a locally integrable function

For `u` locally integrable on `ℂ` and `ρ` of class `C^n` with compact support, the mollification
`z ↦ ∫ t, ρ t • u (z - t)` is of class `C^n`.  This is `HasCompactSupport.contDiff_convolution_left`
of Mathlib; the only work here is to match the two spellings of the convolution.
-/

open MeasureTheory Set
open scoped Topology Convolution

noncomputable section

namespace Work.Analysis.Complex.Mollify

/-- **The mollification of a locally integrable function by a compactly supported smooth mollifier
is smooth.** -/
theorem mollify_contDiff {u : ℂ → ℂ} {ρ : ℂ → ℝ} {n : ℕ∞}
    (hu : LocallyIntegrable u volume) (hρc : ContDiff ℝ n ρ) (hρs : HasCompactSupport ρ) :
    ContDiff ℝ n (fun z => ∫ t, ρ t • u (z - t)) := by
  have h := hρs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hu
  have hfun : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      = (fun z => ∫ t, ρ t • u (z - t)) := by
    funext z
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply]
  rwa [hfun] at h

end Work.Analysis.Complex.Mollify
