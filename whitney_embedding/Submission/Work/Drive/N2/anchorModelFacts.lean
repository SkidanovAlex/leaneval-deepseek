import Mathlib
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2.saddlePsi_helpers
import Submission.Work.Drive.N2.saddlePsi_eq_self_of_im_sq_ge
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.canonChartOfScaled
-- NOTE (H8, 2026-09-27): the import of `Submission.Work.Drive.N2.levelSeparatingMap` was
-- *unused* (the four lemmas below only use `saddlePsi` and its helpers) and it contributed to the
-- import cycle that put `Work.Drive.N2.levelSeparatingMap` (hence the D2 holder
-- `Work.N2C.exists_certifiedWindow_saddle`) into the closure of `saddlePin_oneComp_or`/`landingWide_band`.
-- Removed here; nothing else changed.
import Submission.Work.Drive.N2.windowDatum

/-!
# The model facts behind the anchor picture of the saddle window

The saddle window `criticalWindowDrawing` pastes two pieces on the value band
`(c - lam η, c + lam η)` of a saddle `p`: the model piece `cE3 ∘ Ψ ∘ Z` on the collar-bounded region
`D = {|Im (Z ·)²| < c₀}` and the transported piece `A₀ ∘ foot` off it.  The anchor picture `A₀` must
satisfy the rows of `Work.Drive.N2.saddleWindow_drawing_lam` **only at the feet** of the off-`D` band
points, and this file records the two model facts which reduce those rows to the model's own rows:

* `Ψ` fixes the whole ANCHOR LEVEL: for `(z ^ 2).re = -η` the plateau correction vanishes, so
  `Ψ η δ z = z`.  Since every foot lies on the anchor level, the model value at a collar point `x`
  is `cE3 (Z (foot x))`: the seam identity is *readable on the level*;
* the same fact for the *foot* of any off-`D` point completes the argument that the anchor picture
  needs no pinning row of its own beyond `Z̃ = Z` at the feet.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- **The model fixes the anchor level.**  If `Re (z ^ 2) = -η` then the plateau correction of
`saddlePhi` vanishes at `z ^ 2`, so the ratio is one and `Ψ z = z`. -/
lemma saddlePsi_eq_self_of_re_sq_neg_eta {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    {z : ℂ} (hz : (z ^ 2).re = -η) : saddlePsi η δ z = z := by
  have h2 : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
    linarith
  have hphi : saddlePhi η δ (z ^ 2) = z ^ 2 := by
    rw [saddlePhi_eq_sub]
    simp [hz]
  have hr : saddleRatio η δ z = 1 := by
    have h := saddleRatio_mul_sq (η := η) (δ := δ) hδ h2 z
    rw [hphi] at h
    exact mul_right_cancel₀ (pow_ne_zero 2 hz0) (by rw [h, one_mul])
  rw [saddlePsi, hr, Complex.sqrt_one, mul_one]

/-- The `Im` of the square is preserved by the model (restatement for the anchor level). -/
lemma saddlePsi_sq_re_of_re_sq_neg_eta {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    {z : ℂ} (hz : (z ^ 2).re = -η) : ((saddlePsi η δ z) ^ 2).re = -η := by
  rw [saddlePsi_eq_self_of_re_sq_neg_eta hη hδ hδ₂ hz, hz]

end Work.Drive.N2

namespace Work.Drive.N2

/-- **The core of the anchor-injectivity argument.**

Two points `zx`, `zy` of the chart, of the same level (`Re zx² = Re zy²`), whose feet `wx`, `wy` (the
points of the anchor level `Re (·)² = -η` on their orbits) have the same chart coordinate and whose
branch is the positive one (`0 < Re (w · conj z)`), have the same square: hence (with the chart's
injectivity) they are the same point.

The positivity is exactly the second conclusion of `Work.Drive.N2.saddlePsi_collar`: the flow keeps
`Re (·) · conj (·)` positive along the trajectory, so the foot is `saddlePsi` of the point. -/
lemma anchorFoot_sq_eq_core {η : ℝ} {zx zy wx wy : ℂ}
    (hwx : wx ^ 2 = (-(η : ℂ)) + (((zx ^ 2).im : ℝ) : ℂ) * Complex.I)
    (hwy : wy ^ 2 = (-(η : ℂ)) + (((zy ^ 2).im : ℝ) : ℂ) * Complex.I)
    (hsx : 0 < (wx * (starRingEnd ℂ) zx).re)
    (hsy : 0 < (wy * (starRingEnd ℂ) zy).re)
    (hlev : (zx ^ 2).re = (zy ^ 2).re)
    (heq : wx = wy) : zx = zy := by
  have ht : (zx ^ 2).im = (zy ^ 2).im := by
    have h1 : (wx ^ 2).im = (zx ^ 2).im := by rw [hwx]; simp
    have h2 : (wy ^ 2).im = (zy ^ 2).im := by rw [hwy]; simp
    rw [← h1, heq, h2]
  have hsq : zx ^ 2 = zy ^ 2 := Complex.ext hlev ht
  have hfac : (zx - zy) * (zx + zy) = 0 := by
    have h' : zx ^ 2 - zy ^ 2 = 0 := by rw [hsq]; ring
    linear_combination h'
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hzy : zy = -zx := by linear_combination h
    have hrev : (wy * (starRingEnd ℂ) zy).re = -(wx * (starRingEnd ℂ) zx).re := by
      rw [heq, hzy, map_neg, mul_neg, Complex.neg_re]
    linarith [hsx, hsy, hrev]

/-- The same, in the form in which the window uses it: if the feet of two points of the same level
have the same chart coordinate then the points themselves have the same chart coordinate. -/
lemma anchorFoot_eq_core {η : ℝ} {zx zy wx wy : ℂ}
    (hwx : wx ^ 2 = (-(η : ℂ)) + (((zx ^ 2).im : ℝ) : ℂ) * Complex.I)
    (hwy : wy ^ 2 = (-(η : ℂ)) + (((zy ^ 2).im : ℝ) : ℂ) * Complex.I)
    (hsx : 0 < (wx * (starRingEnd ℂ) zx).re)
    (hsy : 0 < (wy * (starRingEnd ℂ) zy).re)
    (hlev : (zx ^ 2).re = (zy ^ 2).re)
    (heq : wx = wy) : zx = zy :=
  anchorFoot_sq_eq_core hwx hwy hsx hsy hlev heq

end Work.Drive.N2
