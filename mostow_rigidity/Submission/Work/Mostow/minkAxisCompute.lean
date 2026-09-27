import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.minkGeoSeg

/-!
# The Minkowski pairing of two points of a geodesic "axis"

Let `x`, `y` be null vectors of the Minkowski space `ℝ^{Fin n ⊕ Fin 1}` (`⟨x,x⟩ = ⟨y,y⟩ = 0`),
e.g. the two null directions spanning the plane of a loxodromic axis.  Then for all `κ s t`,

`⟨κ(e^s x + e^{-s} y), κ(e^t x + e^{-t} y)⟩ = κ² ⟨x,y⟩ (e^{s-t} + e^{t-s})`.

This is a direct bilinear-algebra computation: expand `mink` by bilinearity, kill the two
terms containing `⟨x,x⟩`, `⟨y,y⟩` with the nullity hypotheses, and use `exp s · exp(-t) =
exp (s - t)`, `exp(-s) · exp t = exp (t - s)`.
-/

namespace Work.Mostow

theorem minkAxisCompute (n : ℕ) (x y : Fin n ⊕ Fin 1 → ℝ)
    (hx : mink x x = 0) (hy : mink y y = 0)
    (κ s t : ℝ) :
    mink (κ • (Real.exp s • x + Real.exp (-s) • y))
        (κ • (Real.exp t • x + Real.exp (-t) • y))
      = κ ^ 2 * mink x y * (Real.exp (s - t) + Real.exp (t - s)) := by
  -- pairing of an arbitrary linear combination of the two null vectors
  have haux : ∀ a b c d : ℝ,
      mink (a • x + b • y) (c • x + d • y) = (a * d + b * c) * mink x y := by
    intro a b c d
    rw [minkSeg_add_left, minkSeg_add_right, minkSeg_add_right,
      minkSeg_smul, minkSeg_smul, minkSeg_smul, minkSeg_smul, hx, hy, minkSeg_comm y x]
    ring
  rw [minkSeg_smul, haux]
  have h1 : Real.exp s * Real.exp (-t) = Real.exp (s - t) := by
    rw [← Real.exp_add, show s + -t = s - t by ring]
  have h2 : Real.exp (-s) * Real.exp t = Real.exp (t - s) := by
    rw [← Real.exp_add, show -s + t = t - s by ring]
  rw [h1, h2]
  ring

end Work.Mostow
