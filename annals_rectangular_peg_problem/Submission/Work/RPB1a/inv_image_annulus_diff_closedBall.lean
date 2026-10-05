import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.inv_image_annulus_inter_ball

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- Inversion `w ↦ w⁻¹` maps the *outer* half `annulus ρ \ closedBall 0 1 = {1 < ‖w‖ < ρ⁻¹}`
of the inversion-symmetric annulus `annulus ρ = {ρ < ‖w‖ < ρ⁻¹}` bijectively onto its inner
half `annulus ρ ∩ ball 0 1 = {ρ < ‖w‖ < 1}`.

This is the reverse direction of `inv_image_annulus_inter_ball`: inversion is an involution
(`(w⁻¹)⁻¹ = w`), so it witnesses the two halves of the annulus as mirror images of one another,
and the claim follows by applying inversion to both sides of the sibling lemma. -/
theorem inv_image_annulus_diff_closedBall {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (fun w : ℂ => w⁻¹) '' (annulus ρ \ closedBall 0 1) = annulus ρ ∩ ball 0 1 := by
  have h := inv_image_annulus_inter_ball hρ0 hρ1
  calc (fun w : ℂ => w⁻¹) '' (annulus ρ \ closedBall 0 1)
      = (fun w : ℂ => w⁻¹) '' ((fun w : ℂ => w⁻¹) '' (annulus ρ ∩ ball 0 1)) := by rw [h]
    _ = annulus ρ ∩ ball 0 1 := by rw [image_image]; simp

end Work.RPB1a
