import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric Set

namespace Work.CoreResiduals.BiotSavart.Bundle

/-- **Change of variables for the reflection `a ↦ x - a` of `ℝ³`.**

The map `a ↦ x - a` is an isometry of `ℝ³` (negation followed by a translation), hence measure
preserving; it sends the ball `B(0,ρ)` onto `B(x,ρ)` and the ball `B(y,R)` onto `B(x - y,R)`, and
images of differences are differences of images.  Hence the set integral over the "difference of
two balls" region transforms accordingly. -/
theorem setIntegral_ball_diff_ball_comp_sub_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Work.LWP.R3 → E) (ρ R : ℝ) (x y : Work.LWP.R3) :
    (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R), f (x - a))
      = ∫ b in (Metric.ball x ρ) \ (Metric.ball (x - y) R), f b := by
  -- The reflection `T a = x - a` is measure preserving and a measurable embedding.
  have hT : MeasureTheory.MeasurePreserving (fun a : Work.LWP.R3 => x - a) volume volume := by
    have h3 : MeasureTheory.MeasurePreserving (fun a : Work.LWP.R3 => x + -a) volume volume :=
      (measurePreserving_add_left volume x).comp (LinearIsometryEquiv.neg ℝ).measurePreserving
    exact h3
  have hTemb : MeasurableEmbedding (fun a : Work.LWP.R3 => x - a) := by
    have := Homeomorph.measurableEmbedding (Homeomorph.subLeft x)
    simpa using this
  -- Membership of the image points in the two balls.
  have hmem1 : ∀ a : Work.LWP.R3,
      x - a ∈ Metric.ball x ρ ↔ a ∈ Metric.ball (0 : Work.LWP.R3) ρ := by
    intro a
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show x - a - x = -a by abel, norm_neg, sub_zero]
  have hmem2 : ∀ a : Work.LWP.R3,
      x - a ∈ Metric.ball (x - y) R ↔ a ∈ Metric.ball y R := by
    intro a
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show x - a - (x - y) = -(a - y) by abel, norm_neg]
  -- The reflection maps the difference of balls onto the reflected difference of balls.
  have hmemB : ∀ a : Work.LWP.R3,
      (x - a ∈ (Metric.ball x ρ) \ (Metric.ball (x - y) R))
        ↔ (a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R)) := by
    intro a
    simp only [Set.mem_sdiff, hmem1 a, hmem2 a]
  have hmemB' : ∀ a : Work.LWP.R3,
      (a ∈ (Metric.ball x ρ) \ (Metric.ball (x - y) R))
        ↔ (x - a ∈ (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R)) := by
    intro a
    have h := hmemB (x - a)
    rwa [show x - (x - a) = a by abel] at h
  have hset : (fun a : Work.LWP.R3 => x - a) ''
      ((Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball y R))
      = (Metric.ball x ρ) \ (Metric.ball (x - y) R) := by
    ext b
    rw [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hmemB a).mpr ha
    · intro hb
      exact ⟨x - b, (hmemB' b).mp hb, by simp⟩
  rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb hT hTemb f _, hset]

end Work.CoreResiduals.BiotSavart.Bundle
