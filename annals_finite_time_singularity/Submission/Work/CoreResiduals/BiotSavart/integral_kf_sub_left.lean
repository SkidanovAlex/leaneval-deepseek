import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Change of variables `b = y - a` for the far-field kernel `kf`.**  The map
`a ↦ y - a` is the isometry `subLeft y` of `ℝ³` (a reflection followed by a translation); it is
measure-preserving for Lebesgue measure and sends the ball `B(0,ρ)` onto the ball `B(y,ρ)`.
Hence the integral of the kernel over `B(0,ρ)` after the substitution equals the integral of the
kernel over `B(y,ρ)`. -/
theorem integral_kf_sub_left (ρ : ℝ) (y : Work.LWP.R3) :
    ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, Work.StabilityFar.Decay.kf (y - a)
      = ∫ b in Metric.ball y ρ, Work.StabilityFar.Decay.kf b := by
  -- `a ↦ y - a` preserves Lebesgue measure on `ℝ³`...
  have hmp := MeasureTheory.Measure.measurePreserving_sub_left (MeasureTheory.volume) y
  -- ... and is a measurable embedding, being a homeomorphism of `ℝ³`.
  have hemb : MeasurableEmbedding (fun a : Work.LWP.R3 => y - a) :=
    (MeasurableEquiv.subLeft y).measurableEmbedding
  -- ... and it maps `B(0,ρ)` onto `B(y,ρ)`.
  have hset : (fun a : Work.LWP.R3 => y - a) '' Metric.ball (0 : Work.LWP.R3) ρ
      = Metric.ball y ρ := by
    ext b
    simp only [Set.mem_image, Metric.mem_ball, dist_eq_norm]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hb
      refine ⟨y - b, ?_, by abel⟩
      simpa [norm_sub_rev] using hb
  rw [← hset]
  exact (hmp.setIntegral_image_emb hemb Work.StabilityFar.Decay.kf
    (Metric.ball (0 : Work.LWP.R3) ρ)).symm

end Work.CoreResiduals.BiotSavart
