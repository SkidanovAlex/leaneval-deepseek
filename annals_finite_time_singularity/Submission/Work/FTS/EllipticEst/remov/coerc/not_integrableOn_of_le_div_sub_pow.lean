import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllipticEst.remov.integral_sub_rpow_neg
import Submission.Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_of_le_div_pow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

open MeasureTheory

/-- If `f` dominates `θ ↦ c / (b - θ)^k` on `(b - ε, b)` with `c > 0`, `ε > 0` and `k ≥ 2`,
then `f` is not integrable on `(b - ε, b)`: the singularity at the right endpoint is too strong.

The interval is reflected onto `(0, ε)` by the measure preserving map `y ↦ b - y`, which turns
the lower bound into `c / z^k ≤ f (b - z)` on `(0, ε)`; there the power `c / z^k` is already
non-integrable (`AxisIntegral.not_integrableOn_const_div_pow`), and domination transfers
non-integrability to `f`. -/
theorem not_integrableOn_of_le_div_sub_pow {f : ℝ → ℝ} {c b ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    {k : ℕ} (hk : 2 ≤ k) (h : ∀ θ ∈ Set.Ioo (b - ε) b, c / (b - θ) ^ k ≤ f θ) :
    ¬ MeasureTheory.IntegrableOn f (Set.Ioo (b - ε) b) := by
  intro hf
  -- the reflection `y ↦ b - y` is measure preserving and a measurable embedding
  have hmp : MeasurePreserving (fun y : ℝ => b - y) volume volume := by
    simpa using (Measure.measurePreserving_sub_left (volume : Measure ℝ) b)
  have hemb : MeasurableEmbedding (fun y : ℝ => b - y) :=
    (Homeomorph.subLeft b).measurableEmbedding
  -- it maps `(b - ε, b)` back to `(0, ε)`
  have hpre : (fun y : ℝ => b - y) ⁻¹' (Set.Ioo (b - ε) b) = Set.Ioo 0 ε := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
  -- transport integrability of `f` to the reflected function on `(0, ε)`
  have hf' : MeasureTheory.IntegrableOn (fun y : ℝ => f (b - y)) (Set.Ioo 0 ε) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hemb).mpr hf
  -- the reflected lower bound makes `z ↦ c / z ^ k` integrable on `(0, ε)`
  have hg : MeasureTheory.IntegrableOn (fun z : ℝ => c / z ^ k) (Set.Ioo 0 ε) := by
    refine hf'.mono' ?_ ?_
    · exact (measurable_const.div (measurable_id.pow_const k)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hzpos : 0 < z := hz.1
      have hle : c / z ^ k ≤ f (b - z) := by
        have h1 : c / (b - (b - z)) ^ k ≤ f (b - z) :=
          h (b - z) (by simp only [Set.mem_Ioo]; constructor <;> linarith [hz.1, hz.2])
        have h2 : b - (b - z) = z := by ring
        rwa [h2] at h1
      have hpos : 0 < c / z ^ k := div_pos hc (pow_pos hzpos k)
      rw [Real.norm_of_nonneg hpos.le]
      exact hle
  exact Work.FTS.EllipticEst.AxisIntegral.not_integrableOn_const_div_pow hc hε hk hg

end Work.FTS.EllipticEst.remov.coerc
