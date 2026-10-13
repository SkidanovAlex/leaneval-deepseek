import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux

/-- For `p ≤ -1` and `t > 0`, the function `θ ↦ (π/2 - θ)^p` is not integrable on the left
neighbourhood `(π/2 - t, π/2)` of `π/2`: it blows up at the right endpoint faster than a
logarithm, so its integral diverges. -/
theorem NotIntegrable {p t : ℝ} (hp : p ≤ -1) (ht : 0 < t) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ p)
      (Set.Ioo (Real.pi / 2 - t) (Real.pi / 2)) := by
  intro h
  -- Write `c` for `π/2`; the integrand is `u ↦ u ^ p` composed with the reflection
  -- `θ ↦ c - θ`, which carries `(0, t)` onto `(c - t, c)`.
  generalize hc : (Real.pi / 2 : ℝ) = c at h
  have hmp : MeasureTheory.MeasurePreserving (fun θ : ℝ => c - θ)
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume c
  have hme : MeasurableEmbedding (fun θ : ℝ => c - θ) :=
    (MeasurableEquiv.subLeft c).measurableEmbedding
  have hset : (fun θ : ℝ => c - θ) ⁻¹' (Set.Ioo (0 : ℝ) t) = Set.Ioo (c - t) c := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h1 <;> constructor <;> linarith
  -- Transfer integrability back along the reflection.
  have h' : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ p) (Set.Ioo (0 : ℝ) t)
      MeasureTheory.volume := by
    rw [← hmp.integrableOn_comp_preimage hme]
    show MeasureTheory.IntegrableOn (fun θ : ℝ => (c - θ) ^ p)
      ((fun θ : ℝ => c - θ) ⁻¹' Set.Ioo (0 : ℝ) t) MeasureTheory.volume
    rw [hset]
    exact h
  -- Mathlib: `x ↦ x ^ p` is integrable on `(0, t)` iff `-1 < p`.
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ht).mp h'
  linarith

end Work.FTS.EllipticEst.AngAWeak.SRSAux
