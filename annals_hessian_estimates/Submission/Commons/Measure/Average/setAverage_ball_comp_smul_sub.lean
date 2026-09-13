import Mathlib
import Submission.Commons.Measure.Lebesgue.setAverage_comp_smul_ball

namespace Commons.Measure.Average

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution Pointwise in
/-- Translating the set average by a vector. -/
theorem setAverage_vadd {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) :
    (⨍ x in c +ᵥ s, f x) = ⨍ x in s, f (c + x) := by
  let φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => c + x
  have hφ_eq : φ = ⇑(MeasurableEquiv.addLeft c) := by
    funext x; rw [MeasurableEquiv.coe_addLeft]
  have hφemb : MeasurableEmbedding φ := by
    rw [hφ_eq]; exact (MeasurableEquiv.addLeft c).measurableEmbedding
  have hmap : Measure.map φ volume = volume := by
    rw [hφ_eq]; exact Measure.IsAddLeftInvariant.map_add_left_eq_self c
  have hpre : φ ⁻¹' (c +ᵥ s) = s := by
    ext x; simp only [Set.mem_preimage, φ]; exact vadd_mem_vadd_set_iff
  have hmeas : MeasurableSet (c +ᵥ s) := hs.const_vadd c
  have hres : volume.restrict (c +ᵥ s) = Measure.map φ (volume.restrict s) := by
    have h1 := Measure.restrict_map (μ := volume) (f := φ) hφemb.measurable hmeas
    rw [hmap, hpre] at h1
    exact h1
  have hreal : volume.real (c +ᵥ s) = volume.real s := by
    rw [Measure.real_def, Measure.real_def, measure_vadd]
  have hint : ∫ x in c +ᵥ s, f x = ∫ x in s, f (c + x) := by
    rw [hres, MeasurableEmbedding.integral_map hφemb]

  rw [setAverage_eq, setAverage_eq, hreal, hint]

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution Pointwise in
theorem setAverage_ball_comp_smul_sub {n : ℕ} {x₀ : EuclideanSpace ℝ (Fin n)} {r t : ℝ}
    (ht : 0 < t) (hr : 0 < r) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    (⨍ y in Metric.ball x₀ r, F y)
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r), F (x₀ + t⁻¹ • z) := by
  have hball : (x₀ +ᵥ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) = Metric.ball x₀ r := by
    rw [vadd_ball]; simp
  have htrans := setAverage_vadd (n := n) (f := F) (c := x₀)
    (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) Metric.isOpen_ball.measurableSet
  have hsub : (⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, F (x₀ + w))
      = ⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (t * r), F (x₀ + t⁻¹ • z) := by
    have hs := Commons.Measure.Lebesgue.setAverage_comp_smul_ball (n := n)
      (f := fun w => F (x₀ + w)) (r := t * r) (t := t⁻¹) (inv_pos.mpr ht) (mul_pos ht hr)
    rw [show t⁻¹ * (t * r) = r by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]] at hs
    simpa only using hs.symm
  rw [← hball, htrans, hsub]

end Commons.Measure.Average
