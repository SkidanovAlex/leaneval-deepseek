import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace Commons.Analysis.Radon

open MeasureTheory
open scoped RealInnerProductSpace Pointwise

/-- Pointwise negation of a set coincides with the "set negation" of `Set` (which is defined as
the preimage of negation). -/
private lemma neg_image_eq_neg {E : Type*} [AddGroup E] (X : Set E) : Neg.neg '' X = -X := by
  ext x
  simp [Set.mem_neg]

/-- Scalar multiplication of sets commutes with pointwise negation. -/
private lemma smul_neg_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Set ℝ) (X : Set E) : a • (Neg.neg '' X) = Neg.neg '' (a • X) := by
  ext y
  simp only [Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, z, ⟨x, hx, rfl⟩, hyz⟩
    exact ⟨r • x, ⟨r, hr, x, hx, rfl⟩, by rw [← hyz, smul_neg]⟩
  · rintro ⟨w, ⟨r, hr, x, hx, rfl⟩, hyw⟩
    exact ⟨r, hr, -x, ⟨x, hx, rfl⟩, by rw [← hyw, smul_neg]⟩

/-- The image of the antipodal image `-s` of a set of unit vectors under the coercion to `E` is the
negation (in `E`) of the image of `s`. -/
private lemma subtype_val_image_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set (Metric.sphere (0 : E) 1)) :
    (Subtype.val '' (-s) : Set E) = Neg.neg '' (Subtype.val '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_neg] at hy
    exact ⟨(↑(-y) : E), ⟨-y, hy, rfl⟩, by simp⟩
  · rintro ⟨z, ⟨w, hw, hwz⟩, hz⟩
    refine ⟨-w, ?_, ?_⟩
    · rw [Set.mem_neg]
      simpa using hw
    · rw [← hz, ← hwz]
      rfl

/-- For a negation-invariant measure `μ` on a normed space, the induced surface measure
`MeasureTheory.Measure.toSphere μ` on the unit sphere is invariant under the antipodal map
`ω ↦ -ω`.  (The proof goes through the defining formula
`toSphere_apply' : μ.toSphere s = finrank ℝ E • μ (Ioo 0 1 • (↑ '' s))`, the set identity
`↑ '' (-s) = Neg.neg '' (↑ '' s)`, `Set.smul_set_neg` and `Measure.measure_neg`.) -/
theorem toSphere_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsNegInvariant]
    (s : Set (Metric.sphere (0 : E) 1)) (hs : MeasurableSet s) :
    μ.toSphere (-s) = μ.toSphere s := by
  have hms : MeasurableSet (-s) := hs.neg
  rw [Measure.toSphere_apply' (μ := μ) hms, Measure.toSphere_apply' (μ := μ) hs]
  congr 1
  rw [subtype_val_image_neg s, smul_neg_image, neg_image_eq_neg, Measure.measure_neg]

end Commons.Analysis.Radon