import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.NeuFrac

/-- Pointwise algebraic identity underlying `trial_algebra`:
`A p / (‖p‖² + c) = ‖p‖² A p / (‖p‖² + c)² + c (A p / (‖p‖² + c)²)`. -/
lemma div_eq_sq_combination {c : ℝ} (hc : 0 < c) (A : EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    A p / (‖p‖ ^ 2 + c) = ‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2
      + c * (A p / (‖p‖ ^ 2 + c) ^ 2) := by
  have h : ‖p‖ ^ 2 + c ≠ 0 := by positivity
  field_simp

/-- Integrability of `p ↦ A p / (‖p‖² + c)²`, from boundedness of the multiplier. -/
lemma integrable_div_sq {c : ℝ} (hc : 0 < c) {A : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : MeasureTheory.Integrable A) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => A p / (‖p‖ ^ 2 + c) ^ 2) := by
  have h1 : ∀ p : EuclideanSpace ℝ (Fin 3), ‖((‖p‖ ^ 2 + c) ^ 2)⁻¹‖ ≤ (c ^ 2)⁻¹ := fun p => by
    have hc2 : c ^ 2 ≤ (‖p‖ ^ 2 + c) ^ 2 := by nlinarith [sq_nonneg (‖p‖), hc]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hc2
  have := hA.mul_bdd (f := A) (g := fun p : EuclideanSpace ℝ (Fin 3) => ((‖p‖ ^ 2 + c) ^ 2)⁻¹)
    (by measurability) (Filter.Eventually.of_forall h1)
  simpa only [div_eq_mul_inv] using this

/-- Integrability of `p ↦ ‖p‖² A p / (‖p‖² + c)²`. -/
lemma integrable_normSq_mul_div_sq {c : ℝ} (hc : 0 < c) {A : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : MeasureTheory.Integrable A) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2) := by
  have h1 : ∀ p : EuclideanSpace ℝ (Fin 3), ‖‖p‖ ^ 2 * ((‖p‖ ^ 2 + c) ^ 2)⁻¹‖ ≤ c⁻¹ := fun p => by
    have h2 : ‖p‖ ^ 2 * c ≤ (‖p‖ ^ 2 + c) ^ 2 := by
      nlinarith [sq_nonneg (‖p‖), sq_nonneg (‖p‖ ^ 2), hc]
    rw [Real.norm_of_nonneg (by positivity)]
    have h : ‖p‖ ^ 2 / (‖p‖ ^ 2 + c) ^ 2 ≤ 1 / c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      simpa using h2
    rwa [div_eq_mul_inv, one_div] at h
  have := hA.mul_bdd (f := A)
    (g := fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * ((‖p‖ ^ 2 + c) ^ 2)⁻¹)
    (by measurability) (Filter.Eventually.of_forall h1)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

/-- Integrability of `p ↦ A p / (‖p‖² + c)`. -/
lemma integrable_div {c : ℝ} (hc : 0 < c) {A : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : MeasureTheory.Integrable A) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => A p / (‖p‖ ^ 2 + c)) := by
  have h1 : ∀ p : EuclideanSpace ℝ (Fin 3), ‖(‖p‖ ^ 2 + c)⁻¹‖ ≤ c⁻¹ := fun p => by
    have hc2 : c ≤ ‖p‖ ^ 2 + c := by nlinarith [sq_nonneg (‖p‖), hc]
    rw [Real.norm_of_nonneg (by positivity)]
    exact (inv_le_inv₀ (by positivity) hc).mpr hc2
  have := hA.mul_bdd (f := A) (g := fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ 2 + c)⁻¹)
    (by measurability) (Filter.Eventually.of_forall h1)
  simpa only [div_eq_mul_inv] using this

theorem trial_algebra {c : ℝ} (hc : 0 < c) {A : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hA : MeasureTheory.Integrable A) :
    (2 * (∫ p : EuclideanSpace ℝ (Fin 3), A p / (‖p‖ ^ 2 + c))
      - (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2)
      - c * (∫ p : EuclideanSpace ℝ (Fin 3), A p / (‖p‖ ^ 2 + c) ^ 2))
    = ∫ p : EuclideanSpace ℝ (Fin 3), A p / (‖p‖ ^ 2 + c) := by
  have hI3 := integrable_div_sq hc hA
  have hI2 := integrable_normSq_mul_div_sq hc hA
  have hcongr : (∫ p : EuclideanSpace ℝ (Fin 3), A p / (‖p‖ ^ 2 + c))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          (‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2 + c * (A p / (‖p‖ ^ 2 + c) ^ 2)) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun p => div_eq_sq_combination hc A p))
  have hsplit :
      (∫ p : EuclideanSpace ℝ (Fin 3),
          (‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2 + c * (A p / (‖p‖ ^ 2 + c) ^ 2)))
      = (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * A p / (‖p‖ ^ 2 + c) ^ 2)
        + c * (∫ p : EuclideanSpace ℝ (Fin 3), A p / (‖p‖ ^ 2 + c) ^ 2) := by
    rw [MeasureTheory.integral_add hI2 (hI3.const_mul c),
      MeasureTheory.integral_const_mul]
  linarith [hcongr, hsplit]

end Work.BoseKinLoc.NeuFrac
