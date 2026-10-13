import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.SourceSide

/-- **Cauchy–Schwarz from the discriminant.**  If the real quadratic form
`t ↦ A + 2 t C + t² B` is nonnegative everywhere and `B ≥ 0`, then `C² ≤ A * B`. -/
private lemma sq_le_mul_of_quadratic_nonneg {A B C : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B) : C ^ 2 ≤ A * B := by
  rcases lt_or_eq_of_le hB with hBpos | hB0
  · have hBne : B ≠ 0 := ne_of_gt hBpos
    have ht := h (-C / B)
    have key : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [key] at ht
    have h3 : 0 ≤ B * (A - C ^ 2 / B) := mul_nonneg (le_of_lt hBpos) ht
    have h4 : B * (A - C ^ 2 / B) = B * A - C ^ 2 := by
      field_simp
    rw [h4] at h3
    nlinarith [h3]
  · have hBz : B = 0 := hB0.symm
    have hC : C = 0 := by
      by_contra hCne
      have ht := h (-(A + 1) / (2 * C))
      have hdiv : 2 * (-(A + 1) / (2 * C)) * C = -(A + 1) := by
        field_simp
      simp only [hBz, mul_zero, add_zero] at ht
      linarith [ht, hdiv]
    rw [hC, hBz]
    simp

/-- **Cauchy–Schwarz for the integral of a product**, in squared form: for a.e. strongly
measurable `u, v` with `u²` and `v²` integrable on `s`,

`(∫_s u v)² ≤ (∫_s u²) (∫_s v²)`.

The point of stating it for an arbitrary `s ⊆ ℝ × ℝ` is that the pairing `u · v` need not be
known to be integrable a priori: the bound `|u v| ≤ u² + v²` provides that, after which the
usual discriminant argument applies to the nonnegative quadratic form
`t ↦ ∫_s (u + t v)² = A + 2 t C + t² B`. -/
theorem sq_integral_mul_le_of_integrable_sq {s : Set (ℝ × ℝ)} {u v : ℝ × ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn (fun p => u p ^ 2) s)
    (hv : MeasureTheory.IntegrableOn (fun p => v p ^ 2) s)
    (hum : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict s))
    (hvm : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume.restrict s)) :
    (∫ p in s, u p * v p) ^ 2 ≤ (∫ p in s, u p ^ 2) * (∫ p in s, v p ^ 2) := by
  have hu' : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p ^ 2)
      (MeasureTheory.volume.restrict s) := hu
  have hv' : MeasureTheory.Integrable (fun p : ℝ × ℝ => v p ^ 2)
      (MeasureTheory.volume.restrict s) := hv
  -- `u * v` is integrable on `s`, by `|u v| ≤ u² + v²` and `Integrable.mono'`.
  have huv_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p * v p)
      (MeasureTheory.volume.restrict s) := by
    have hsum : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p ^ 2 + v p ^ 2)
        (MeasureTheory.volume.restrict s) :=
      MeasureTheory.Integrable.congr (hu'.add hv')
        (Filter.Eventually.of_forall fun p => by simp only [Pi.add_apply])
    refine MeasureTheory.Integrable.mono'
      (g := fun p : ℝ × ℝ => u p ^ 2 + v p ^ 2) hsum (hum.mul hvm) ?_
    filter_upwards with p
    have h := sq_nonneg (|u p| - |v p|)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (u p), sq_abs (v p)]
  -- The quadratic form `t ↦ ∫_s (u + t v)²`, evaluated.
  have hquad : ∀ t : ℝ, ∫ p in s, (u p + t * v p) ^ 2
      = (∫ p in s, u p ^ 2) + 2 * t * (∫ p in s, u p * v p)
        + t ^ 2 * (∫ p in s, v p ^ 2) := by
    intro t
    have h1 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => 2 * t * (u p * v p) + t ^ 2 * v p ^ 2)
        (MeasureTheory.volume.restrict s) :=
      MeasureTheory.Integrable.congr
        ((huv_int.const_mul (2 * t)).add (hv'.const_mul (t ^ 2)))
        (Filter.Eventually.of_forall fun p => by simp only [Pi.add_apply])
    have hcongr : ∫ p in s, (u p + t * v p) ^ 2
        = ∫ p in s, (u p ^ 2 + (2 * t * (u p * v p) + t ^ 2 * v p ^ 2)) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have hsplit1 : ∫ p in s, (u p ^ 2 + (2 * t * (u p * v p) + t ^ 2 * v p ^ 2))
        = (∫ p in s, u p ^ 2)
          + ∫ p in s, (2 * t * (u p * v p) + t ^ 2 * v p ^ 2) :=
      MeasureTheory.integral_add hu' h1
    have hsplit2 : ∫ p in s, (2 * t * (u p * v p) + t ^ 2 * v p ^ 2)
        = (∫ p in s, 2 * t * (u p * v p)) + ∫ p in s, t ^ 2 * v p ^ 2 :=
      MeasureTheory.integral_add (huv_int.const_mul (2 * t)) (hv'.const_mul (t ^ 2))
    have hcm1 : ∫ p in s, 2 * t * (u p * v p) = (2 * t) * (∫ p in s, u p * v p) :=
      MeasureTheory.integral_const_mul (2 * t) (fun p : ℝ × ℝ => u p * v p)
    have hcm2 : ∫ p in s, t ^ 2 * v p ^ 2 = t ^ 2 * (∫ p in s, v p ^ 2) :=
      MeasureTheory.integral_const_mul (t ^ 2) (fun p : ℝ × ℝ => v p ^ 2)
    rw [hcongr, hsplit1, hsplit2, hcm1, hcm2]
    ring
  -- It is nonnegative, being the integral of a square.
  have hnn : ∀ t : ℝ, 0 ≤ (∫ p in s, u p ^ 2) + 2 * t * (∫ p in s, u p * v p)
      + t ^ 2 * (∫ p in s, v p ^ 2) := by
    intro t
    rw [← hquad t]
    exact MeasureTheory.integral_nonneg fun p => sq_nonneg (u p + t * v p)
  have hB : 0 ≤ ∫ p in s, v p ^ 2 :=
    MeasureTheory.integral_nonneg fun p => sq_nonneg (v p)
  exact sq_le_mul_of_quadratic_nonneg (A := ∫ p in s, u p ^ 2)
    (B := ∫ p in s, v p ^ 2) (C := ∫ p in s, u p * v p) hB hnn

end Work.FTS.H2.ModalSolR.SourceSide
