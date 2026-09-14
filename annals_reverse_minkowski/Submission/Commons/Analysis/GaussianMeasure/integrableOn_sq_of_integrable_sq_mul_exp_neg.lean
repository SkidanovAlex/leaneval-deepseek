import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

theorem integrableOn_sq_of_integrable_sq_mul_exp_neg {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hg : MeasureTheory.Integrable (fun x => g x ^ 2 * Real.exp (-(f x)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    MeasureTheory.IntegrableOn (fun x => g x ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    exact integrableOn_empty
  · obtain ⟨x₀, _hx₀, hmax⟩ := hK.exists_isMaxOn hKne hf.continuousOn
    have hmeas : AEStronglyMeasurable (fun x => g x ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      have h1 : AEStronglyMeasurable (fun x => g x ^ 2 * Real.exp (-(f x))) volume :=
        hg.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun x => Real.exp (f x)) volume :=
        (Real.continuous_exp.comp hf).aestronglyMeasurable
      have h3 : AEStronglyMeasurable
          (fun x => (g x ^ 2 * Real.exp (-(f x))) * Real.exp (f x)) volume := h1.mul h2
      refine h3.congr ?_
      filter_upwards with x
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have hgint : Integrable (fun x => Real.exp (f x₀) * (g x ^ 2 * Real.exp (-(f x))))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hg.const_mul (Real.exp (f x₀))
    have hbound : ∀ᵐ x ∂(volume.restrict K),
        ‖g x ^ 2‖ ≤ Real.exp (f x₀) * (g x ^ 2 * Real.exp (-(f x))) := by
      have hKm : MeasurableSet K := hK.measurableSet
      filter_upwards [ae_restrict_mem hKm] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g x))]
      have hfx : f x ≤ f x₀ := hmax hx
      have h1 : 1 ≤ Real.exp (f x₀ - f x) := Real.one_le_exp (sub_nonneg.mpr hfx)
      have hs : 0 ≤ g x ^ 2 := sq_nonneg _
      calc g x ^ 2 ≤ g x ^ 2 * Real.exp (f x₀ - f x) := le_mul_of_one_le_right hs h1
        _ = Real.exp (f x₀) * (g x ^ 2 * Real.exp (-(f x))) := by
              rw [sub_eq_add_neg, Real.exp_add]; ring
    exact (hgint.restrict).mono' (hmeas.restrict) hbound

end Commons.Analysis.GaussianMeasure