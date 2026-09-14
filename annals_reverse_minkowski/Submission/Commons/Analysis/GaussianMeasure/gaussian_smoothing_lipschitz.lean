import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.mollified_infDist

open MeasureTheory Metric Filter Function Set
open scoped Topology ContDiff

namespace Commons.Analysis.GaussianMeasure

variable {m : ℕ}

/-- The total mass of the Gaussian kernel with variance `σ ^ 2` on `EuclideanSpace ℝ (Fin m)`. -/
lemma integral_exp_neg_norm_sq_div (σ : ℝ) (hσ : 0 < σ) :
    ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) =
      (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2) := by
  have h1 := MollifierAux.integral_gauss (n := m) (σ / Real.sqrt 2) (by positivity)
  have e1 : 4 * (σ / Real.sqrt 2) ^ 2 = 2 * σ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have e2 : 4 * Real.pi * (σ / Real.sqrt 2) ^ 2 = 2 * Real.pi * σ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  simpa only [e1, e2] using h1

/-- Integrability of the Gaussian kernel with variance `σ ^ 2`. -/
lemma integrable_exp_neg_norm_sq_div (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m) => Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
      (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
  simpa using MollifierAux.integrable_one_add_pow_gauss (n := m) σ hσ 0

/-- Translation change of variables for the Gaussian smoothing integral. -/
lemma integral_gauss_smoothing_shift (f : EuclideanSpace ℝ (Fin m) → ℝ) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    (∫ y, f y * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) =
      ∫ z, f (x - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) := by
  have h1 := integral_sub_left_eq_self
    (fun z : EuclideanSpace ℝ (Fin m) => f (x - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
    volume x
  simpa only [sub_sub_cancel] using h1

/-- The integral defining the Gaussian smoothing of a Lipschitz function is finite. -/
lemma integrable_gauss_smoothing_shift (f : EuclideanSpace ℝ (Fin m) → ℝ) (K : NNReal)
    (hf : LipschitzWith K f) (σ : ℝ) (hσ : 0 < σ) (w : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      f (w - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
      (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y, |f y| ≤ C * (1 + ‖y‖) := by
    refine ⟨|f 0| + (K : ℝ), fun y => ?_⟩
    have h1 : ‖f y - f 0‖ ≤ (K : ℝ) * ‖y - 0‖ := hf.norm_sub_le y 0
    rw [sub_zero, Real.norm_eq_abs] at h1
    have h2 : |f y| ≤ |f y - f 0| + |f 0| := by
      calc |f y| = |(f y - f 0) + f 0| := by rw [sub_add_cancel]
        _ ≤ |f y - f 0| + |f 0| := abs_add_le _ _
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hyn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    have h3 : (|f 0| + (K : ℝ)) * (1 + ‖y‖) = |f 0| + (K : ℝ) + |f 0| * ‖y‖ + (K : ℝ) * ‖y‖ := by
      ring
    nlinarith [h1, h2, hK0, hyn, abs_nonneg (f 0), h3]
  have h2 : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      (1 + ‖z‖) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
      (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    simpa using MollifierAux.integrable_one_add_pow_gauss (n := m) σ hσ 1
  refine Integrable.mono' (h2.const_mul (|C| * (1 + ‖w‖))) ?_ ?_
  · exact ((hf.continuous.comp (continuous_const.sub continuous_id)).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards with z
    have hz0 : (0 : ℝ) ≤ Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) := Real.exp_nonneg _
    have hfz : |f (w - z)| ≤ C * (1 + ‖w - z‖) := hC (w - z)
    have hwz : ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le w z
    have hCa : (0 : ℝ) ≤ |C| := abs_nonneg _
    have hstep : |f (w - z)| ≤ |C| * (1 + ‖w‖) * (1 + ‖z‖) := by
      refine hfz.trans ?_
      have h5 : (1 : ℝ) + ‖w - z‖ ≤ (1 + ‖w‖) * (1 + ‖z‖) := by
        nlinarith [hwz, norm_nonneg w, norm_nonneg z]
      calc C * (1 + ‖w - z‖) ≤ |C| * (1 + ‖w - z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((1 + ‖w‖) * (1 + ‖z‖)) := mul_le_mul_of_nonneg_left h5 hCa
        _ = |C| * (1 + ‖w‖) * (1 + ‖z‖) := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hz0]
    calc |f (w - z)| * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))
        ≤ (|C| * (1 + ‖w‖) * (1 + ‖z‖)) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) :=
          mul_le_mul_of_nonneg_right hstep hz0
      _ = (|C| * (1 + ‖w‖)) * ((1 + ‖z‖) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) := by ring

/-- The Gaussian smoothing
`x ↦ (2πσ²)^{-m/2} ∫ y, f y * exp(-‖x-y‖²/(2σ²))`
of a `K`-Lipschitz function is again `K`-Lipschitz (and smooth). -/
theorem gaussian_smoothing_lipschitz {m : ℕ} (K : NNReal)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : LipschitzWith K f)
    (σ : ℝ) (hσ : 0 < σ) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin m) =>
        (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) *
          ∫ y, f y * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)))
    ∧ LipschitzWith K (fun x : EuclideanSpace ℝ (Fin m) =>
        (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) *
          ∫ y, f y * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) := by
  have hπσ : (0 : ℝ) < 2 * Real.pi * σ ^ 2 := by positivity
  have hcpos : (0 : ℝ) < (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) :=
    Real.rpow_pos_of_pos hπσ _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y, |f y| ≤ C * (1 + ‖y‖) := by
    refine ⟨|f 0| + (K : ℝ), fun y => ?_⟩
    have h1 : ‖f y - f 0‖ ≤ (K : ℝ) * ‖y - 0‖ := hf.norm_sub_le y 0
    rw [sub_zero, Real.norm_eq_abs] at h1
    have h2 : |f y| ≤ |f y - f 0| + |f 0| := by
      calc |f y| = |(f y - f 0) + f 0| := by rw [sub_add_cancel]
        _ ≤ |f y - f 0| + |f 0| := abs_add_le _ _
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hyn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    have h3 : (|f 0| + (K : ℝ)) * (1 + ‖y‖) = |f 0| + (K : ℝ) + |f 0| * ‖y‖ + (K : ℝ) * ‖y‖ := by
      ring
    nlinarith [h1, h2, hK0, hyn, abs_nonneg (f 0), h3]
  refine ⟨?_, ?_⟩
  · have hCD : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin m) =>
        ∫ y, f y * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) :=
      MollifierAux.contDiff_top_gauss_smoothing σ hσ f hf.continuous C hC
    simpa using contDiff_const.mul hCD
  · have hKint : ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) =
        (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2) := integral_exp_neg_norm_sq_div σ hσ
    have hKi : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
        Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
      integrable_exp_neg_norm_sq_div σ hσ
    have hsub : ∀ x : EuclideanSpace ℝ (Fin m),
        (∫ y, f y * Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2))) =
          ∫ z, f (x - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) :=
      fun x => integral_gauss_smoothing_shift f σ x
    have hint : ∀ w : EuclideanSpace ℝ (Fin m),
        Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
          f (w - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
          (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
      fun w => integrable_gauss_smoothing_shift f K hf σ hσ w
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [dist_eq_norm, Real.norm_eq_abs]
    rw [hsub x, hsub y, ← mul_sub, abs_mul, abs_of_pos hcpos]
    have hdiff : (∫ z : EuclideanSpace ℝ (Fin m),
          f (x - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) -
        (∫ z, f (y - z) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))) =
        ∫ z, (f (x - z) - f (y - z)) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) := by
      rw [← integral_sub (hint x) (hint y)]
      apply integral_congr_ae
      filter_upwards with z
      ring
    rw [hdiff]
    have h2 : |∫ z, (f (x - z) - f (y - z)) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))| ≤
        ((K : ℝ) * ‖x - y‖) * (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2) := by
      have hb : ∀ z : EuclideanSpace ℝ (Fin m),
          ‖(f (x - z) - f (y - z)) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))‖ ≤
            ((K : ℝ) * ‖x - y‖) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) := by
        intro z
        have h3 : |f (x - z) - f (y - z)| ≤ (K : ℝ) * ‖x - y‖ := by
          have h4 := hf.norm_sub_le (x - z) (y - z)
          have h5 : (x - z) - (y - z) = x - y := by abel
          rw [Real.norm_eq_abs, h5] at h4
          exact h4
        have h6 : (0 : ℝ) ≤ Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)) := Real.exp_nonneg _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h6]
        exact mul_le_mul_of_nonneg_right h3 h6
      have hg : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
          ((K : ℝ) * ‖x - y‖) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2)))
          (volume : Measure (EuclideanSpace ℝ (Fin m))) := hKi.const_mul _
      have h7 := norm_integral_le_of_norm_le hg (Eventually.of_forall hb)
      rw [Real.norm_eq_abs, integral_const_mul, hKint] at h7
      exact h7
    calc (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) *
          |∫ z, (f (x - z) - f (y - z)) * Real.exp (-‖z‖ ^ 2 / (2 * σ ^ 2))|
        ≤ (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) *
            (((K : ℝ) * ‖x - y‖) * (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left h2 hcpos.le
      _ = (K : ℝ) * ‖x - y‖ := by
          rw [show (2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) *
                (((K : ℝ) * ‖x - y‖) * (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2)) =
              ((K : ℝ) * ‖x - y‖) *
                ((2 * Real.pi * σ ^ 2) ^ (-(m : ℝ) / 2) * (2 * Real.pi * σ ^ 2) ^ ((m : ℝ) / 2))
              by ring]
          rw [← Real.rpow_add hπσ, show (-(m : ℝ) / 2 + (m : ℝ) / 2) = 0 by ring,
            Real.rpow_zero, mul_one]

end Commons.Analysis.GaussianMeasure
