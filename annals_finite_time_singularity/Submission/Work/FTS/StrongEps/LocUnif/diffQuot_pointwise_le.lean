import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.LocUnif.DiffQuotFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

open MeasureTheory Set

theorem diffQuot_pointwise_le {a b a' b' c d h C : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hh : 0 < h) (hah : h < a' - a) (hC : 1 ≤ C)
    {w : ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hw : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < w z θ)
    (hCw : ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |z - y| ≤ h → (w z θ) ^ 2 ≤ C * (w y θ) ^ 2)
    (hu_sm : ∀ θ ∈ Set.Icc c d, ContDiffOn ℝ 1 (fun z => u z θ) (Set.Ioo a b))
    {z θ : ℝ} (hz : z ∈ Set.Icc a' b') (hθ : θ ∈ Set.Icc c d) :
    ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
        ∫⁻ s in Set.Ioc 0 h,
          ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s)) ^ 2 * (w (z - s) θ) ^ 2) := by
  -- `z ∈ (a,b)` and `z - h ∈ (a,b)`; the whole closed interval `[z-h,z]` lies in `Ioo a b`.
  have hz_ab : z ∈ Set.Icc a b := ⟨by linarith [hz.1, haa'], by linarith [hz.2, hb'b]⟩
  have hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1, hah, hz.1], by linarith [hx.2, hb'b, hz.2]⟩
  -- Continuity of the `z`-derivative of the slice on the integration range.
  have hderiv_cont : ContinuousOn (deriv (fun z' => u z' θ)) (Set.Ioo a b) :=
    (hu_sm θ hθ).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont : ContinuousOn (fun s => deriv (fun z' => u z' θ) (z - s)) (Set.Ioc 0 h) := by
    have hmap : Set.MapsTo (fun s : ℝ => z - s) (Set.Ioc 0 h) (Set.Ioo a b) :=
      fun s hs => hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hcs : ContinuousOn (fun s : ℝ => z - s) (Set.Ioc 0 h) :=
      (continuous_const.sub continuous_id).continuousOn
    exact hderiv_cont.comp hcs hmap
  have hmeas : AEStronglyMeasurable (fun s => deriv (fun z' => u z' θ) (z - s))
      (MeasureTheory.volume.restrict (Set.Ioc 0 h)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  -- Fundamental theorem of calculus for the slice, backward difference.
  have hFTC : ∫ s in (0:ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ :=
    integral_deriv_slice_sub hh.le hsub (hu_sm θ hθ)
  -- Cauchy–Schwarz against the constant weight `1`.
  have hCS : ENNReal.ofReal ((u z θ - u (z - h) θ)^2)
      ≤ ENNReal.ofReal h *
        ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2) := by
    have h := ofReal_interval_integral_sq_le hh.le
      (fun s => deriv (fun z' => u z' θ) (z - s)) hmeas
    rw [hFTC, sub_zero] at h
    exact h
  -- Pointwise comparison of the weights, valid on `Ioc 0 h`.
  have hpb : ∀ s ∈ Set.Ioc 0 h,
      ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        ≤ ENNReal.ofReal C *
            ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
    intro s hs
    have hs_ab : z - s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [hz.1, hah, hs.2]
      · linarith [hz.2, hb'b, hs.1]
    have habs : |z - (z - s)| ≤ h := by
      rw [show z - (z - s) = s by ring, abs_of_pos hs.1]
      exact hs.2
    have hCw' : (w z θ)^2 ≤ C * (w (z - s) θ)^2 := hCw z hz_ab (z - s) hs_ab θ hθ habs
    have hCpos : 0 ≤ C := by linarith [hC]
    have hg2 : 0 ≤ (deriv (fun z' => u z' θ) (z - s))^2 := sq_nonneg _
    calc ENNReal.ofReal ((w z θ)^2) * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)
        = ENNReal.ofReal ((w z θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (C * ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [hCw', hg2])
      _ = ENNReal.ofReal C * ENNReal.ofReal ((w (z - s) θ)^2 * (deriv (fun z' => u z' θ) (z - s))^2) :=
          ENNReal.ofReal_mul hCpos
      _ = ENNReal.ofReal C * ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
          rw [mul_comm ((w (z - s) θ)^2) ((deriv (fun z' => u z' θ) (z - s))^2)]
  -- Integrate the pointwise comparison against the Cauchy–Schwarz weight.
  have hB : ENNReal.ofReal ((w z θ)^2) *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
      ≤ ENNReal.ofReal C *
        (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)) := by
    have hmono := setLIntegral_mono' (μ := volume) measurableSet_Ioc hpb
    rw [lintegral_const_mul' (ENNReal.ofReal ((w z θ)^2))
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)) ENNReal.ofReal_ne_top,
        lintegral_const_mul' (ENNReal.ofReal C)
          (fun s => ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2))
          ENNReal.ofReal_ne_top] at hmono
    exact hmono
  -- `ofReal` arithmetic for the squared difference quotient.
  have hcore : ENNReal.ofReal (((u z θ - u (z - h) θ)/h)^2)
      = ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ := by
    rw [show ((u z θ - u (z - h) θ)/h)^2
        = (u z θ - u (z - h) θ)^2 * (h⁻¹)^2 by ring]
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ h⁻¹),
        ENNReal.ofReal_inv_of_pos hh]
    ring
  have ht : ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top
  have h1 := mul_le_mul_of_nonneg_right hCS (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h2 := mul_le_mul_of_nonneg_right h1 (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  have h3 := mul_le_mul_of_nonneg_right h2 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal ((w z θ)^2))
  have h4 := mul_le_mul_of_nonneg_right hB (zero_le : (0 : ENNReal) ≤ (ENNReal.ofReal h)⁻¹)
  calc ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2 * (w z θ) ^ 2)
      = ENNReal.ofReal (((u z θ - u (z - h) θ) / h) ^ 2) * ENNReal.ofReal ((w z θ)^2) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ = (ENNReal.ofReal ((u z θ - u (z - h) θ)^2) * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹)
          * ENNReal.ofReal ((w z θ)^2) := by rw [hcore]
    _ ≤ (ENNReal.ofReal h * (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
          * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2) := h3
    _ = ENNReal.ofReal ((w z θ)^2) *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
          * (ENNReal.ofReal h)⁻¹ := by
        rw [show (ENNReal.ofReal h * (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2)))
              * (ENNReal.ofReal h)⁻¹ * (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal ((w z θ)^2)
            = (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2))
              * (ENNReal.ofReal h * (ENNReal.ofReal h)⁻¹) * (ENNReal.ofReal h)⁻¹
              * ENNReal.ofReal ((w z θ)^2) from by ring]
        rw [ht]; ring
    _ ≤ (ENNReal.ofReal C *
          (∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2)))
          * (ENNReal.ofReal h)⁻¹ := h4
    _ = ENNReal.ofReal C * (ENNReal.ofReal h)⁻¹ *
          ∫⁻ s in Set.Ioc 0 h, ENNReal.ofReal ((deriv (fun z' => u z' θ) (z - s))^2 * (w (z - s) θ)^2) := by
        ring

end Work.FTS.StrongEps.LocUnif
