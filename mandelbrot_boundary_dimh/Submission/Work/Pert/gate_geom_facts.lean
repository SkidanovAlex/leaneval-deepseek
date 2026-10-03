import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

theorem gate_geom_facts {Ξ : ℝ} {α w : ℂ} (hα : MandelDim.InF1 α)
    (hw : w ∈ Work.Pert.Qm Ξ α) :
    0 < (1 / α).re ∧
      (1 / α).re + |(1 / α).im| ≤ 2 / ‖α‖ ∧
      w.re + |w.im + (1 / α).im| > Ξ - (1 / α).re ∧
      w.re + Ξ < |w.im| ∧
      0 < |w.im| - w.re - Ξ ∧
      (0 < w.im → |w.im| - w.re - Ξ ≤ 2 * w.im + ((1 / α).re + |(1 / α).im|) - 2 * Ξ) := by
  -- The two membership conditions defining the lower gate `Qm Ξ α`
  -- (`Qreg (Ξ - 1/α) (-Ξ)`), written in coordinates.
  have key3 : w.re + |w.im + (1 / α).im| > Ξ - (1 / α).re := by
    have h := hw.1 ((Ξ : ℂ) - 1 / α) (by simp)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] at h
    have e : w.im - (0 - (1 / α).im) = w.im + (1 / α).im := by ring
    rw [e] at h
    linarith [h]
  have key4 : w.re + Ξ < |w.im| := by
    have h := hw.2 (-(Ξ : ℂ)) (by simp)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im] at h
    have e : w.im - -0 = w.im := by ring
    rw [e] at h
    linarith [h]
  -- `0 < α.re` and `α ≠ 0`, hence `0 < ‖α‖²`.
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg (α.im)) hα
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hαre
    simp at hαre
  refine ⟨?_, ?_, key3, key4, by linarith, ?_⟩
  · -- `1/α` has positive real part: `(1/α).re = α.re / ‖α‖²`.
    have hn : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
    rw [one_div, Complex.inv_re]
    exact div_pos hαre hn
  · -- `(1/α).re + |(1/α).im| ≤ 2‖1/α‖ = 2/‖α‖`.
    have h1 : (1 / α).re ≤ ‖1 / α‖ := Complex.re_le_norm _
    have h2 : |(1 / α).im| ≤ ‖1 / α‖ := Complex.abs_im_le_norm _
    have h3 : ‖1 / α‖ = 1 / ‖α‖ := by rw [one_div, norm_inv, one_div]
    calc (1 / α).re + |(1 / α).im| ≤ ‖1 / α‖ + ‖1 / α‖ := add_le_add h1 h2
      _ = 2 / ‖α‖ := by rw [h3]; ring
  · -- The comparison at the upper end: `w.im - |w.im + (1/α).im| ≥ -|(1/α).im|`.
    intro hwim
    have hle : |w.im + (1 / α).im| ≤ w.im + |(1 / α).im| := by
      calc |w.im + (1 / α).im| ≤ |w.im| + |(1 / α).im| := abs_add_le _ _
        _ = w.im + |(1 / α).im| := by rw [abs_of_pos hwim]
    rw [abs_of_pos hwim]
    linarith

end Work.Pert
