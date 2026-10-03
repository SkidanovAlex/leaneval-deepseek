import Mathlib

namespace Work.Pert.OmArc

/-- Under `|Im α| < Re α` and `2πη‖α‖ ≤ 1/64` (with `η > 0`), the quantity `Re(1/α) + |Im(1/α)|`
is at least `64πη`.  (Proof: `Re(1/α) + |Im(1/α)| = (Re α + |Im α|)/‖α‖² ≥ Re α/‖α‖² ≥ 1/(2‖α‖) ≥ 64πη`.) -/
theorem inv_bound {α : ℂ} {η : ℝ} (hη : 0 < η) (hF1 : |α.im| < α.re)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64) :
    64 * Real.pi * η ≤ (1 / α).re + |(1 / α).im| := by
  -- `|Im α| < Re α` forces `Re α > 0`, so `α ≠ 0` and `‖α‖ > 0`.
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg _) hF1
  have hne : α ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hnpos : 0 < ‖α‖ := norm_pos_iff.mpr hne
  -- hence `‖α‖ ≤ 2 Re α`.
  have hle : ‖α‖ ≤ 2 * α.re := by
    have h2 : ‖α‖ ^ 2 < (2 * α.re) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      rw [abs_lt] at hF1
      nlinarith [hF1.1, hF1.2]
    nlinarith [hnpos, hre, h2, norm_nonneg α]
  -- explicit form of the two summands.
  have e1 : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have e2 : |(1 / α).im| = |α.im| / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_im, abs_div, abs_neg, abs_of_nonneg (Complex.normSq_nonneg α),
      Complex.normSq_eq_norm_sq]
  -- `1/(2‖α‖) ≤ Re(1/α) + |Im(1/α)|`.
  have hA : 1 / (2 * ‖α‖) ≤ (1 / α).re + |(1 / α).im| := by
    rw [e1, e2]
    have h1 : 1 / (2 * ‖α‖) ≤ α.re / ‖α‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hle, hnpos]
    have h2 : 0 ≤ |α.im| / ‖α‖ ^ 2 := by positivity
    linarith
  -- and `2πη‖α‖ ≤ 1/64` gives `64πη ≤ 1/(2‖α‖)`.
  have hB : 64 * Real.pi * η ≤ 1 / (2 * ‖α‖) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ‖α‖)]
    nlinarith [hαη]
  linarith

end Work.Pert.OmArc
