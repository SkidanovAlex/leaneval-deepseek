import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_geom_facts

/-!
# The gate point at horizontal level `≥ 1` lies in the upper half plane

If `w` lies in the lower gate `Qm Ξ α` of §4.2 and the rotated point `α w` has imaginary
part `≥ 1`, then `Im w > 0`.  This is the elementary geometric fact behind the "high band"
analysis of the gate walk: the gate forces `w` to be far to the left of the vertex `-Ξ` of
the second cone, and `α` (with `|arg α| < π/4`) then pushes `α w` back to the right, so a
level `≥ 1` can only be reached with `Im w > 0`.
-/

namespace Work.Pert.GateDriftRate

theorem gate_high_im_pos {Ξ : ℝ} {α w : ℂ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hw : w ∈ Work.Pert.Qm Ξ α)
    (ht : 1 ≤ (α * w).im) : 0 < w.im := by
  -- `InF1 α` is by definition `|α.im| < α.re`.
  have hInF1' : |α.im| < α.re := hInF1
  by_contra hcon
  have hcon : w.im ≤ 0 := le_of_not_gt hcon
  -- the two defining inequalities of `Qm Ξ α`, in coordinates
  obtain ⟨-, -, key3, key4, -, -⟩ := Work.Pert.gate_geom_facts hInF1 hw
  have ha : 0 < α.re := lt_of_le_of_lt (abs_nonneg (α.im)) hInF1'
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hS : 0 < Complex.normSq α := Complex.normSq_pos.mpr hαne
  have habs : |w.im| = -w.im := abs_of_nonpos hcon
  have ht' : 1 ≤ α.re * w.im + α.im * w.re := by
    rw [Complex.mul_im] at ht
    exact ht
  rcases le_or_gt 0 α.im with hb | hb
  · -- `0 ≤ α.im`.  Then `α.re * w.im + α.im * (-w.im - Ξ) ≤ 0`, while it is `≥ 1`.
    have hab : α.im < α.re := by
      rw [abs_of_nonneg hb] at hInF1'
      exact hInF1'
    have h2 : w.re + Ξ < -w.im := by
      have h := key4; rw [habs] at h; exact h
    have hxle : w.re < -w.im - Ξ := by linarith
    have hstep : α.im * w.re ≤ α.im * (-w.im - Ξ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hxle) hb
    have hcomb : 1 ≤ w.im * (α.re - α.im) - α.im * Ξ := by
      have e : α.re * w.im + α.im * (-w.im - Ξ) = w.im * (α.re - α.im) - α.im * Ξ := by ring
      linarith [ht', hstep, e]
    have hneg : w.im * (α.re - α.im) - α.im * Ξ ≤ 0 := by
      have hA : (α.re - α.im) * w.im ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hcon
      have hB : 0 ≤ α.im * Ξ := mul_nonneg hb (le_of_lt hΞ)
      nlinarith [hA, hB]
    linarith
  · -- `α.im < 0`: write `α = α.re - i β`, `β > 0`.  The hypothesis gives
    -- `w.re ≤ (α.re * w.im - 1)/β`, the gate inequality gives a lower bound for `w.re`
    -- in terms of `|w.im + (1/α).im|`, and the elementary bound
    -- `α.re * s + β * |s + q| ≤ β * q` (`s ≤ 0`, `q = (1/α).im > 0`) closes the parenthesis.
    have hlt : -α.im < α.re := by
      rw [abs_of_neg hb] at hInF1'
      exact hInF1'
    set β : ℝ := -α.im with hβdef
    have hβ : 0 < β := by rw [hβdef]; linarith
    have hq : 0 < (1 / α).im := by
      rw [one_div, Complex.inv_im]
      apply div_pos
      · rw [hβdef] at hβ; linarith
      · exact hS
    have hkey : α.re * w.im + β * |w.im + (1 / α).im| ≤ β * (1 / α).im := by
      rcases le_or_gt 0 (w.im + (1 / α).im) with h | h
      · rw [abs_of_nonneg h]
        have hAB : 0 ≤ α.re + β := by rw [hβdef]; linarith
        have hwim : (α.re + β) * w.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hAB hcon
        nlinarith [hwim]
      · rw [abs_of_neg h]
        have hAB : 0 ≤ α.re - β := by rw [hβdef]; linarith
        have hwim : (α.re - β) * w.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hAB hcon
        have hbq : 0 ≤ β * (1 / α).im := mul_nonneg (le_of_lt hβ) (le_of_lt hq)
        nlinarith [hwim, hbq]
    have h1β : β * w.re ≤ α.re * w.im - 1 := by
      have h2 := ht'
      linarith [hβdef]
    have hstep : α.re * w.im - 1 + β * |w.im + (1 / α).im| > β * Ξ - β * (1 / α).re := by
      have hmul := mul_lt_mul_of_pos_left key3 hβ
      nlinarith [hmul, h1β]
    have hfin : β * (1 / α).im > 1 + β * Ξ - β * (1 / α).re := by
      linarith [hkey, hstep]
    -- the crux: `β * ((1/α).re + (1/α).im) = -α.re * (α.im + α.re) / ‖α‖² < 1`
    have hone : β * ((1 / α).re + (1 / α).im) < 1 := by
      have hsum : (1 / α).re + (1 / α).im = (α.re - α.im) / Complex.normSq α := by
        rw [one_div, Complex.inv_re, Complex.inv_im, sub_div]
        ring
      rw [hsum, ← mul_div_assoc, div_lt_one hS]
      rw [Complex.normSq_apply, hβdef]
      nlinarith [mul_lt_mul_of_pos_left hlt ha]
    have hbX : 0 < β * Ξ := mul_pos hβ hΞ
    have : 1 < β * ((1 / α).re + (1 / α).im) := by nlinarith [hfin, hbX]
    linarith

end Work.Pert.GateDriftRate
