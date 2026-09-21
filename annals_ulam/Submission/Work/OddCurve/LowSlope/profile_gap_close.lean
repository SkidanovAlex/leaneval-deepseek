import Mathlib
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddCurve.LowSlope.AnchorRadialClose
import Submission.Work.OddCurve.LowSlope.radial_gap_bound

/-!
# The profile gap on the perturbed window `(tStar, y (1 - 2τ))`

The envelope profile `f = envelopeProfile h X Y` is the semicircle outside the perturbed window,
but on the window `t ∈ (tStar, y (1 - 2τ))` the chord `t = Y σ` has slope `σ ∈ (1 - 2τ, 1 - τ)`
inside the support of the bump `h`, so `f t = σ * t + h σ`.  Comparing with the semicircle:
writing `σ₁ = √(1 - t²)/t` for the slope with `profileX σ₁ = t`, one has
`√(1 - t²) = σ₁ * t` and hence

  `f t - √(1 - t²) = (σ - σ₁) * t + h σ`.

The first term is controlled by the `C⁰`-closeness of `Y` to `profileX` together with the
*reverse Lipschitz bound* `|a - b| ≤ 3 |profileX a - profileX b|` valid on `[3/4, 9/10]`
(a mean-value-theorem consequence of `|profileX'| ≥ 1/3` there), the second by the bump bound
`|h s| ≤ ε`.  Since `t < 4/5` this gives `≤ (3/100) · (4/5) + ε = 3/125 + ε ≤ ε + 1/40`.

## Main results

* `deriv_profileX_eq` — the derivative of `profileX s = 1/√(1 + s²)`;
* `one_third_le_abs_deriv_profileX` — `|profileX'| ≥ 1/3` on `[3/4, 9/10]`;
* `abs_sub_le_three_abs_profileX_sub` — the reverse Lipschitz bound on `[3/4, 9/10]`;
* `profile_gap_close` — the gap bound on the perturbed window.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open Set
open scoped ContDiff

/-! ### The semicircle chord function -/

/-- The derivative of the semicircle chord function `profileX s = 1/√(1+s²)`. -/
lemma deriv_profileX_eq (s : ℝ) :
    deriv Work.OddEnvelope.profileX s
      = -(s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s := by
  have h1 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * s) s := by
    have h : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (deriv (fun u : ℝ => 1 + u ^ 2) s) s :=
      (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => 1 + u ^ 2) s).hasDerivAt
    rwa [show deriv (fun u : ℝ => 1 + u ^ 2) s = 2 * s from by simp] at h
  have h2 := h1.sqrt (show (1 : ℝ) + s ^ 2 ≠ 0 by positivity)
  have h3 := h2.inv (show Real.sqrt (1 + s ^ 2) ≠ 0 by positivity)
  have hfun : Work.OddEnvelope.profileX = (fun u : ℝ => Real.sqrt (1 + u ^ 2))⁻¹ := by
    funext u; rw [Work.OddEnvelope.profileX]; simp [one_div]
  rw [hfun, h3.deriv]
  simp only [Pi.inv_apply]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + s ^ 2)]
  field_simp

/-- `profileX` is smooth on the positive axis. -/
lemma contDiffOn_profileX_Ioi :
    ContDiffOn ℝ ∞ Work.OddEnvelope.profileX (Set.Ioi 0) := by
  unfold Work.OddEnvelope.profileX
  apply ContDiffOn.div
  · exact contDiffOn_const
  · apply ContDiffOn.sqrt
    · fun_prop
    · intro x hx; positivity
  · intro x hx; exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))

/-- On `[3/4, 9/10]` the derivative of `profileX` has modulus at least `1/3`. -/
lemma one_third_le_abs_deriv_profileX {s : ℝ} (h1 : 3 / 4 ≤ s) (h2 : s ≤ 9 / 10) :
    1 / 3 ≤ |deriv Work.OddEnvelope.profileX s| := by
  have hs0 : 0 < s := by linarith
  have hkey : 9 * s ^ 2 ≥ (1 + s ^ 2) ^ 3 := by
    have hs2le : s ^ 2 ≤ 81 / 100 := by nlinarith
    have hs2ge : 0 ≤ s ^ 2 := sq_nonneg s
    have hs4le : s ^ 4 ≤ (81 / 100) ^ 2 := by
      have h := pow_le_pow_left₀ hs2ge hs2le 2
      simpa [pow_succ, pow_two, mul_comm, mul_assoc, mul_left_comm] using h
    have h3 : 3 * s ^ 2 + s ^ 4 ≤ 30861 / 10000 := by nlinarith
    have h4 : 0 < s ^ 2 * (29139 / 10000) - 1 := by nlinarith
    have h5 : s ^ 2 * (3 * s ^ 2 + s ^ 4) ≤ s ^ 2 * (30861 / 10000) :=
      mul_le_mul_of_nonneg_left h3 hs2ge
    have heq : 9 * s ^ 2 - (1 + s ^ 2) ^ 3 = 6 * s ^ 2 - 1 - s ^ 2 * (3 * s ^ 2 + s ^ 4) := by
      ring
    rw [ge_iff_le, ← sub_nonneg, heq]
    linarith
  have hstep : |-(s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s|
      = (s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s := by
    rw [abs_mul, abs_neg, abs_of_pos (div_pos hs0 (by positivity)),
      abs_of_pos (Work.OddEnvelope.profileX_pos s)]
  rw [deriv_profileX_eq s, hstep]
  have ha2 : ((s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s) ^ 2
      = s ^ 2 / (1 + s ^ 2) ^ 3 := by
    rw [mul_pow, div_pow, Work.OddEnvelope.profileX_sq]
    field_simp
  have hb : (1 / 3 : ℝ) ^ 2 ≤ ((s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s) ^ 2 := by
    rw [ha2, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s ^ 2) ^ 3)]
    nlinarith [hkey]
  have hnn : 0 ≤ (s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s :=
    mul_nonneg (le_of_lt (div_pos hs0 (by positivity)))
      (le_of_lt (Work.OddEnvelope.profileX_pos s))
  have hsq := sq_le_sq.mp hb
  rwa [abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hsq

/-- **Reverse Lipschitz bound for `profileX` on `[3/4, 9/10]`**: the mean value theorem with
`|profileX'| ≥ 1/3` turns a bound on the *values* into a bound on the *arguments*. -/
lemma abs_sub_le_three_abs_profileX_sub {a b : ℝ} (ha : 3 / 4 ≤ a) (ha' : a ≤ 9 / 10)
    (hb : 3 / 4 ≤ b) (hb' : b ≤ 9 / 10) :
    |a - b| ≤ 3 * |Work.OddEnvelope.profileX a - Work.OddEnvelope.profileX b| := by
  have key : ∀ {u v : ℝ}, 3 / 4 ≤ u → v ≤ 9 / 10 → u < v →
      v - u ≤ 3 * |Work.OddEnvelope.profileX v - Work.OddEnvelope.profileX u| := by
    intro u v hu hv' huv
    have hcont : ContinuousOn Work.OddEnvelope.profileX (Set.Icc u v) :=
      contDiffOn_profileX_Ioi.continuousOn.mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < u) hx.1)
    have hdiff : DifferentiableOn ℝ Work.OddEnvelope.profileX (Set.Ioo u v) :=
      (contDiffOn_profileX_Ioi.differentiableOn (by simp)).mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < u) hx.1.le)
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope Work.OddEnvelope.profileX huv hcont hdiff
    have huv0 : 0 < v - u := by linarith
    have hd : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX ξ| :=
      one_third_le_abs_deriv_profileX (le_trans hu hξ.1.le) (le_trans hξ.2.le hv')
    have hmain : |Work.OddEnvelope.profileX v - Work.OddEnvelope.profileX u|
        = |deriv Work.OddEnvelope.profileX ξ| * (v - u) := by
      rw [hξeq, abs_div, abs_of_pos huv0, div_mul_cancel₀ _ (ne_of_gt huv0)]
    rw [hmain]; nlinarith [hd, huv0]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h := key ha hb' hlt
    rw [abs_of_neg (by linarith : a - b < 0), abs_sub_comm]
    linarith
  · rw [heq, sub_self, abs_zero]; positivity
  · have h := key hb ha' hgt
    rw [abs_of_pos (by linarith : (0 : ℝ) < a - b)]
    linarith

/-- `profileX (3/4) = 4/5`. -/
lemma profileX_three_quarters : Work.OddEnvelope.profileX (3 / 4) = 4 / 5 := by
  rw [Work.OddEnvelope.profileX, show (1 : ℝ) + (3 / 4) ^ 2 = (5 / 4) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  norm_num

/-- `profileX (4/5) ≤ 79/100`. -/
lemma profileX_four_fifths_le : Work.OddEnvelope.profileX (4 / 5) ≤ 79 / 100 := by
  have hs : (500 : ℝ) / 79 ≤ Real.sqrt 41 := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 500 / 79) (by norm_num : (0 : ℝ) ≤ 41)]
    norm_num
  have h79 : (0 : ℝ) < 79 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hs (le_of_lt h79)
  rw [mul_div_cancel₀] at hmul
  · rw [Work.OddEnvelope.profileX, show (1 : ℝ) + (4 / 5) ^ 2 = 41 / 25 by norm_num]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 41 / 25))]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 41)]
    have h25 : Real.sqrt (25 : ℝ) = 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
    rw [h25]
    have hcongr : (79 : ℝ) / 100 * (Real.sqrt 41 / 5) = 79 * Real.sqrt 41 / 500 := by ring
    rw [hcongr, le_div_iff₀ (by norm_num : (0 : ℝ) < 500)]
    linarith
  · norm_num

/-! ### The gap bound -/

theorem profile_gap_close {h X Y : ℝ → ℝ} {ε : ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hε0 : 0 ≤ ε)
    (hεb : ∀ s : ℝ, 1 - 2 * Work.OddCurve.tau ≤ s → s ≤ 1 - Work.OddCurve.tau → |h s| ≤ ε)
    (hcl : Work.OddCurve.LowSlope.CloseToProfileX Y)
    {t : ℝ} (ht : t ∈ Set.Ioo Work.OddEnvelope.tStar (Y (1 - 2 * Work.OddCurve.tau))) :
    |Work.OddEnvelope.envelopeProfile h X Y t - Real.sqrt (1 - t ^ 2)| ≤ ε + 1 / 40 := by
  have _ : 0 ≤ ε := hε0
  have hτ4 : (1 : ℝ) - 2 * Work.OddCurve.tau = 4 / 5 := Work.OddCurve.one_sub_two_tau_eq
  have hτ9 : (1 : ℝ) - Work.OddCurve.tau = 9 / 10 := Work.OddCurve.one_sub_tau_eq
  have htStar : Work.OddEnvelope.tStar < t := ht.1
  have htY : t < Y (1 - 2 * Work.OddCurve.tau) := ht.2
  -- `t < 4/5`
  have hYbound : Y (1 - 2 * Work.OddCurve.tau) ≤ Work.OddEnvelope.profileX (4 / 5) + 1 / 100 := by
    have hpos : (0 : ℝ) < 1 - 2 * Work.OddCurve.tau := by norm_num [Work.OddCurve.tau]
    have hh := (hcl _ hpos).1
    rw [hτ4] at hh ⊢
    linarith [(abs_le.mp hh).2]
  have ht45 : t < 4 / 5 := by
    have h := profileX_four_fifths_le
    linarith
  have ht0 : 0 < t := lt_trans Work.OddEnvelope.tStar_pos htStar
  have ht1 : t < 1 := by linarith
  have htI : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  -- the slope `σ` of the chord through `t`
  set σ : ℝ := Work.OddEnvelope.slopeRight Y t with hσdef
  have hYσ : Y σ = t := by
    rw [hσdef]
    exact H.toChordCurve_y.slopeRight_eq htI
  have hσpos : 0 < σ := by
    rw [hσdef]; exact H.toChordCurve_y.slopeRight_pos htI
  have hσgt' : 1 - 2 * Work.OddCurve.tau < σ := by
    have hpos : (0 : ℝ) < 1 - 2 * Work.OddCurve.tau := by norm_num [Work.OddCurve.tau]
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hh := H.toChordCurve_y.strictAntiOn hσpos hpos hlt
      rw [hYσ] at hh
      linarith [htY]
    · rw [heq] at hYσ
      linarith [htY, hYσ]
  have hσgt : 4 / 5 < σ := by rw [← hτ4]; exact hσgt'
  have hYtStar : Y (1 - Work.OddCurve.tau) = Work.OddEnvelope.tStar := by
    rw [Work.OddEnvelope.tStar]
    exact H.y_tail _ le_rfl
  have hσlt' : σ < 1 - Work.OddCurve.tau := by
    have hpos : (0 : ℝ) < 1 - Work.OddCurve.tau := by norm_num [Work.OddCurve.tau]
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hh := H.toChordCurve_y.strictAntiOn hpos hσpos hlt
      rw [hYσ, hYtStar] at hh
      linarith [htStar]
    · rw [← heq, hYtStar] at hYσ
      linarith [htStar, hYσ]
  have hσlt : σ < 9 / 10 := by rw [← hτ9]; exact hσlt'
  -- the slope `σ₁` with `profileX σ₁ = t`
  set σ₁ : ℝ := Real.sqrt (1 - t ^ 2) / t with hσ₁def
  have ht2 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hσ₁pos : 0 < σ₁ := by
    rw [hσ₁def]
    exact div_pos (Real.sqrt_pos.mpr ht2) ht0
  have hσ₁t : σ₁ * t = Real.sqrt (1 - t ^ 2) := by
    rw [hσ₁def]; field_simp
  have hprofXσ₁ : Work.OddEnvelope.profileX σ₁ = t := by
    have hsq : σ₁ ^ 2 = (1 - t ^ 2) / t ^ 2 := by
      rw [hσ₁def, div_pow, Real.sq_sqrt (le_of_lt ht2)]
    rw [Work.OddEnvelope.profileX,
      show (1 : ℝ) + σ₁ ^ 2 = (1 / t) ^ 2 by rw [hsq]; field_simp; ring,
      Real.sqrt_sq (le_of_lt (one_div_pos.mpr ht0))]
    field_simp
  have htStar9 : Work.OddEnvelope.profileX (9 / 10) = Work.OddEnvelope.tStar := by
    simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.tau]
    norm_num
  have hσ₁ge : 3 / 4 < σ₁ := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hh := Work.OddEnvelope.profileX_strictAntiOn hσ₁pos
        (by norm_num : (0 : ℝ) < 3 / 4) hlt
      rw [profileX_three_quarters, hprofXσ₁] at hh
      linarith [ht45]
    · rw [heq, profileX_three_quarters] at hprofXσ₁
      linarith [ht45]
  have hσ₁le : σ₁ < 9 / 10 := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hh := Work.OddEnvelope.profileX_strictAntiOn
        (by norm_num : (0 : ℝ) < 9 / 10) hσ₁pos hlt
      rw [hprofXσ₁, htStar9] at hh
      linarith [htStar]
    · rw [← heq, htStar9] at hprofXσ₁
      linarith [htStar, hprofXσ₁]
  -- assembling the bound
  have hf : Work.OddEnvelope.envelopeProfile h X Y t = σ * t + h σ := by
    rw [Work.OddEnvelope.envelopeProfile_of_pos htI, Work.OddEnvelope.envelopeRight, ← hσdef]
  have hprof_le : |Work.OddEnvelope.profileX σ - Work.OddEnvelope.profileX σ₁| ≤ 1 / 100 := by
    have hh := (hcl σ hσpos).1
    rw [hYσ, ← hprofXσ₁, abs_sub_comm] at hh
    exact hh
  have hdiff_le : |σ - σ₁| ≤ 3 / 100 := by
    have h := abs_sub_le_three_abs_profileX_sub
      (le_trans (by norm_num : (3 : ℝ) / 4 ≤ 4 / 5) (le_of_lt hσgt)) (le_of_lt hσlt)
      (le_of_lt hσ₁ge) (le_of_lt hσ₁le)
    linarith
  have hh_le : |h σ| ≤ ε :=
    hεb σ (by rw [hτ4]; exact le_of_lt hσgt) (by rw [hτ9]; exact le_of_lt hσlt)
  have htarget : |Work.OddEnvelope.envelopeProfile h X Y t - Real.sqrt (1 - t ^ 2)|
      ≤ |σ - σ₁| * t + |h σ| := by
    rw [hf, ← hσ₁t,
      show σ * t + h σ - σ₁ * t = (σ - σ₁) * t + h σ by ring]
    calc |(σ - σ₁) * t + h σ| ≤ |(σ - σ₁) * t| + |h σ| := abs_add_le _ _
      _ = |σ - σ₁| * t + |h σ| := by rw [abs_mul, abs_of_pos ht0]
  calc |Work.OddEnvelope.envelopeProfile h X Y t - Real.sqrt (1 - t ^ 2)|
      ≤ |σ - σ₁| * t + |h σ| := htarget
    _ ≤ (3 / 100) * t + ε := by
        have h1 : |σ - σ₁| * t ≤ (3 / 100) * t :=
          mul_le_mul_of_nonneg_right hdiff_le (le_of_lt ht0)
        linarith
    _ ≤ (3 / 100) * (4 / 5) + ε := by
        have h1 : (3 / 100) * t ≤ (3 / 100) * (4 / 5) :=
          mul_le_mul_of_nonneg_left (le_of_lt ht45) (by norm_num)
        linarith
    _ ≤ ε + 1 / 40 := by linarith

end

end Work.OddCurve.LowSlope
