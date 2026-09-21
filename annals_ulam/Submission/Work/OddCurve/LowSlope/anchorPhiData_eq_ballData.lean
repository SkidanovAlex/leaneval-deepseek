import Mathlib
import Submission.Work.OddCurve.LowSlope.chord_eq_radial
import Submission.Work.OddCurve.LowSlope.anchor_junction
import Submission.Work.OddCurve.LowSlope.anchorRadonData
import Submission.Work.OddCurve.LowSlope.integrableOn_rpow_sub_left
import Submission.Work.OddCurve.LowSlope.integrableOn_rpow_sub_right

/-!
# The junction identity for the anchor's *Radon* datum (`Work.OddCurve.LowSlope`)

`anchorPhiData_eq_ballData` is the "Route R" form of the junction of the low-slope pipeline: on a
slope range where the bump `h` vanishes together with its derivative and where the anchor curve
`(X,Y)` (with profile `f = envelopeProfile h X Y`) satisfies the two moment equations with the
*ball's* constants, the spherical-Radon datum of the anchor body,

    `𝓡 (w ↦ w_1² ρ(w)^{2n+2})` at the normal of slope `s` (`ρ` the radial function of `f`),

equals the ball's datum `𝓡 (w ↦ w_1²)` there.  This is what makes the piecewise datum function of
the construction (`φ_new = φ_anchor` on the cap, the ball's below) smooth: the anchor's datum *is*
the ball's on the whole overlap window.

The proof assembles three ingredients already in the workspace:

* `envelope_chord_eq_radial` — on a slope where `h s = 0` the chord endpoints are the radial points
  `X s = ρ(-c)·c`, `Y s = ρ(c)·c`, `c = (√(1+s²))⁻¹` (strict concavity of the profile gives the
  uniqueness of the two roots, which is all this needs);
* `anchorRadonData` (Prop. `workHARD1` in one dimension) — the Radon datum is
  `(2n+2)|B^{2n-1}|√(1+s²)` times the chord inertia integral;
* `anchorPhi_eq_ballData` (Lemma 4.2 forward + the ball's reference identity
  `radonProfile_data_semicircle`) — the chord inertia integral *is* the ball's datum.

The only hypothesis of `anchorRadonData` that is not immediate from the statement is the
interval-integrability of the two singular chord integrands (`hint1`, `hint2`) — the integrands
carry a possible `1/√(f² - s²t²)` singularity at the two ends of the chord.  `hint2` is continuous
on the closed chord, and `hint1` is handled by `rad0_hint1_aux` below: for a concave profile the
radicand vanishes *linearly* at both ends of the chord (the chord bounds `rad0_lower_left`,
`rad0_lower_right`, obtained from the concavity inequalities), so the exponent `-1/2` is
integrable.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## Integrability of the singular chord integrand -/

private lemma concaveOn_chord {u : ℝ → ℝ} {α β : ℝ} (hαβ : α < β)
    (h : ConcaveOn ℝ (Set.Icc α β) u) {t : ℝ} (ht : t ∈ Set.Icc α β) :
    ((β - t) / (β - α)) * u α + ((t - α) / (β - α)) * u β ≤ u t := by
  have hqa : 0 ≤ (β - t) / (β - α) := div_nonneg (by linarith [ht.2]) (by linarith)
  have hra : 0 ≤ (t - α) / (β - α) := div_nonneg (by linarith [ht.1]) (by linarith)
  have hqr : (β - t) / (β - α) + (t - α) / (β - α) = 1 := by
    rw [← add_div, show (β - t) + (t - α) = β - α by ring,
      div_self (ne_of_gt (sub_pos.mpr hαβ))]
  have hcombo : (β - t) / (β - α) * α + (t - α) / (β - α) * β = t := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff (ne_of_gt (sub_pos.mpr hαβ))]
    ring
  have hchord := h.2 ⟨le_refl α, hαβ.le⟩ ⟨hαβ.le, le_refl β⟩ hqa hra hqr
  simp only [smul_eq_mul, hcombo] at hchord
  exact hchord

private lemma rad0_lower_left {f : ℝ → ℝ} {s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hconc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f) (hx1 : x < 1)
    (hf0 : f 0 = 1) (hrootm : f (-x) = s * x) :
    ∀ t ∈ Set.Ioo (-x) 0, (min (s * x) 1 / x) * (t + x) ≤ rad0 f s t := by
  intro t ht
  have hsub : Set.Icc (-x) 0 ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.1, hx1], by linarith [hu.2]⟩
  have hc : ConcaveOn ℝ (Set.Icc (-x) 0) f := hconc.subset hsub (convex_Icc _ _)
  have htIcc : t ∈ Set.Icc (-x) 0 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hchord := concaveOn_chord (u := f) (α := -x) (β := 0) (by linarith) hc htIcc
  rw [hrootm, hf0] at hchord
  have hd : (0 : ℝ) - (-x) = x := by ring
  rw [hd] at hchord
  have hft : -s * t + (t + x) / x ≤ f t := by
    have heq : ((0 - t) / x) * (s * x) + ((t - (-x)) / x) * 1 = -s * t + (t + x) / x := by
      rw [sub_neg_eq_add]; field_simp; ring
    linarith [hchord, heq]
  have hsum1 : (t + x) / x ≤ f t + s * t := by linarith
  have hst : s * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) (le_of_lt ht.2)
  have hmin : min (s * x) 1 ≤ f t - s * t := by
    have hw1 : 0 ≤ (0 - t) / x := div_nonneg (by linarith [ht.2]) (le_of_lt hx)
    have hw2 : 0 ≤ (t - (-x)) / x := div_nonneg (by linarith [ht.1]) (le_of_lt hx)
    have hw : (0 - t) / x + (t - (-x)) / x = 1 := by
      rw [← add_div, show (0 - t) + (t - (-x)) = x by ring, div_self (ne_of_gt hx)]
    have hcombo : min (s * x) 1 ≤ ((0 - t)/x) * (s * x) + ((t - (-x))/x) * 1 := by
      have := Convex.min_le_combo (s * x) 1 hw1 hw2 hw
      simpa [smul_eq_mul] using this
    have heq : ((0 - t) / x) * (s * x) + ((t - (-x)) / x) * 1 = -s * t + (t + x) / x := by
      rw [sub_neg_eq_add]; field_simp; ring
    linarith [hchord, hcombo, heq, hst]
  have hx0 : 0 < t + x := by linarith [ht.1]
  have hminpos : 0 < min (s * x) 1 := lt_min (mul_pos hs hx) one_pos
  have hmul : (min (s * x) 1) * ((t + x)/x) ≤ (f t - s * t) * (f t + s * t) :=
    mul_le_mul hmin hsum1 (div_nonneg (le_of_lt hx0) (le_of_lt hx))
      (by linarith [hmin, hminpos])
  have hR : rad0 f s t = (f t - s * t) * (f t + s * t) := by simp [rad0]; ring
  rw [hR]
  have heq2 : (min (s * x) 1 / x) * (t + x) = (min (s * x) 1) * ((t + x)/x) := by ring_nf
  rw [heq2]
  exact hmul

private lemma rad0_lower_right {f : ℝ → ℝ} {s y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hconc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f) (hy1 : y < 1)
    (hf0 : f 0 = 1) (hroot : f y = s * y) :
    ∀ t ∈ Set.Ioo 0 y, (min 1 (s * y) / y) * (y - t) ≤ rad0 f s t := by
  intro t ht
  have hsub : Set.Icc 0 y ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2, hy1]⟩
  have hc : ConcaveOn ℝ (Set.Icc 0 y) f := hconc.subset hsub (convex_Icc _ _)
  have htIcc : t ∈ Set.Icc 0 y := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hchord := concaveOn_chord (u := f) (α := 0) (β := y) (by linarith) hc htIcc
  rw [hf0, hroot] at hchord
  have hd : y - (0 : ℝ) = y := by ring
  rw [hd] at hchord
  have hft : s * t + (y - t) / y ≤ f t := by
    have heq : ((y - t) / y) * 1 + ((t - 0) / y) * (s * y) = s * t + (y - t) / y := by
      field_simp; ring
    linarith [hchord, heq]
  have h1 : (y - t) / y ≤ f t - s * t := by linarith
  have hst : 0 ≤ s * t := mul_nonneg (le_of_lt hs) (le_of_lt ht.1)
  have hmin : min 1 (s * y) ≤ f t + s * t := by
    have hw1 : 0 ≤ (y - t) / y := div_nonneg (by linarith [ht.2]) (le_of_lt hy)
    have hw2 : 0 ≤ (t - 0) / y := div_nonneg (by linarith [ht.1]) (le_of_lt hy)
    have hw : (y - t) / y + (t - 0) / y = 1 := by
      rw [← add_div, show (y - t) + (t - 0) = y by ring, div_self (ne_of_gt hy)]
    have hcombo : min 1 (s * y) ≤ ((y - t)/y) * 1 + ((t - 0)/y) * (s * y) := by
      have := Convex.min_le_combo (1 : ℝ) (s * y) hw1 hw2 hw
      simpa [smul_eq_mul] using this
    have heq : ((y - t) / y) * 1 + ((t - 0) / y) * (s * y) = s * t + (y - t) / y := by
      field_simp; ring
    linarith [hchord, hcombo, heq, hst]
  have hy0 : 0 < y - t := by linarith [ht.2]
  have hminpos : 0 < min 1 (s * y) := lt_min one_pos (mul_pos hs hy)
  have hmul : (min 1 (s * y)) * ((y - t)/y) ≤ (f t + s * t) * (f t - s * t) :=
    mul_le_mul hmin h1 (div_nonneg (le_of_lt hy0) (le_of_lt hy))
      (by linarith [hmin, hminpos])
  have hR : rad0 f s t = (f t + s * t) * (f t - s * t) := by simp [rad0]; ring
  rw [hR]
  have heq2 : (min 1 (s * y) / y) * (y - t) = (min 1 (s * y)) * ((y - t)/y) := by ring_nf
  rw [heq2]
  exact hmul


/-- **Integrability of the singular chord integrand.**  For a concave profile with
`f 0 = 1`, `f y = s y`, `f (-x) = s x` (`x, y ∈ (0,1)`), the inertia integrand
`t² f (f - t f') (f² - s²t²)^{n-1} / √(f² - s²t²)` is interval integrable over the chord
`(-x, y)`: the only singularity is at the two ends of the chord, where the radicand vanishes
linearly, so it is integrable (this is exactly the `hint1` hypothesis of `anchorRadonData`). -/
private lemma rad0_hint1_aux (n : ℕ) {f : ℝ → ℝ} {s x y : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hy : 0 < y) (hx1 : x < 1) (hy1 : y < 1)
    (hconc : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f)
    (hf_cont : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hd_cont : ContinuousOn (deriv f) (Set.Icc (-x) y))
    (hf0 : f 0 = 1) (hroot : f y = s * y) (hrootm : f (-x) = s * x) :
    IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-x) y := by
  have hbL := rad0_lower_left (f := f) (s := s) (x := x) hs hx hconc hx1 hf0 hrootm
  have hbR := rad0_lower_right (f := f) (s := s) (y := y) hs hy hconc hy1 hf0 hroot
  have hcLpos : 0 < min (s * x) 1 / x := div_pos (lt_min (mul_pos hs hx) one_pos) hx
  have hcRpos : 0 < min 1 (s * y) / y := div_pos (lt_min one_pos (mul_pos hs hy)) hy
  have hRpos : ∀ t ∈ Set.Ioo (-x) y, 0 < rad0 f s t := by
    intro t ht
    rcases lt_trichotomy t 0 with h | h | h
    · have h1 := hbL t ⟨ht.1, h⟩
      nlinarith [h1, hcLpos, ht.1]
    · subst h
      rw [rad0]; simp [hf0]
    · have h1 := hbR t ⟨h, ht.2⟩
      nlinarith [h1, hcRpos, ht.2]
  have hsubIcc : Set.Icc (-x) y ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun u hu => ⟨by linarith [hu.1, hx1], by linarith [hu.2, hy1]⟩
  have hsubO : Set.Ioo (-x) y ⊆ Set.Icc (-x) y := fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hfc : ContinuousOn f (Set.Icc (-x) y) := hf_cont.mono hsubIcc
  have hRc : ContinuousOn (fun t : ℝ => rad0 f s t) (Set.Icc (-x) y) := by
    have h1 : ContinuousOn (fun t : ℝ => f t ^ 2 - (s * t) ^ 2) (Set.Icc (-x) y) :=
      (hfc.pow 2).sub ((continuous_const.mul continuous_id).continuousOn.pow 2)
    exact h1.congr (fun t _ => by simp [rad0])
  have hgc : ContinuousOn (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t))
      (Set.Icc (-x) y) :=
    ((continuous_id.pow 2).continuousOn.mul hfc).mul
      (hfc.sub (continuous_id.continuousOn.mul hd_cont))
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hRc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have hM'nn : 0 ≤ max C₁ 0 := le_max_right _ _
  have hMnn : 0 ≤ max C₂ 0 := le_max_right _ _
  have hRle : ∀ t ∈ Set.Ioo (-x) y, rad0 f s t ≤ max C₁ 0 := by
    intro t ht
    have h := hC₁ t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_trans (le_abs_self _) h) (le_max_left _ _)
  have hgle : ∀ t ∈ Set.Ioo (-x) y, |t ^ 2 * f t * (f t - t * deriv f t)| ≤ max C₂ 0 := by
    intro t ht
    have h := hC₂ t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hcontA : ContinuousOn (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) (Set.Ioo (-x) y) := by
    have hnum : ContinuousOn (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1)) (Set.Ioo (-x) y) :=
      (hgc.mono hsubO).mul ((hRc.mono hsubO).pow (n - 1))
    exact hnum.div (Real.continuous_sqrt.comp_continuousOn (hRc.mono hsubO))
      (fun t ht => ne_of_gt (Real.sqrt_pos.mpr (hRpos t ht)))
  set KL : ℝ := max C₂ 0 * (max C₁ 0) ^ (n - 1) * (Real.sqrt (min (s * x) 1 / x))⁻¹ with hKL
  set KR : ℝ := max C₂ 0 * (max C₁ 0) ^ (n - 1) * (Real.sqrt (min 1 (s * y) / y))⁻¹ with hKR
  have hIntL : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-x) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : -x ≤ 0)]
    have hAesm : AEStronglyMeasurable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
        (volume.restrict (Set.Ioo (-x) 0)) :=
      (hcontA.mono (fun t ht => ⟨ht.1, by linarith [ht.2, hy]⟩)).aestronglyMeasurable
        measurableSet_Ioo
    have hdom : Integrable (fun t : ℝ => KL * (Real.sqrt (t + x))⁻¹)
        (volume.restrict (Set.Ioo (-x) 0)) := by
      have h1 : Integrable (fun t : ℝ => (t - (-x)) ^ (-(1 / 2) : ℝ))
          (volume.restrict (Set.Ioo (-x) 0)) :=
        integrableOn_rpow_sub_left (a := -x) (b := 0) (p := -(1 / 2)) (by linarith) (by norm_num)
      refine MeasureTheory.IntegrableOn.congr_fun (s := Set.Ioo (-x) 0) (μ := volume)
        (h1.const_mul KL) ?_ measurableSet_Ioo
      intro t ht
      rw [Set.mem_Ioo] at ht
      have htx : 0 < t + x := by linarith [ht.1]
      change KL * (t - (-x)) ^ (-(1 / 2) : ℝ) = KL * (Real.sqrt (t + x))⁻¹
      rw [show t - (-x) = t + x by ring, Real.sqrt_eq_rpow,
        ← Real.rpow_neg (le_of_lt htx) (1 / 2 : ℝ)]
    refine Integrable.mono' hdom hAesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htx : 0 < t + x := by linarith [ht.1]
    have hty : t < y := by linarith [ht.2, hy]
    have htI : t ∈ Set.Ioo (-x) y := ⟨ht.1, hty⟩
    have hRt : 0 < rad0 f s t := hRpos t htI
    have hsqrtR : 0 < Real.sqrt (rad0 f s t) := Real.sqrt_pos.mpr hRt
    have hRge : min (s * x) 1 / x * (t + x) ≤ rad0 f s t := hbL t ⟨ht.1, ht.2⟩
    have hcLtx : 0 < min (s * x) 1 / x * (t + x) := mul_pos hcLpos htx
    have hsqrtc : 0 < Real.sqrt (min (s * x) 1 / x * (t + x)) := Real.sqrt_pos.mpr hcLtx
    have hinv : (Real.sqrt (rad0 f s t))⁻¹ ≤ (Real.sqrt (min (s * x) 1 / x * (t + x)))⁻¹ :=
      (inv_le_inv₀ hsqrtR hsqrtc).mpr (Real.sqrt_le_sqrt hRge)
    have hquot : rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t) ≤
        (max C₁ 0) ^ (n - 1) / Real.sqrt (min (s * x) 1 / x * (t + x)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (le_of_lt hRt) (hRle t htI) _) hinv
        (le_of_lt (inv_pos.mpr hsqrtR)) (pow_nonneg hM'nn _)
    calc ‖t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)‖
        = |t ^ 2 * f t * (f t - t * deriv f t)| *
            (rad0 f s t ^ (n - 1) * (Real.sqrt (rad0 f s t))⁻¹) := by
          rw [Real.norm_eq_abs, abs_div, abs_mul,
            abs_of_nonneg (pow_nonneg (le_of_lt hRt) _), abs_of_pos hsqrtR, div_eq_mul_inv]
          ring
      _ ≤ max C₂ 0 * ((max C₁ 0) ^ (n - 1) *
            (Real.sqrt (min (s * x) 1 / x * (t + x)))⁻¹) := by
          refine mul_le_mul (hgle t htI) hquot (le_of_lt ?_) hMnn
          exact mul_pos (pow_pos hRt (n - 1)) (inv_pos.mpr hsqrtR)
      _ = KL * (Real.sqrt (t + x))⁻¹ := by
          rw [hKL, Real.sqrt_mul (le_of_lt hcLpos), mul_inv]
          ring
  have hIntR : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume 0 y := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : (0 : ℝ) ≤ y)]
    have hAesm : AEStronglyMeasurable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t))
        (volume.restrict (Set.Ioo 0 y)) :=
      (hcontA.mono (fun t ht => ⟨by linarith [ht.1, hx], ht.2⟩)).aestronglyMeasurable
        measurableSet_Ioo
    have hdom : Integrable (fun t : ℝ => KR * (Real.sqrt (y - t))⁻¹)
        (volume.restrict (Set.Ioo 0 y)) := by
      have h1 : Integrable (fun t : ℝ => (y - t) ^ (-(1 / 2) : ℝ))
          (volume.restrict (Set.Ioo 0 y)) :=
        integrableOn_rpow_sub_right (a := 0) (b := y) (p := -(1 / 2)) (by linarith) (by norm_num)
      refine MeasureTheory.IntegrableOn.congr_fun (s := Set.Ioo 0 y) (μ := volume)
        (h1.const_mul KR) ?_ measurableSet_Ioo
      intro t ht
      rw [Set.mem_Ioo] at ht
      have hyt : 0 < y - t := by linarith [ht.2]
      change KR * (y - t) ^ (-(1 / 2) : ℝ) = KR * (Real.sqrt (y - t))⁻¹
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hyt) (1 / 2 : ℝ)]
    refine Integrable.mono' hdom hAesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have htI : t ∈ Set.Ioo (-x) y := ⟨by linarith [ht.1, hx], ht.2⟩
    have hRt : 0 < rad0 f s t := hRpos t htI
    have hsqrtR : 0 < Real.sqrt (rad0 f s t) := Real.sqrt_pos.mpr hRt
    have hRge : min 1 (s * y) / y * (y - t) ≤ rad0 f s t := hbR t ht
    have hcRyt : 0 < min 1 (s * y) / y * (y - t) := mul_pos hcRpos (by linarith [ht.2])
    have hsqrtc : 0 < Real.sqrt (min 1 (s * y) / y * (y - t)) := Real.sqrt_pos.mpr hcRyt
    have hinv : (Real.sqrt (rad0 f s t))⁻¹ ≤ (Real.sqrt (min 1 (s * y) / y * (y - t)))⁻¹ :=
      (inv_le_inv₀ hsqrtR hsqrtc).mpr (Real.sqrt_le_sqrt hRge)
    have hquot : rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t) ≤
        (max C₁ 0) ^ (n - 1) / Real.sqrt (min 1 (s * y) / y * (y - t)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (le_of_lt hRt) (hRle t htI) _) hinv
        (le_of_lt (inv_pos.mpr hsqrtR)) (pow_nonneg hM'nn _)
    calc ‖t ^ 2 * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
            Real.sqrt (rad0 f s t)‖
        = |t ^ 2 * f t * (f t - t * deriv f t)| *
            (rad0 f s t ^ (n - 1) * (Real.sqrt (rad0 f s t))⁻¹) := by
          rw [Real.norm_eq_abs, abs_div, abs_mul,
            abs_of_nonneg (pow_nonneg (le_of_lt hRt) _), abs_of_pos hsqrtR, div_eq_mul_inv]
          ring
      _ ≤ max C₂ 0 * ((max C₁ 0) ^ (n - 1) *
            (Real.sqrt (min 1 (s * y) / y * (y - t)))⁻¹) := by
          refine mul_le_mul (hgle t htI) hquot (le_of_lt ?_) hMnn
          exact mul_pos (pow_pos hRt (n - 1)) (inv_pos.mpr hsqrtR)
      _ = KR * (Real.sqrt (y - t))⁻¹ := by
          rw [hKR, Real.sqrt_mul (le_of_lt hcRpos), mul_inv]
          ring
  exact hIntL.trans hIntR

/-- The target of this file: on a range where the bump `h` vanishes with its derivative and where
the anchor curve satisfies the two moment equations with the ball's constants, the anchor's Radon
datum is the ball's datum. -/
theorem anchorPhiData_eq_ballData (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0)
    (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hA : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ s ∈ Set.Ioo a b,
      Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2))
          ((Real.sqrt (1 + s ^ 2))⁻¹) =
        Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2)
          ((Real.sqrt (1 + s ^ 2))⁻¹) := by
  intro s hs
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hsIcc : s ∈ Set.Icc a b := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hs' : 0 < s := lt_trans ha hs.1
  have hz : h s = 0 := hzero s hsIcc
  have hdz : deriv h s = 0 := hder0 s hsIcc
  set f : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h X Y with hf
  have hchord := envelope_chord_eq_radial (h := h) (X := X) (Y := Y) (ρ := ρ) H hs' hz hρpos
    hgraph
  have hYeq : Y s = ρ c * c := by rw [hc]; exact hchord.1
  have hXeq : X s = ρ (-c) * c := by rw [hc]; exact hchord.2
  have hYmem : Y s ∈ Set.Ioo (0 : ℝ) 1 := ⟨H.toChordCurve_y.pos hs', H.toChordCurve_y.lt_one hs'⟩
  have hXmem : X s ∈ Set.Ioo (0 : ℝ) 1 := ⟨H.toChordCurve_x.pos hs', H.toChordCurve_x.lt_one hs'⟩
  have hf0 : f 0 = 1 := by rw [hf]; exact Work.OddEnvelope.envelopeProfile_zero
  have hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f := by
    rw [hf]; exact Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hfY : f (Y s) = s * Y s := by
    rw [hf, Work.OddEnvelope.envelopeProfile_root_right H hs', hz]; ring
  have hfmX : f (-(X s)) = -(s * (-(X s))) := by
    rw [hf, Work.OddEnvelope.envelopeProfile_root_left H hs', hz]; ring
  have hrootR : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = ρ c * c := by
    have ha' : ρ c * c ∈ Set.Ioo (0 : ℝ) 1 := by rw [← hYeq]; exact hYmem
    have hfa : f (ρ c * c) = s * (ρ c * c) := by rw [← hYeq]; exact hfY
    exact eq_linear_unique_pos hconc hf0 ha' hfa
  have hrootL : ∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(ρ (-c) * c) := by
    have ha' : -(ρ (-c) * c) ∈ Set.Ioo (-1 : ℝ) 0 := by
      rw [← hXeq]; exact ⟨by linarith [hXmem.2], by linarith [hXmem.1]⟩
    have hfa : f (-(ρ (-c) * c)) = -(s * (-(ρ (-c) * c))) := by rw [← hXeq]; exact hfmX
    exact eq_linear_unique_neg hconc hf0 ha' hfa
  have hbound : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    have hspos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2])
    have hfu : f (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) := by
      rw [hf]; exact (hgraph u hu).symm
    have hne : f (ρ u * u) ≠ 0 := by
      rw [hfu]; exact ne_of_gt (mul_pos (hρpos u hu) hspos)
    have hsupp : Function.support f ⊆ Set.Icc (-1 : ℝ) 1 := by
      rw [hf]; exact Work.OddEnvelope.envelopeProfile_support
    have hIcc : ρ u * u ∈ Set.Icc (-1 : ℝ) 1 := hsupp (Function.mem_support.mpr hne)
    have hne1 : f 1 = 0 := by rw [hf]; exact Work.OddEnvelope.envelopeProfile_right_end
    have hnem1 : f (-1) = 0 := by rw [hf]; exact Work.OddEnvelope.envelopeProfile_left_end
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hIcc.1 with hq | hq
      · exfalso
        rw [← hq, hnem1] at hfu
        exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
      · exact hq
    · rcases eq_or_lt_of_le hIcc.2 with hq | hq
      · exfalso
        rw [hq, hne1] at hfu
        exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
      · exact hq
  have hrad : ∀ t ∈ Set.Ioo (-(ρ (-c) * c)) (ρ c * c), 0 < rad0 f s t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-(X s)) (Y s) := by rw [hXeq, hYeq]; exact ht
    have hpos := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
      (Work.OddEnvelope.concaveOn_envelopeProfile H) hs' t ht'
    rw [hz, add_zero] at hpos
    rwa [rad0, hf]
  have hf_c : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
    rw [hf]; exact Work.OddEnvelope.continuousOn_envelopeProfile' H
  have hf_sm : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) := by
    rw [hf]; exact (Work.OddEnvelope.envelopeProfile_contDiffOn H).of_le (by simp)
  have hd_cont : ContinuousOn (deriv f) (Set.Icc (-(X s)) (Y s)) := by
    have h1 : ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
      hf_sm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    refine h1.mono ?_
    intro u hu
    exact ⟨by linarith [hu.1, hXmem.2], by linarith [hu.2, hYmem.2]⟩
  have ha1 : -1 < -(ρ (-c) * c) := by rw [← hXeq]; linarith [hXmem.2]
  have hb1 : ρ c * c < 1 := by rw [← hYeq]; exact hYmem.2
  have hab' : -(ρ (-c) * c) < ρ c * c := by
    rw [← hXeq, ← hYeq]; linarith [hXmem.1, hYmem.1]
  have hint2 : IntervalIntegrable (fun t : ℝ => t ^ 2 * rad0 f s t ^ (n - 1) *
      Real.sqrt (rad0 f s t)) volume (-(ρ (-c) * c)) (ρ c * c) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab'.le]
    have hcontf : ContinuousOn f (Set.Icc (-(ρ (-c) * c)) (ρ c * c)) :=
      hf_c.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hcontR : ContinuousOn (fun t : ℝ => rad0 f s t)
        (Set.Icc (-(ρ (-c) * c)) (ρ c * c)) := by
      have h1 : ContinuousOn (fun t : ℝ => f t ^ 2 - (s * t) ^ 2)
          (Set.Icc (-(ρ (-c) * c)) (ρ c * c)) :=
        (hcontf.pow 2).sub ((continuous_const.mul continuous_id).continuousOn.pow 2)
      exact h1.congr (fun t _ => by simp [rad0])
    exact ((continuous_id.pow 2).continuousOn.mul (hcontR.pow (n - 1))).mul
      (Real.continuous_sqrt.comp_continuousOn hcontR)
  have hrootm : f (-(X s)) = s * X s := by rw [hfmX]; ring
  have hint1 : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
      rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(ρ (-c) * c)) (ρ c * c) := by
    have h' : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t * (f t - t * deriv f t) *
        rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)) volume (-(X s)) (Y s) :=
      rad0_hint1_aux n hs' hXmem.1 hYmem.1 hXmem.2 hYmem.2
        (Work.OddEnvelope.concaveOn_envelopeProfile H) hf_c hd_cont hf0 hfY hrootm
    rwa [hXeq, hYeq] at h'
  have hcrux := anchorRadonData n hn hs' hf_c hf_sm hρpos hρsm hρmono hgraph hbound hrootR
    hrootL hrad hint1 hint2
  rw [← hc] at hcrux
  have hjunc := anchorPhi_eq_ballData n hn H ha hab hzero hder0 hA hB s hs
  rw [← hc] at hjunc
  have hII : inertiaIntegral n f (fun _ : ℝ => ρ (-c) * c) (fun _ : ℝ => ρ c * c) s
      = inertiaIntegral n f X Y s := by
    unfold inertiaIntegral
    rw [← hXeq, ← hYeq]
  rw [hcrux, hII, hjunc]

end

end Work.OddCurve.LowSlope
