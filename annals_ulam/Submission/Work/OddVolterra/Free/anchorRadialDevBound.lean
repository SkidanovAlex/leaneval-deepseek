import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.anchor_curve_close_linear
import Submission.Work.OddVolterra.Free.envelopeRightDevOrdersTwo
import Submission.Work.OddVolterra.Free.envelopeLeftWideDevOrdersTwo
import Submission.Work.OddVolterra.Free.anchorBumpJetsAbs
import Submission.Work.OddVolterra.Free.radialDevPolyBound

set_option maxHeartbeats 4000000

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Elementary profile facts -/

/-- The envelope profile is zero for `t ≥ 1`. -/
lemma envelopeProfile_eq_zero_of_one_le {h x y : ℝ → ℝ} {t : ℝ} (ht : 1 ≤ t) :
    Work.OddEnvelope.envelopeProfile h x y t = 0 := by
  rw [Work.OddEnvelope.envelopeProfile]
  rw [if_neg (by intro hmem; exact absurd hmem.2 (not_lt.mpr ht)),
    if_neg (by intro hmem; linarith [hmem.2, ht]),
    if_neg (by intro hc; rw [hc] at ht; norm_num at ht)]

/-- The envelope profile is zero for `t ≤ -1`. -/
lemma envelopeProfile_eq_zero_of_le_neg_one {h x y : ℝ → ℝ} {t : ℝ} (ht : t ≤ -1) :
    Work.OddEnvelope.envelopeProfile h x y t = 0 := by
  rw [Work.OddEnvelope.envelopeProfile]
  rw [if_neg (by intro hmem; linarith [hmem.1, ht]),
    if_neg (by intro hmem; linarith [hmem.1, ht]),
    if_neg (by intro hc; rw [hc] at ht; norm_num at ht)]

/-- **The chord (secant) lower bound** for a strictly concave profile with `f 0 = 1` and
`f (∓1) = 0`: `1 - |t| ≤ f t`. -/
lemma one_sub_abs_le_of_strictConcaveOn {f : ℝ → ℝ}
    (h : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f) (h0 : f 0 = 1) (h1 : f 1 = 0)
    (hm : f (-1) = 0) {t : ℝ} (ht : |t| < 1) : 1 - |t| ≤ f t := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hmemm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
  · have ht1 : -1 < t := (abs_lt.mp ht).1
    have hkey := h.2 hmem0 hmemm1 (by norm_num : (0 : ℝ) ≠ -1)
      (show 0 < 1 + t by linarith) (show 0 < -t by linarith) (by ring)
    have harg : (1 + t) • (0 : ℝ) + (-t) • (-1) = t := by
      simp only [smul_eq_mul]; ring
    rw [harg, h0, hm] at hkey
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at hkey
    rw [abs_of_neg ht0]
    linarith
  · rw [ht0, abs_zero, sub_zero]
    exact h0.symm.le
  · have ht1 : t < 1 := (abs_lt.mp ht).2
    have hkey := h.2 hmem0 hmem1 (by norm_num : (0 : ℝ) ≠ 1)
      (show 0 < 1 - t by linarith) (show 0 < t by linarith) (by ring)
    have harg : (1 - t) • (0 : ℝ) + t • 1 = t := by
      simp only [smul_eq_mul, mul_one, mul_zero, zero_add]
    rw [harg, h0, h1] at hkey
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at hkey
    rw [abs_of_pos ht0]
    linarith

lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]

/-- `2 ≤ ∞` in the smoothness order. -/
private lemma two_le_smoothness_infty : (2 : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)

/-- `profileX (7/10) ≤ 82/100`. -/
lemma profileX_seven_tenths_le : Work.OddEnvelope.profileX (7 / 10) ≤ 82 / 100 := by
  rw [Work.OddEnvelope.profileX]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  have h2 : Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) ^ 2 = 1 + (7 / 10 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt (1 + (7 / 10 : ℝ) ^ 2) := Real.sqrt_nonneg _
  nlinarith [h2, h0]

/-! ## `ρ ≡ 1` where the profile is the semicircle -/

/-- If `ρ =ᶠ 1` near `u` then its value and first two derivatives there vanish. -/
lemma abs_derivs_eq_zero_of_eventuallyEq_one {ρ : ℝ → ℝ} {u : ℝ} (h : ρ =ᶠ[𝓝 u] 1) :
    ρ u = 1 ∧ deriv ρ u = 0 ∧ deriv (deriv ρ) u = 0 := by
  refine ⟨h.eq_of_nhds, ?_, ?_⟩
  · rw [h.deriv_eq]; simp
  · have h2 := (h.iteratedDeriv 2).eq_of_nhds
    rw [iteratedDeriv_two_eq ρ, iteratedDeriv_two_eq (1 : ℝ → ℝ)] at h2
    rw [h2]; simp

/-- **Where the profile traces the semicircle, `ρ ≡ 1`.** -/
lemma eventuallyEq_one_of_trace_semicircle {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1)
    (hpos : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ v)
    (hcont : ContinuousAt ρ u)
    (hgraph : ∀ v ∈ Set.Ioo (-1 : ℝ) 1,
      ρ v * Real.sqrt (1 - v ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ v * v))
    (htw : ρ u * u ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar) :
    ρ =ᶠ[𝓝 u] 1 := by
  have hcφ : ContinuousAt (fun v : ℝ => ρ v * v) u := hcont.mul continuousAt_id
  have hmem : ∀ᶠ v in 𝓝 u, ρ v * v ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
    hcφ.preimage_mem_nhds (isOpen_Ioo.mem_nhds htw)
  filter_upwards [hmem, isOpen_Ioo.mem_nhds hu] with v hv hvI
  have hv1 : |v| < 1 := abs_lt.mpr hvI
  have harg : 0 ≤ 1 - v ^ 2 := by nlinarith [hv1, abs_nonneg v, sq_abs v]
  have harg2 : 0 ≤ 1 - (ρ v * v) ^ 2 := by
    have h2 : |ρ v * v| < 1 := by
      have h1' : -(1 : ℝ) < ρ v * v := by linarith [hv.1, Work.OddEnvelope.tStar_lt_one]
      have h2' : ρ v * v < 1 := by linarith [hv.2, Work.OddEnvelope.tStar_lt_one]
      rw [abs_lt]; exact ⟨h1', h2'⟩
    nlinarith [h2, abs_nonneg (ρ v * v), sq_abs (ρ v * v)]
  have hg := hgraph v hvI
  rw [Work.OddEnvelope.envelopeProfile_eq_semicircle H hv] at hg
  have hsq : (ρ v) ^ 2 = 1 := by
    have h2 := congrArg (fun z : ℝ => z ^ 2) hg
    rw [mul_pow, Real.sq_sqrt harg] at h2
    simp only [Work.OddEnvelope.semicircle, Real.sq_sqrt harg2] at h2
    nlinarith [h2]
  have hp := hpos v hvI
  have h1 : (ρ v - 1) * (ρ v + 1) = 0 := by nlinarith [hsq]
  have h2 : 0 < ρ v + 1 := by linarith
  rcases mul_eq_zero.mp h1 with h | h
  · rw [sub_eq_zero] at h; exact h
  · rw [add_eq_zero_iff_eq_neg] at h; linarith

/-- The envelope profile and `envelopeRight` have the same `iteratedDeriv`s on `(0,1)`. -/
lemma iteratedDeriv_envelopeProfile_eq_envelopeRight {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    iteratedDeriv k (Work.OddEnvelope.envelopeProfile h X Y) t =
      iteratedDeriv k (Work.OddEnvelope.envelopeRight h Y) t := by
  have hev : Work.OddEnvelope.envelopeProfile h X Y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeRight h Y := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact Work.OddEnvelope.envelopeProfile_of_pos hu
  exact (hev.iteratedDeriv k).eq_of_nhds

/-! ## The profile deviation at the anchor point -/

/-- **The profile's deviation from the semicircle at the anchor point (right branch).** -/
private theorem profile_dev_right (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ {h X Y ρ : ℝ → ℝ} {u ε' η : ℝ},
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      IsAnchorRadial h X Y ρ →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      0 < u → |u| < 4 / 5 → 0 ≤ η → η ≤ 1 / 100 → 0 ≤ ε' →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |Y s - Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η) →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |h s| ≤ ε' ∧ |deriv h s| ≤ ε' ∧ |deriv (deriv h) s| ≤ ε') →
      |ρ u * u| ≤ 17 / 20 ∧
      |Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) -
          Work.OddEnvelope.semicircle (ρ u * u)| ≤ Cd * (η + ε') ∧
      |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ u * u) -
          deriv Work.OddEnvelope.semicircle (ρ u * u)| ≤ Cd * (η + ε') ∧
      |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ u * u) -
          deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)| ≤ Cd * (η + ε') := by
  obtain ⟨CR, hCRpos, hRight⟩ := envelopeRightDevOrdersTwo n hn
  refine ⟨max CR 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro h X Y ρ u ε' η H hρ hcY hu0 hu huη0 huη1 hε'0 hcl hjet
  have hCRle : CR ≤ max CR 1 := le_max_left _ _
  have hCdpos : 0 < max CR 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hηε : 0 ≤ η + ε' := by linarith
  have huI : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [abs_lt] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hρu : 0 < ρ u := hρ.1 u huI
  have hgraph := hρ.2.2.2.1 u huI
  have hsq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 :=
    Real.sq_sqrt (by nlinarith [huI.1, huI.2])
  have hsqrtpos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [huI.1, huI.2])
  set t : ℝ := ρ u * u with htdef
  have htpos : 0 < t := by rw [htdef]; exact mul_pos hρu hu0
  have hft : 0 < Work.OddEnvelope.envelopeProfile h X Y t := by
    rw [htdef, ← hgraph]
    exact mul_pos hρu hsqrtpos
  have htlt1 : t < 1 := by
    by_contra hc
    have h0 : Work.OddEnvelope.envelopeProfile h X Y t = 0 :=
      envelopeProfile_eq_zero_of_one_le (le_of_not_gt hc)
    linarith
  have htI : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨htpos, htlt1⟩
  have hRsq : (ρ u) ^ 2 = t ^ 2 + (Work.OddEnvelope.envelopeProfile h X Y t) ^ 2 := by
    rw [htdef, ← hgraph]
    nlinarith [hsq]
  have hflower : 3 / 4 * t < Work.OddEnvelope.envelopeProfile h X Y t := by
    have hu2 : u ^ 2 < (4 / 5 : ℝ) ^ 2 := by
      have := abs_lt.mp hu
      nlinarith [this.1, this.2]
    have hut : u = t / ρ u := by rw [htdef]; field_simp
    have h25 : 25 * t ^ 2 < 16 * (ρ u) ^ 2 := by
      rw [hut, div_pow] at hu2
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (ρ u) ^ 2)] at hu2
      nlinarith [hu2]
    rw [hRsq] at h25
    nlinarith [h25, hft, htpos]
  have hfanti : StrictAntiOn (Work.OddEnvelope.envelopeProfile h X Y) (Set.Ioo (0 : ℝ) 1) :=
    strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
      ((Work.OddEnvelope.envelopeProfile_contDiffOn H).continuousOn.mono
        (fun x hx => ⟨by linarith [hx.1], hx.2⟩))
      (fun x hx => by
        rw [interior_Ioo] at hx
        exact Work.OddEnvelope.deriv_envelopeProfile_neg H hx)
  set σ : ℝ := Work.OddEnvelope.slopeRight Y t with hσdef
  have hσpos : 0 < σ := H.toChordCurve_y.slopeRight_pos htI
  have hYσ : Y σ = t := H.toChordCurve_y.slopeRight_eq htI
  have hσ7 : 7 / 10 < σ := by
    by_contra hc
    have hσle : σ ≤ 7 / 10 := le_of_not_gt hc
    have hY7mem : Y (7 / 10) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨H.toChordCurve_y.pos (by norm_num), H.toChordCurve_y.lt_one (by norm_num)⟩
    have htge : Y (7 / 10) ≤ t := by
      rcases lt_or_eq_of_le hσle with hlt | heq
      · have hh := H.toChordCurve_y.strictAntiOn hσpos (by norm_num : (0 : ℝ) < 7 / 10) hlt
        rw [hYσ] at hh
        linarith
      · rw [← heq, hYσ]
    have hfle : Work.OddEnvelope.envelopeProfile h X Y t
        ≤ Work.OddEnvelope.envelopeProfile h X Y (Y (7 / 10)) := by
      rcases lt_or_eq_of_le htge with hlt | heq
      · exact le_of_lt (hfanti hY7mem htI hlt)
      · rw [heq]
    have hsl : (7 : ℝ) / 10 = Work.OddEnvelope.slopeRight Y (Y (7 / 10)) :=
      H.toChordCurve_y.slopeRight_eq_of hY7mem (by norm_num) rfl
    have hval7 : Work.OddEnvelope.envelopeProfile h X Y (Y (7 / 10)) = 7 / 10 * Y (7 / 10) := by
      have hsl2 : Work.OddEnvelope.slopeRight Y (Y (7 / 10)) = 7 / 10 := hsl.symm
      rw [Work.OddEnvelope.envelopeProfile_of_pos hY7mem, Work.OddEnvelope.envelopeRight, hsl2]
      have hz : h (7 / 10) = 0 := by
        by_contra hc
        have hmem := H.h_support (Function.mem_support.mpr hc)
        rw [Set.mem_Icc] at hmem
        have h1 : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by
          norm_num [Work.OddEnvelope.tau]
        linarith [hmem.1, h1]
      rw [hz, add_zero]
    have h7t : 7 / 10 * Y (7 / 10) ≤ 7 / 10 * t := by nlinarith [htge]
    linarith [hfle, hval7, hflower]
  -- the range of the profile point
  have ht17 : |ρ u * u| ≤ 17 / 20 := by
    have hY7le : Y (7 / 10) ≤ 83 / 100 := by
      have h1 := (hcY (7 / 10) (by norm_num)).1
      have h2 : Work.OddEnvelope.profileX (7 / 10) ≤ 82 / 100 := profileX_seven_tenths_le
      rw [abs_le] at h1
      linarith [h1.2, h2]
    have htle : t ≤ Y (7 / 10) := by
      have hh := H.toChordCurve_y.strictAntiOn (by norm_num : (0 : ℝ) < 7 / 10) hσpos hσ7
      rw [hYσ] at hh
      linarith
    rw [← htdef, abs_of_pos htpos]
    linarith
  rcases le_or_gt σ 1 with hσ1 | hσ1
  · have hres := hRight (p := h) (c := Y) (σ := σ) (ε := ε') (η := η)
      huη0 huη1 H.toChordCurve_y H.smooth_h (le_of_lt hσ7) hσ1 hcl
      (hjet σ (le_of_lt hσ7) hσ1)
    have hconv : ∀ k : ℕ, k ≤ 2 →
        |iteratedDeriv k (Work.OddEnvelope.envelopeProfile h X Y) t -
          iteratedDeriv k Work.OddEnvelope.semicircle t| ≤ CR * (η + ε') := by
      intro k hk
      have hk' := hres k hk
      rw [hYσ] at hk'
      rw [← iteratedDeriv_envelopeProfile_eq_envelopeRight H htI k] at hk'
      exact hk'
    have h0 : |Work.OddEnvelope.envelopeProfile h X Y t - Work.OddEnvelope.semicircle t|
        ≤ CR * (η + ε') := by simpa using hconv 0 (by norm_num)
    have h1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) t
        - deriv Work.OddEnvelope.semicircle t| ≤ CR * (η + ε') := by
      simpa [iteratedDeriv_one] using hconv 1 (by norm_num)
    have h2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) t
        - deriv (deriv Work.OddEnvelope.semicircle) t| ≤ CR * (η + ε') := by
      simpa [iteratedDeriv_two_eq] using hconv 2 (by norm_num)
    have hle : CR * (η + ε') ≤ max CR 1 * (η + ε') :=
      mul_le_mul_of_nonneg_right hCRle hηε
    refine ⟨ht17, ?_, ?_, ?_⟩
    · linarith [h0, hle]
    · linarith [h1, hle]
    · linarith [h2, hle]
  · have htstar : t < Work.OddEnvelope.tStar := by
      have htail : Y σ = Work.OddEnvelope.profileX σ :=
        H.y_tail σ (by
          have h : (1 : ℝ) - Work.OddEnvelope.tau = 9 / 10 := by norm_num [Work.OddEnvelope.tau]
          linarith [hσ1, h])
      have hstar : Work.OddEnvelope.tStar = Work.OddEnvelope.profileX (9 / 10) := by
        rw [Work.OddEnvelope.tStar]
        norm_num [Work.OddEnvelope.tau]
      rw [hstar, ← hYσ, htail]
      exact Work.OddEnvelope.profileX_strictAntiOn (by norm_num) hσpos (by linarith [hσ1])
    have htmem : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
      ⟨by linarith [Work.OddEnvelope.tStar_pos], htstar⟩
    have hev : Work.OddEnvelope.envelopeProfile h X Y =ᶠ[𝓝 t] Work.OddEnvelope.semicircle := by
      filter_upwards [isOpen_Ioo.mem_nhds htmem] with x hx
      exact Work.OddEnvelope.envelopeProfile_eq_semicircle H hx
    have h0 : Work.OddEnvelope.envelopeProfile h X Y t = Work.OddEnvelope.semicircle t := by
      simpa using (hev.iteratedDeriv 0).eq_of_nhds
    have h1 : deriv (Work.OddEnvelope.envelopeProfile h X Y) t =
        deriv Work.OddEnvelope.semicircle t := by
      simpa [iteratedDeriv_one] using (hev.iteratedDeriv 1).eq_of_nhds
    have h2 : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) t =
        deriv (deriv Work.OddEnvelope.semicircle) t := by
      simpa [iteratedDeriv_two_eq] using (hev.iteratedDeriv 2).eq_of_nhds
    have hnn : (0 : ℝ) ≤ max CR 1 * (η + ε') := by positivity
    refine ⟨ht17, ?_, ?_, ?_⟩
    · have : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)
          - Work.OddEnvelope.semicircle (ρ u * u) = 0 := by
        rw [← htdef, h0]; ring
      rw [this, abs_zero]; exact hnn
    · have : deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ u * u)
          - deriv Work.OddEnvelope.semicircle (ρ u * u) = 0 := by
        rw [← htdef, h1]; ring
      rw [this, abs_zero]; exact hnn
    · have : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ u * u)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u) = 0 := by
        rw [← htdef, h2]; ring
      rw [this, abs_zero]; exact hnn

/-- **The profile's deviation from the semicircle at the anchor point (left branch).** -/
private theorem profile_dev_left (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ {h X Y ρ : ℝ → ℝ} {u ε' η : ℝ},
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      IsAnchorRadial h X Y ρ →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      u < 0 → |u| < 4 / 5 → 0 ≤ η → η ≤ 1 / 100 → 0 ≤ ε' →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |X s - Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η) →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |h s| ≤ ε' ∧ |deriv h s| ≤ ε' ∧ |deriv (deriv h) s| ≤ ε') →
      |ρ u * u| ≤ 17 / 20 ∧
      |Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) -
          Work.OddEnvelope.semicircle (ρ u * u)| ≤ Cd * (η + ε') ∧
      |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ u * u) -
          deriv Work.OddEnvelope.semicircle (ρ u * u)| ≤ Cd * (η + ε') ∧
      |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ u * u) -
          deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)| ≤ Cd * (η + ε') := by
  obtain ⟨CL, hCLpos, hLeft⟩ := envelopeLeftWideDevOrdersTwo n hn
  refine ⟨max CL 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro h X Y ρ u ε' η H hρ hcX hu0 hu huη0 huη1 hε'0 hcl hjet
  have hCLle : CL ≤ max CL 1 := le_max_left _ _
  have hCdpos : 0 < max CL 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hηε : 0 ≤ η + ε' := by linarith
  have huI : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [abs_lt] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hρu : 0 < ρ u := hρ.1 u huI
  have hgraph := hρ.2.2.2.1 u huI
  have hsq : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 :=
    Real.sq_sqrt (by nlinarith [huI.1, huI.2])
  have hsqrtpos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [huI.1, huI.2])
  set t : ℝ := ρ u * u with htdef
  have htneg : t < 0 := by rw [htdef]; exact mul_neg_of_pos_of_neg hρu hu0
  have htabs : |t| = -t := abs_of_neg htneg
  have hft : 0 < Work.OddEnvelope.envelopeProfile h X Y t := by
    rw [htdef, ← hgraph]
    exact mul_pos hρu hsqrtpos
  have htgt1 : -1 < t := by
    by_contra hc
    have h0 : Work.OddEnvelope.envelopeProfile h X Y t = 0 :=
      envelopeProfile_eq_zero_of_le_neg_one (le_of_not_gt hc)
    linarith
  have htI : t ∈ Set.Ioo (-1 : ℝ) 0 := ⟨htgt1, htneg⟩
  have hRsq : (ρ u) ^ 2 = t ^ 2 + (Work.OddEnvelope.envelopeProfile h X Y t) ^ 2 := by
    rw [htdef, ← hgraph]
    nlinarith [hsq]
  have hflower : 3 / 4 * |t| < Work.OddEnvelope.envelopeProfile h X Y t := by
    have hu2 : u ^ 2 < (4 / 5 : ℝ) ^ 2 := by
      have := abs_lt.mp hu
      nlinarith [this.1, this.2]
    have hut : u = t / ρ u := by rw [htdef]; field_simp
    have h25 : 25 * t ^ 2 < 16 * (ρ u) ^ 2 := by
      rw [hut, div_pow] at hu2
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (ρ u) ^ 2)] at hu2
      nlinarith [hu2]
    rw [hRsq] at h25
    nlinarith [h25, hft, htneg, htabs]
  have hfmono : StrictMonoOn (Work.OddEnvelope.envelopeProfile h X Y) (Set.Ioo (-1 : ℝ) 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 0)
      ((Work.OddEnvelope.envelopeProfile_contDiffOn H).continuousOn.mono
        (fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
      (fun x hx => by
        rw [interior_Ioo] at hx
        exact Work.OddEnvelope.deriv_envelopeProfile_pos H hx)
  set ξ : ℝ := -t with hξdef
  have hξpos : 0 < ξ := by rw [hξdef]; linarith
  have hξlt1 : ξ < 1 := by rw [hξdef]; linarith
  set σ : ℝ := Work.OddEnvelope.slopeRight X ξ with hσdef
  have hξI : ξ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hξpos, hξlt1⟩
  have hσpos : 0 < σ := H.toChordCurve_x.slopeRight_pos hξI
  have hXσ : X σ = ξ := H.toChordCurve_x.slopeRight_eq hξI
  have htt : t = -(X σ) := by rw [hXσ, hξdef]; ring
  have hσ7 : 7 / 10 < σ := by
    by_contra hc
    have hσle : σ ≤ 7 / 10 := le_of_not_gt hc
    have hX7mem : X (7 / 10) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨H.toChordCurve_x.pos (by norm_num), H.toChordCurve_x.lt_one (by norm_num)⟩
    have hξge : X (7 / 10) ≤ ξ := by
      rcases lt_or_eq_of_le hσle with hlt | heq
      · have hh := H.toChordCurve_x.strictAntiOn hσpos (by norm_num : (0 : ℝ) < 7 / 10) hlt
        rw [hXσ] at hh
        linarith
      · rw [← heq, hXσ]
    have hneg7mem : -(X (7 / 10)) ∈ Set.Ioo (-1 : ℝ) 0 :=
      ⟨by linarith [hX7mem.2], by linarith [hX7mem.1]⟩
    have htle : t ≤ -(X (7 / 10)) := by linarith [hξge, hξdef]
    have hfle : Work.OddEnvelope.envelopeProfile h X Y t
        ≤ Work.OddEnvelope.envelopeProfile h X Y (-(X (7 / 10))) := by
      rcases lt_or_eq_of_le htle with hlt | heq
      · exact le_of_lt (hfmono htI hneg7mem hlt)
      · rw [heq]
    have hsl : (7 : ℝ) / 10 = Work.OddEnvelope.slopeRight X (X (7 / 10)) :=
      H.toChordCurve_x.slopeRight_eq_of hX7mem (by norm_num) rfl
    have hval7 : Work.OddEnvelope.envelopeProfile h X Y (-(X (7 / 10))) = 7 / 10 * X (7 / 10) := by
      rw [Work.OddEnvelope.envelopeProfile_of_neg hneg7mem, Work.OddEnvelope.envelopeLeft_eq_negH,
        Work.OddEnvelope.envelopeRight]
      simp only [neg_neg]
      rw [hsl.symm]
      have hz : h (7 / 10) = 0 := by
        by_contra hc
        have hmem := H.h_support (Function.mem_support.mpr hc)
        rw [Set.mem_Icc] at hmem
        have h1 : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by
          norm_num [Work.OddEnvelope.tau]
        linarith [hmem.1, h1]
      simp only [Work.OddEnvelope.negH, hz, neg_zero, add_zero]
    have h7t : 7 / 10 * X (7 / 10) ≤ 7 / 10 * |t| := by
      have : X (7 / 10) ≤ |t| := by rw [htabs]; linarith [hξge, hξdef]
      nlinarith [this]
    linarith [hfle, hval7, hflower]
  have ht17 : |ρ u * u| ≤ 17 / 20 := by
    have hX7le : X (7 / 10) ≤ 83 / 100 := by
      have h1 := (hcX (7 / 10) (by norm_num)).1
      have h2 : Work.OddEnvelope.profileX (7 / 10) ≤ 82 / 100 := profileX_seven_tenths_le
      rw [abs_le] at h1
      linarith [h1.2, h2]
    have hξle : ξ ≤ X (7 / 10) := by
      have hh := H.toChordCurve_x.strictAntiOn (by norm_num : (0 : ℝ) < 7 / 10) hσpos hσ7
      rw [hXσ] at hh
      linarith
    rw [← htdef, abs_of_neg htneg]
    linarith [hξle, hX7le, hξdef]
  rcases le_or_gt σ 1 with hσ1 | hσ1
  · have hres := hLeft (h := h) (X := X) (σ := σ) (ε := ε') (η := η)
      huη0 huη1 H (le_of_lt hσ7) hσ1 hcl (hjet σ (le_of_lt hσ7) hσ1)
    have hconv : ∀ k : ℕ, k ≤ 2 →
        |iteratedDeriv k (Work.OddEnvelope.envelopeProfile h X Y) t -
          iteratedDeriv k Work.OddEnvelope.semicircle t| ≤ CL * (η + ε') := by
      intro k hk
      have hk' := hres k hk
      rw [← htt] at hk'
      exact hk'
    have h0 : |Work.OddEnvelope.envelopeProfile h X Y t - Work.OddEnvelope.semicircle t|
        ≤ CL * (η + ε') := by simpa using hconv 0 (by norm_num)
    have h1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) t
        - deriv Work.OddEnvelope.semicircle t| ≤ CL * (η + ε') := by
      simpa [iteratedDeriv_one] using hconv 1 (by norm_num)
    have h2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) t
        - deriv (deriv Work.OddEnvelope.semicircle) t| ≤ CL * (η + ε') := by
      simpa [iteratedDeriv_two_eq] using hconv 2 (by norm_num)
    have hle : CL * (η + ε') ≤ max CL 1 * (η + ε') :=
      mul_le_mul_of_nonneg_right hCLle hηε
    refine ⟨ht17, ?_, ?_, ?_⟩
    · linarith [h0, hle]
    · linarith [h1, hle]
    · linarith [h2, hle]
  · have htstar : -t < Work.OddEnvelope.tStar := by
      have htail : X σ = Work.OddEnvelope.profileX σ :=
        H.x_tail σ (by
          have h : (1 : ℝ) - Work.OddEnvelope.tau = 9 / 10 := by norm_num [Work.OddEnvelope.tau]
          linarith [hσ1, h])
      have hstar : Work.OddEnvelope.tStar = Work.OddEnvelope.profileX (9 / 10) := by
        rw [Work.OddEnvelope.tStar]
        norm_num [Work.OddEnvelope.tau]
      rw [hstar, ← hξdef, ← hXσ, htail]
      exact Work.OddEnvelope.profileX_strictAntiOn (by norm_num) hσpos (by linarith [hσ1])
    have htmem : t ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
      ⟨by linarith [htstar], by linarith [Work.OddEnvelope.tStar_pos, htneg]⟩
    have hev : Work.OddEnvelope.envelopeProfile h X Y =ᶠ[𝓝 t] Work.OddEnvelope.semicircle := by
      filter_upwards [isOpen_Ioo.mem_nhds htmem] with x hx
      exact Work.OddEnvelope.envelopeProfile_eq_semicircle H hx
    have h0 : Work.OddEnvelope.envelopeProfile h X Y t = Work.OddEnvelope.semicircle t := by
      simpa using (hev.iteratedDeriv 0).eq_of_nhds
    have h1 : deriv (Work.OddEnvelope.envelopeProfile h X Y) t =
        deriv Work.OddEnvelope.semicircle t := by
      simpa [iteratedDeriv_one] using (hev.iteratedDeriv 1).eq_of_nhds
    have h2 : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) t =
        deriv (deriv Work.OddEnvelope.semicircle) t := by
      simpa [iteratedDeriv_two_eq] using (hev.iteratedDeriv 2).eq_of_nhds
    have hnn : (0 : ℝ) ≤ max CL 1 * (η + ε') := by positivity
    refine ⟨ht17, ?_, ?_, ?_⟩
    · have : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)
          - Work.OddEnvelope.semicircle (ρ u * u) = 0 := by
        rw [← htdef, h0]; ring
      rw [this, abs_zero]; exact hnn
    · have : deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ u * u)
          - deriv Work.OddEnvelope.semicircle (ρ u * u) = 0 := by
        rw [← htdef, h1]; ring
      rw [this, abs_zero]; exact hnn
    · have : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ u * u)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u) = 0 := by
        rw [← htdef, h2]; ring
      rw [this, abs_zero]; exact hnn

/-! ## From the profile deviation to the radial deviation -/

/-- **The radial function is `1` up to the profile deviation.** -/
private theorem radial_dev_of_profile_dev :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ {h X Y ρ : ℝ → ℝ} {u ν : ℝ},
      Work.OddEnvelope.IsEnvelopeCurve h X Y → IsAnchorRadial h X Y ρ →
      |u| < 4 / 5 → u ≠ 0 → |ρ u * u| ≤ 17 / 20 →
      |Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) -
        Work.OddEnvelope.semicircle (ρ u * u)| ≤ ν →
      |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ u * u) -
        deriv Work.OddEnvelope.semicircle (ρ u * u)| ≤ ν →
      |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ u * u) -
        deriv (deriv Work.OddEnvelope.semicircle) (ρ u * u)| ≤ ν →
      |ρ u - 1| ≤ Cr * (ν + ν ^ 2) ∧
        |deriv ρ u| ≤ Cr * (ν + ν ^ 2 + ν ^ 3) ∧
        |deriv (deriv ρ) u| ≤ Cr * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) := by
  obtain ⟨Cr, hCr, hrad⟩ := radialDevPolyBound
  refine ⟨Cr, hCr, ?_⟩
  intro h X Y ρ u ν H hρ hu hune ht17 hd0 hd1 hd2
  have hν0 : 0 ≤ ν := le_trans (abs_nonneg _) hd0
  have huI : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [abs_lt] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have ht1 : |ρ u * u| < 1 := lt_of_le_of_lt ht17 (by norm_num)
  have hft : 0 < Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) := by
    rw [← hρ.2.2.2.1 u huI]
    exact mul_pos (hρ.1 u huI) (Real.sqrt_pos.mpr (by nlinarith [huI.1, huI.2]))
  have hchord : 1 - |ρ u * u| ≤ Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) :=
    one_sub_abs_le_of_strictConcaveOn (Work.OddEnvelope.strictConcaveOn_envelopeProfile H)
      (Work.OddEnvelope.envelopeProfile_zero) (Work.OddEnvelope.envelopeProfile_right_end)
      (Work.OddEnvelope.envelopeProfile_left_end) ht1
  exact hrad hν0 hu hune (hρ.2.1.of_le two_le_smoothness_infty)
    ((Work.OddEnvelope.envelopeProfile_contDiffOn H).of_le two_le_smoothness_infty)
    ht17 (hρ.1 u huI) hft hchord (Work.OddEnvelope.strictConcaveOn_envelopeProfile H)
    (Work.OddEnvelope.envelopeProfile_right_end) (Work.OddEnvelope.envelopeProfile_left_end)
    (Work.OddEnvelope.envelopeProfile_zero)
    (fun t ht0 ht1 => le_of_lt (Work.OddEnvelope.deriv_envelopeProfile_neg H ⟨ht0, ht1⟩))
    (fun t ht0 ht1 => le_of_lt (Work.OddEnvelope.deriv_envelopeProfile_pos H ⟨ht0, ht1⟩))
    (hρ.2.2.2.1) hd0 hd1 hd2

/-! ## The anchor radial deviation bound -/

theorem anchorRadialDevBound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ} {h X Y ρ : ℝ → ℝ},
      Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h →
      h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      Work.OddVolterra.Free.IsAnchorRadial h X Y ρ →
      ∀ u : ℝ, |u| < 4 / 5 →
        |ρ u - 1| ≤ C * ε ∧ |deriv ρ u| ≤ C * ε ∧ |deriv (deriv ρ) u| ≤ C * ε := by
  obtain ⟨C₁, hC₁pos, hcurve⟩ := anchor_curve_close_linear n hn
  obtain ⟨CR, hCRpos, hRightDev⟩ := profile_dev_right n hn
  obtain ⟨CL, hCLpos, hLeftDev⟩ := profile_dev_left n hn
  obtain ⟨Cd, hCdpos, hRad⟩ := radial_dev_of_profile_dev
  obtain ⟨Kh, hKhpos, hBump⟩ := anchorBumpJetsAbs n hn
  -- constants
  set CD : ℝ := max (max CR 1) (max CL 1) with hCDdef
  have hCDpos : 0 < CD := by
    rw [hCDdef]
    exact lt_of_lt_of_le one_pos (le_trans (le_max_right CR 1) (le_max_left _ _))
  have hCRle : max CR 1 ≤ CD := by rw [hCDdef]; exact le_max_left _ _
  have hCLle : max CL 1 ≤ CD := by rw [hCDdef]; exact le_max_right _ _
  have hCRle' : CR ≤ CD := le_trans (le_max_left CR 1) hCRle
  have hCLle' : CL ≤ CD := le_trans (le_max_left CL 1) hCLle
  set K1 : ℝ := CD * (C₁ + 1) with hK1def
  have hK1pos : 0 < K1 := by rw [hK1def]; exact mul_pos hCDpos (by linarith)
  set νabs : ℝ := CD * (1 / 100 + Kh) with hνabsdef
  have hνabs0 : 0 ≤ νabs := by rw [hνabsdef]; positivity
  set Gabs : ℝ := 4 * Cd * (max 1 νabs) ^ 4 with hGabsdef
  have hGabs0 : 0 ≤ Gabs := by rw [hGabsdef]; positivity
  refine ⟨16 * Cd * K1 + Gabs * (K1 + 1) + 1, by positivity, ?_⟩
  intro ε h X Y ρ hbump hne H hcX hcY hA hB hρ u hu
  -- basic set-up
  have hε0 : 0 ≤ ε := by
    have h0 := hbump.2.2.1 0 (by omega) 0
    rw [iteratedDeriv_zero] at h0
    exact le_trans (abs_nonneg _) h0
  have hclass : ∀ k : ℕ, k ≤ 2 * n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε := hbump.2.2.1
  -- the three-fold bump class
  have hthree : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h :=
    ⟨hbump.1, hbump.2.1, fun k hk s => hclass k (by omega) s, hbump.2.2.2⟩
  have hcur := hcurve hthree hne H hcX hcY hA hB
  have hτ : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by
    norm_num [Work.OddVolterra.tau]
  -- the two closeness packages and the two jet packages
  set η₁ : ℝ := min (C₁ * ε) (1 / 100) with hη₁def
  have hη₁0 : 0 ≤ η₁ := by rw [hη₁def]; exact le_min (by positivity) (by norm_num)
  have hη₁100 : η₁ ≤ 1 / 100 := by rw [hη₁def]; exact min_le_right _ _
  have hη₁C : η₁ ≤ C₁ * ε := by rw [hη₁def]; exact min_le_left _ _
  have hclX : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |X s - Work.OddEnvelope.profileX s| ≤ η₁ ∧
      |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ η₁ ∧
      |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η₁ := by
    intro s h1 h2
    have hcs := hcur s (by linarith [h1, hτ]) h2
    exact ⟨le_min (by linarith [hcs.1]) ((hcX s (by linarith)).1),
      le_min (by linarith [hcs.2.1]) ((hcX s (by linarith)).2.1),
      le_min (by linarith [hcs.2.2.1]) ((hcX s (by linarith)).2.2)⟩
  have hclY : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |Y s - Work.OddEnvelope.profileX s| ≤ η₁ ∧
      |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ η₁ ∧
      |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η₁ := by
    intro s h1 h2
    have hcs := hcur s (by linarith [h1, hτ]) h2
    exact ⟨le_min (by linarith [hcs.2.2.2.1]) ((hcY s (by linarith)).1),
      le_min (by linarith [hcs.2.2.2.2.1]) ((hcY s (by linarith)).2.1),
      le_min (by linarith [hcs.2.2.2.2.2]) ((hcY s (by linarith)).2.2)⟩
  have hclX100 : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |X s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100 :=
    fun s h1 h2 => ⟨(hcX s (by linarith)).1, (hcX s (by linarith)).2.1,
      (hcX s (by linarith)).2.2⟩
  have hclY100 : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |Y s - Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100 :=
    fun s h1 h2 => ⟨(hcY s (by linarith)).1, (hcY s (by linarith)).2.1,
      (hcY s (by linarith)).2.2⟩
  have hjetε : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |h s| ≤ ε ∧ |deriv h s| ≤ ε ∧ |deriv (deriv h) s| ≤ ε := by
    intro s h1 h2
    refine ⟨?_, ?_, ?_⟩
    · simpa [iteratedDeriv_zero] using hclass 0 (by omega) s
    · simpa [iteratedDeriv_one] using hclass 1 (by omega) s
    · have hh := hclass 2 (by omega) s
      rwa [iteratedDeriv_two_eq h] at hh
  have hjetK : ∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
      |h s| ≤ Kh ∧ |deriv h s| ≤ Kh ∧ |deriv (deriv h) s| ≤ Kh :=
    fun s h1 h2 => hBump H hcX hcY hbump.2.1 s h1 h2
  -- the arithmetic lemmas
  have hνKall : CD * (η₁ + ε) ≤ K1 * ε := by
    have h1 : η₁ + ε ≤ (C₁ + 1) * ε := by linarith [hη₁C]
    have h2 := mul_le_mul_of_nonneg_left h1 hCDpos.le
    have h3 : CD * ((C₁ + 1) * ε) = CD * (C₁ + 1) * ε := by ring
    rw [hK1def]
    linarith [h2, h3]
  have hlin : ∀ ν : ℝ, 0 ≤ ν → ν ≤ 1 → ν ≤ K1 * ε →
      Cd * (ν + ν ^ 2) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      Cd * (ν + ν ^ 2 + ν ^ 3) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := by
    intro ν hν0 hν1 hνK
    have hquad : ν ^ 2 ≤ ν := by nlinarith
    have hcube : ν ^ 3 ≤ ν := by nlinarith [hquad, hν0]
    have hquart : ν ^ 4 ≤ ν := by nlinarith [hquad, hν0]
    have hsum : ν + ν ^ 2 + ν ^ 3 + ν ^ 4 ≤ 4 * ν := by linarith
    have hkey : Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) ≤ 4 * Cd * ν := by
      have h := mul_le_mul_of_nonneg_left hsum hCdpos.le
      linarith [h]
    have hkey2 : 4 * Cd * ν ≤ 4 * Cd * (K1 * ε) := by
      have h := mul_le_mul_of_nonneg_left hνK (by positivity : (0:ℝ) ≤ 4 * Cd)
      linarith [h]
    have hcf : 4 * Cd * K1 ≤ 16 * Cd * K1 + Gabs * (K1 + 1) + 1 := by
      nlinarith [hGabs0, hK1pos]
    have hfin : 4 * Cd * (K1 * ε) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := by
      have hcf' : 4 * Cd * K1 * ε ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε :=
        mul_le_mul_of_nonneg_right hcf hε0
      have h3 : 4 * Cd * (K1 * ε) = 4 * Cd * K1 * ε := by ring
      linarith [hcf', h3]
    refine ⟨?_, ?_, ?_⟩
    · calc
        Cd * (ν + ν ^ 2) ≤ Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) := by
          have hnn : 0 ≤ ν ^ 3 + ν ^ 4 := by positivity
          nlinarith [hnn, hCdpos.le]
        _ ≤ 4 * Cd * ν := hkey
        _ ≤ 4 * Cd * (K1 * ε) := hkey2
        _ ≤ _ := hfin
    · calc
        Cd * (ν + ν ^ 2 + ν ^ 3) ≤ Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) := by
          have hnn : 0 ≤ ν ^ 4 := by positivity
          nlinarith [hnn, hCdpos.le]
        _ ≤ 4 * Cd * ν := hkey
        _ ≤ 4 * Cd * (K1 * ε) := hkey2
        _ ≤ _ := hfin
    · calc
        Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) ≤ 4 * Cd * ν := hkey
        _ ≤ 4 * Cd * (K1 * ε) := hkey2
        _ ≤ _ := hfin
  have habs : ∀ ν : ℝ, 0 ≤ ν → ν ≤ νabs → 1 / (K1 + 1) ≤ ε →
      Cd * (ν + ν ^ 2) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      Cd * (ν + ν ^ 2 + ν ^ 3) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := by
    intro ν hν0 hνν hreg
    have hmax1 : (1 : ℝ) ≤ max 1 νabs := le_max_left _ _
    have hmaxp : 0 < max 1 νabs := lt_of_lt_of_le one_pos hmax1
    have hmaxν : ν ≤ max 1 νabs := le_trans hνν (le_max_right _ _)
    have h2 : ν ^ 2 ≤ (max 1 νabs) ^ 2 := by nlinarith [hν0, hmaxν, hmaxp.le]
    have h3 : ν ^ 3 ≤ (max 1 νabs) ^ 3 := by nlinarith [hν0, hmaxν, hmaxp.le]
    have h4 : ν ^ 4 ≤ (max 1 νabs) ^ 4 := by nlinarith [hν0, hmaxν, hmaxp.le]
    have hK1p : (0 : ℝ) < K1 + 1 := by linarith
    have hG : Cd * (ν + ν ^ 2 + ν ^ 3 + ν ^ 4) ≤ Gabs := by
      have h1 : ν ≤ (max 1 νabs) ^ 4 := by
        calc ν ≤ max 1 νabs := hmaxν
          _ = (max 1 νabs) ^ 1 := by ring
          _ ≤ (max 1 νabs) ^ 4 := pow_le_pow_right₀ hmax1 (by norm_num)
      have h2' : ν ^ 2 ≤ (max 1 νabs) ^ 4 :=
        le_trans h2 (pow_le_pow_right₀ hmax1 (by norm_num : (2:ℕ) ≤ 4))
      have h3' : ν ^ 3 ≤ (max 1 νabs) ^ 4 :=
        le_trans h3 (pow_le_pow_right₀ hmax1 (by norm_num : (3:ℕ) ≤ 4))
      have hsum : ν + ν ^ 2 + ν ^ 3 + ν ^ 4 ≤ 4 * (max 1 νabs) ^ 4 := by
        linarith [h1, h2', h3', h4]
      rw [hGabsdef]
      have := mul_le_mul_of_nonneg_left hsum hCdpos.le
      linarith [this]
    have hε1 : 1 ≤ (K1 + 1) * ε := by
      have h := mul_le_mul_of_nonneg_right hreg hK1p.le
      have h2 : (1 : ℝ) / (K1 + 1) * (K1 + 1) = 1 := div_mul_cancel₀ 1 (ne_of_gt hK1p)
      rw [h2] at h
      linarith [h]
    have hG1 : Gabs ≤ Gabs * ((K1 + 1) * ε) := by
      have := mul_le_mul_of_nonneg_left hε1 hGabs0
      rwa [mul_one] at this
    have hG2 : Gabs * ((K1 + 1) * ε) ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := by
      have hmain : Gabs * (K1 + 1) ≤ 16 * Cd * K1 + Gabs * (K1 + 1) + 1 := by
        nlinarith [hGabs0, hCdpos.le, hK1pos]
      have h := mul_le_mul_of_nonneg_right hmain hε0
      have h3 : Gabs * (K1 + 1) * ε = Gabs * ((K1 + 1) * ε) := by ring
      linarith [h, h3]
    have hGfin : Gabs ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := le_trans hG1 hG2
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (by
        have hnn : 0 ≤ ν ^ 3 + ν ^ 4 := by positivity
        nlinarith [hnn, hCdpos.le]) (le_trans hG hGfin)
    · exact le_trans (by
        have hnn : 0 ≤ ν ^ 4 := by positivity
        nlinarith [hnn, hCdpos.le]) (le_trans hG hGfin)
    · exact le_trans hG hGfin
  -- the per-point argument
  have key : ∀ v : ℝ, |v| < 4 / 5 →
      |ρ v - 1| ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      |deriv ρ v| ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε ∧
      |deriv (deriv ρ) v| ≤ (16 * Cd * K1 + Gabs * (K1 + 1) + 1) * ε := by
    intro v hv
    have hηε0 : 0 ≤ η₁ + ε := by positivity
    have h1ε : (0 : ℝ) ≤ 1 / 100 + Kh := by positivity
    rcases lt_trichotomy v 0 with hneg | hzero | hpos
    · obtain ⟨ht17, d0, d1, d2⟩ := hLeftDev H hρ hcX hneg hv hη₁0 hη₁100 hε0 hclX hjetε
      obtain ⟨_, e0, e1, e2⟩ := hLeftDev H hρ hcX hneg hv (by norm_num) (by norm_num)
        hKhpos.le hclX100 hjetK
      have hd0 : |Work.OddEnvelope.envelopeProfile h X Y (ρ v * v)
          - Work.OddEnvelope.semicircle (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d0 (mul_le_mul_of_nonneg_right hCLle' hηε0)
      have hd1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ v * v)
          - deriv Work.OddEnvelope.semicircle (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d1 (mul_le_mul_of_nonneg_right hCLle' hηε0)
      have hd2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ v * v)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d2 (mul_le_mul_of_nonneg_right hCLle' hηε0)
      have he0 : |Work.OddEnvelope.envelopeProfile h X Y (ρ v * v)
          - Work.OddEnvelope.semicircle (ρ v * v)| ≤ νabs :=
        le_trans e0 (mul_le_mul_of_nonneg_right hCLle' h1ε)
      have he1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ v * v)
          - deriv Work.OddEnvelope.semicircle (ρ v * v)| ≤ νabs :=
        le_trans e1 (mul_le_mul_of_nonneg_right hCLle' h1ε)
      have he2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ v * v)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ v * v)| ≤ νabs :=
        le_trans e2 (mul_le_mul_of_nonneg_right hCLle' h1ε)
      obtain ⟨b0, b1, b2⟩ := hRad H hρ hv (by linarith) ht17 hd0 hd1 hd2
      obtain ⟨c0, c1, c2⟩ := hRad H hρ hv (by linarith) ht17 he0 he1 he2
      by_cases hεl : ε ≤ 1 / (K1 + 1)
      · have hν1 : CD * (η₁ + ε) ≤ 1 := by
          have h1 : K1 * ε ≤ K1 / (K1 + 1) := by
            have h := mul_le_mul_of_nonneg_left hεl hK1pos.le
            rwa [mul_one_div] at h
          have h3 : K1 / (K1 + 1) ≤ 1 := by
            rw [div_le_one (by linarith : (0 : ℝ) < K1 + 1)]
            linarith
          linarith [hνKall, h1, h3]
        obtain ⟨a0, a1, a2⟩ := hlin (CD * (η₁ + ε)) (by positivity) hν1 hνKall
        exact ⟨le_trans b0 a0, le_trans b1 a1, le_trans b2 a2⟩
      · have hreg : 1 / (K1 + 1) ≤ ε := (le_of_lt (not_le.mp hεl))
        obtain ⟨a0, a1, a2⟩ := habs νabs hνabs0 le_rfl hreg
        exact ⟨le_trans c0 a0, le_trans c1 a1, le_trans c2 a2⟩
    · subst hzero
      have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
      have hcont : ContinuousAt ρ 0 :=
        (hρ.2.1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0mem))
      have htw : ρ 0 * 0 ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar := by
        simp only [mul_zero]
        exact ⟨by linarith [Work.OddEnvelope.tStar_pos], Work.OddEnvelope.tStar_pos⟩
      have hev := eventuallyEq_one_of_trace_semicircle H h0mem hρ.1 hcont (hρ.2.2.2.1) htw
      obtain ⟨hv0, hd1, hd2⟩ := abs_derivs_eq_zero_of_eventuallyEq_one hev
      rw [hv0, hd1, hd2]
      have hCfin0 : (0 : ℝ) ≤ 16 * Cd * K1 + Gabs * (K1 + 1) + 1 := by positivity
      have hmain := mul_nonneg hCfin0 hε0
      exact ⟨by simpa using hmain, by simpa using hmain, by simpa using hmain⟩
    · obtain ⟨ht17, d0, d1, d2⟩ := hRightDev H hρ hcY hpos hv hη₁0 hη₁100 hε0 hclY hjetε
      obtain ⟨_, e0, e1, e2⟩ := hRightDev H hρ hcY hpos hv (by norm_num) (by norm_num)
        hKhpos.le hclY100 hjetK
      have hd0 : |Work.OddEnvelope.envelopeProfile h X Y (ρ v * v)
          - Work.OddEnvelope.semicircle (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d0 (mul_le_mul_of_nonneg_right hCRle' hηε0)
      have hd1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ v * v)
          - deriv Work.OddEnvelope.semicircle (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d1 (mul_le_mul_of_nonneg_right hCRle' hηε0)
      have hd2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ v * v)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ v * v)| ≤ CD * (η₁ + ε) :=
        le_trans d2 (mul_le_mul_of_nonneg_right hCRle' hηε0)
      have he0 : |Work.OddEnvelope.envelopeProfile h X Y (ρ v * v)
          - Work.OddEnvelope.semicircle (ρ v * v)| ≤ νabs :=
        le_trans e0 (mul_le_mul_of_nonneg_right hCRle' h1ε)
      have he1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (ρ v * v)
          - deriv Work.OddEnvelope.semicircle (ρ v * v)| ≤ νabs :=
        le_trans e1 (mul_le_mul_of_nonneg_right hCRle' h1ε)
      have he2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (ρ v * v)
          - deriv (deriv Work.OddEnvelope.semicircle) (ρ v * v)| ≤ νabs :=
        le_trans e2 (mul_le_mul_of_nonneg_right hCRle' h1ε)
      obtain ⟨b0, b1, b2⟩ := hRad H hρ hv (by linarith) ht17 hd0 hd1 hd2
      obtain ⟨c0, c1, c2⟩ := hRad H hρ hv (by linarith) ht17 he0 he1 he2
      by_cases hεl : ε ≤ 1 / (K1 + 1)
      · have hν1 : CD * (η₁ + ε) ≤ 1 := by
          have h1 : K1 * ε ≤ K1 / (K1 + 1) := by
            have h := mul_le_mul_of_nonneg_left hεl hK1pos.le
            rwa [mul_one_div] at h
          have h3 : K1 / (K1 + 1) ≤ 1 := by
            rw [div_le_one (by linarith : (0 : ℝ) < K1 + 1)]
            linarith
          linarith [hνKall, h1, h3]
        obtain ⟨a0, a1, a2⟩ := hlin (CD * (η₁ + ε)) (by positivity) hν1 hνKall
        exact ⟨le_trans b0 a0, le_trans b1 a1, le_trans b2 a2⟩
      · have hreg : 1 / (K1 + 1) ≤ ε := (le_of_lt (not_le.mp hεl))
        obtain ⟨a0, a1, a2⟩ := habs νabs hνabs0 le_rfl hreg
        exact ⟨le_trans c0 a0, le_trans c1 a1, le_trans c2 a2⟩
  exact key u hu

end

end Work.OddVolterra.Free
