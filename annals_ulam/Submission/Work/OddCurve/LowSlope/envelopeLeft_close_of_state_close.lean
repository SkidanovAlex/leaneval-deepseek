import Mathlib
import Submission.Work.OddCurve.LowSlope.QuantDefs
import Submission.Work.OddEnvelope.Defs
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddEnvelope.Concave
import Submission.Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf
import Submission.Work.OddCurve.LowSlope.profile_gap_close
import Submission.Work.OddEnvelope.Semicircle.deriv_semicircle
import Submission.Work.OddEnvelope.Close.profileX_deriv_formulas

/-!
# The left branch of the envelope profile is close to the semicircle on the gap

Statement requested by the low-slope step of the odd case of Ulam's problem; see
`Submission/Work/OddCurve/LowSlope/NOTES_CRUX_2026.md` §9, §10, §13.

We are given a state `Z` whose first component is `C²`-close (`η`) to the semicircle chord
function `profileX` on `[1/2,1]`, and a curve `(X,Y)` which equals the first two components of
`Z` there.  On the gap `ξ ∈ (tStar, cStar)` the left branch of the profile is
`envelopeProfile h X Y (-ξ) = σ ξ - h σ` with `σ = slopeRight X ξ` the slope with `X σ = ξ`, and
`σ` runs over `(4/5, 9/10)`.  Comparing with the semicircle (= the same construction with
`X = profileX`, `h = 0`) we show that the value, the first and the second derivative deviate by
at most `C (η + ε)`, where `ε` bounds the bump `h` and its first two derivatives.

The two mechanisms:
* the value: `|σ - σ₁| ≤ 3 η` where `σ₁` is the semicircle slope with `profileX σ₁ = ξ`, by the
  reverse Lipschitz bound for `profileX` on `[3/4, 9/10]`;
* the derivatives: `σ` is an implicit function of `ξ` with `dσ/dξ = 1/X'(σ)`, so the deviations
  are explicit rational expressions in the jets `(X, X', X'', h, h', h'')` at `σ`; these are
  Lipschitz in the data, and the constants are bounded on the compact window.
-/

namespace Work.OddCurve.LowSlope

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-! ## Eventual equality of derivatives -/

private lemma deriv_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    deriv f =ᶠ[𝓝 x] deriv g := by
  obtain ⟨t, hsub, htopen, hxt⟩ := mem_nhds_iff.mp h
  refine Filter.eventually_of_mem (htopen.mem_nhds hxt) ?_
  intro u hu
  exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (htopen.mem_nhds hu) hsub)

/-! ## The second derivative of the semicircle -/

theorem deriv_deriv_semicircle {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv Work.OddEnvelope.semicircle) t = -(1 / Work.OddEnvelope.semicircle t ^ 3) := by
  have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hne : (1 - t ^ 2 : ℝ) ≠ 0 := ne_of_gt hpos
  have hspos : 0 < Work.OddEnvelope.semicircle t := Real.sqrt_pos.mpr hpos
  -- first derivative of the semicircle at `t`, as a `HasDerivAt`
  have hs : HasDerivAt Work.OddEnvelope.semicircle (-t / Work.OddEnvelope.semicircle t) t := by
    have h2 : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-2 * t) t := by
      have h : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      simpa using h.const_sub 1
    have h3 : HasDerivAt (fun u : ℝ => Real.sqrt (1 - u ^ 2)) ((-2 * t) / (2 * Real.sqrt (1 - t ^ 2))) t :=
      h2.sqrt hne
    have hfun : (fun u : ℝ => Real.sqrt (1 - u ^ 2)) = Work.OddEnvelope.semicircle := rfl
    rw [hfun] at h3
    refine h3.congr_deriv ?_
    rw [Work.OddEnvelope.semicircle]
    field_simp
  have hq : HasDerivAt (fun u : ℝ => -u / Work.OddEnvelope.semicircle u)
      ((-1 * Work.OddEnvelope.semicircle t - (-t) * (-t / Work.OddEnvelope.semicircle t)) /
        Work.OddEnvelope.semicircle t ^ 2) t :=
    ((hasDerivAt_id t).neg).div hs (ne_of_gt hspos)
  have heq : deriv Work.OddEnvelope.semicircle =ᶠ[𝓝 t]
      (fun u => -u / Work.OddEnvelope.semicircle u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      (fun u hu => Work.OddEnvelope.Semicircle.deriv_semicircle hu)
  rw [Filter.EventuallyEq.deriv_eq heq, hq.deriv]
  have hsq : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Work.OddEnvelope.semicircle, Real.sq_sqrt (le_of_lt hpos)]
  field_simp
  nlinarith [hsq]

/-! ## The derivative of `slopeRight` for a chord curve -/

section SlopeRightDeriv

variable {c : ℝ → ℝ}

private lemma slopeRight_eq_of_chord (hc : Work.OddEnvelope.IsChordCurve c) {σ t : ℝ}
    (hσ : 0 < σ) (h : c σ = t) : σ = Work.OddEnvelope.slopeRight c t := by
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [← h]
    exact ⟨hc.pos hσ, hc.lt_one hσ⟩
  exact hc.slopeRight_eq_of ht hσ h

private lemma eventually_slopeRight_apply_chord (hc : Work.OddEnvelope.IsChordCurve c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ u in 𝓝 t, c (Work.OddEnvelope.slopeRight c u) = u := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact hc.slopeRight_eq hu

private lemma continuousAt_slopeRight_chord (hc : Work.OddEnvelope.IsChordCurve c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ContinuousAt (Work.OddEnvelope.slopeRight c) t := by
  obtain ⟨σ, hσpos, hσt⟩ := hc.surj ht
  have hAnti : StrictAntiOn c (Set.Ioi 0) := hc.strictAntiOn
  have hInj : Set.InjOn c (Set.Ioi 0) := hAnti.injOn
  have hst : Work.OddEnvelope.slopeRight c t = σ := (slopeRight_eq_of_chord hc hσpos hσt).symm
  rw [Metric.continuousAt_iff, hst]
  intro ε hε
  set e : ℝ := min ε σ / 2 with he
  have he_pos : 0 < e := by rw [he]; have h := lt_min hε hσpos; linarith
  have he_lt_ε : e < ε := by rw [he]; have h := min_le_left ε σ; linarith
  have he_lt_σ : e < σ := by rw [he]; have h := min_le_right ε σ; linarith
  have ha_pos : 0 < σ - e := by linarith
  have hb_pos : 0 < σ + e := by linarith
  have hya : t < c (σ - e) := by
    have h := (hAnti.lt_iff_gt hσpos ha_pos).2 (show σ - e < σ by linarith)
    rwa [hσt] at h
  have hyb : c (σ + e) < t := by
    have h := (hAnti.lt_iff_gt hb_pos hσpos).2 (show σ < σ + e by linarith)
    rwa [hσt] at h
  refine ⟨min (min t (1 - t)) (min (t - c (σ + e)) (c (σ - e) - t)), ?_, ?_⟩
  · exact lt_min (lt_min ht.1 (by linarith [ht.2])) (lt_min (by linarith) (by linarith))
  · intro u hu
    have h1 : dist u t < t := lt_of_lt_of_le hu (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : dist u t < 1 - t := lt_of_lt_of_le hu (le_trans (min_le_left _ _) (min_le_right _ _))
    have h3 : dist u t < t - c (σ + e) :=
      lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_left _ _))
    have h4 : dist u t < c (σ - e) - t :=
      lt_of_lt_of_le hu (le_trans (min_le_right _ _) (min_le_right _ _))
    have hub : |u - t| < t := by rw [Real.dist_eq] at h1; exact h1
    have hu1' : |u - t| < 1 - t := by rw [Real.dist_eq] at h2; exact h2
    have hu3 : |u - t| < t - c (σ + e) := by rw [Real.dist_eq] at h3; exact h3
    have hu4 : |u - t| < c (σ - e) - t := by rw [Real.dist_eq] at h4; exact h4
    have hu0 : 0 < u := by have := (abs_lt.mp hub).1; linarith
    have hu1 : u < 1 := by have := (abs_lt.mp hu1').2; linarith
    have huya : u < c (σ - e) := by have := (abs_lt.mp hu4).2; linarith
    have huyb : c (σ + e) < u := by have := (abs_lt.mp hu3).1; linarith
    obtain ⟨w, hw, hwy⟩ := intermediate_value_Ioo' (show σ - e ≤ σ + e by linarith)
      (hc.smooth.continuousOn.mono
        (by intro x hx; simp only [mem_Icc] at hx
            exact show 0 < x from by linarith [hx.1, ha_pos]))
      (show u ∈ Set.Ioo (c (σ + e)) (c (σ - e)) from ⟨huyb, huya⟩)
    have hwmem : w ∈ Set.Ioi (0 : ℝ) := show 0 < w from by linarith [hw.1, ha_pos]
    have hslope : Work.OddEnvelope.slopeRight c u = w := by
      refine hInj (hc.slopeRight_mem ⟨hu0, hu1⟩).1 hwmem ?_
      rw [hc.slopeRight_eq ⟨hu0, hu1⟩, hwy]
    rw [hslope, Real.dist_eq]
    have : |w - σ| < e := by
      rw [abs_lt]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
    linarith

/-- **The inverse of a chord curve is differentiable with derivative `1/c'(σ)`.** -/
theorem slopeRight_hasDerivAt (hc : Work.OddEnvelope.IsChordCurve c) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (Work.OddEnvelope.slopeRight c)
      ((deriv c (Work.OddEnvelope.slopeRight c t))⁻¹) t := by
  set σ := Work.OddEnvelope.slopeRight c t with hσdef
  have hσpos : 0 < σ := hc.slopeRight_pos ht
  have hcont : ContinuousAt (Work.OddEnvelope.slopeRight c) t :=
    continuousAt_slopeRight_chord hc ht
  have hc_at : HasDerivAt c (deriv c σ) σ :=
    ((hc.smooth.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hσpos)).hasDerivAt
  have hne : deriv c σ ≠ 0 := ne_of_lt (hc.deriv_neg σ hσpos)
  have := HasDerivAt.of_local_left_inverse hcont hc_at hne
    (eventually_slopeRight_apply_chord hc ht)
  simpa [hσdef] using this

end SlopeRightDeriv

/-! ## The derivative of `kSlope` -/

/-- The logarithmic-derivative quotient `kSlope p c` is differentiable with the quotient-rule
derivative. -/
theorem hasDerivAt_kSlope {p c : ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (Set.Ioi 0))
    (hp : ContDiffOn ℝ ∞ p (Set.Ioi 0)) {σ : ℝ} (hσ : 0 < σ) (hne : deriv c σ ≠ 0) :
    HasDerivAt (Work.OddEnvelope.kSlope p c)
      ((2 * (deriv c σ) ^ 2 - c σ * deriv (deriv c) σ + deriv (deriv p) σ * deriv c σ
        - deriv p σ * deriv (deriv c) σ) / (deriv c σ) ^ 2) σ := by
  have hderivc : ContDiffOn ℝ ∞ (deriv c) (Set.Ioi 0) :=
    hc.deriv_of_isOpen isOpen_Ioi (by simp)
  have hderivp : ContDiffOn ℝ ∞ (deriv p) (Set.Ioi 0) :=
    hp.deriv_of_isOpen isOpen_Ioi (by simp)
  have hc_at : HasDerivAt c (deriv c σ) σ :=
    (hc.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσ)
  have hdc_at : HasDerivAt (deriv c) (deriv (deriv c) σ) σ :=
    (hderivc.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσ)
  have hdp_at : HasDerivAt (deriv p) (deriv (deriv p) σ) σ :=
    (hderivp.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hσ)
  have hnum : HasDerivAt (fun τ => c τ + τ * deriv c τ + deriv p τ)
      (deriv c σ + (deriv c σ + σ * deriv (deriv c) σ) + deriv (deriv p) σ) σ := by
    have key : (fun τ => c τ + τ * deriv c τ + deriv p τ)
        = (c + id * deriv c + deriv p) := by
      funext τ; simp [Pi.add_apply, Pi.mul_apply]
    rw [key]
    exact ((hc_at.add ((hasDerivAt_id σ).mul hdc_at)).add hdp_at).congr_deriv
      (by simp only [id_eq, one_mul])
  rw [show Work.OddEnvelope.kSlope p c
      = fun τ => (c τ + τ * deriv c τ + deriv p τ) / deriv c τ from rfl]
  refine (hnum.div hdc_at hne).congr_deriv ?_
  ring

/-! ## The second derivative of the right branch of the envelope -/

/-- The second derivative of `envelopeRight p c` at the value `t`, in terms of the jet of
`(p, c)` at the slope `σ = slopeRight c t`. -/
theorem deriv_deriv_envelopeRight {p c : ℝ → ℝ} (hc : Work.OddEnvelope.IsChordCurve c)
    (hp : ContDiffOn ℝ ∞ p (Set.Ioi 0)) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv (Work.OddEnvelope.envelopeRight p c)) t =
      (2 * (deriv c (Work.OddEnvelope.slopeRight c t)) ^ 2
          - c (Work.OddEnvelope.slopeRight c t) * deriv (deriv c) (Work.OddEnvelope.slopeRight c t)
          + deriv (deriv p) (Work.OddEnvelope.slopeRight c t) * deriv c (Work.OddEnvelope.slopeRight c t)
          - deriv p (Work.OddEnvelope.slopeRight c t)
              * deriv (deriv c) (Work.OddEnvelope.slopeRight c t))
        / (deriv c (Work.OddEnvelope.slopeRight c t)) ^ 3 := by
  set σ := Work.OddEnvelope.slopeRight c t with hσdef
  have hσpos : 0 < σ := hc.slopeRight_pos ht
  have hne : deriv c σ ≠ 0 := ne_of_lt (hc.deriv_neg σ hσpos)
  have hkeq : deriv (Work.OddEnvelope.envelopeRight p c) =ᶠ[𝓝 t]
      (fun v => Work.OddEnvelope.kSlope p c (Work.OddEnvelope.slopeRight c v)) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun v hv =>
      Work.OddEnvelope.Smoothness.envelopeRight_deriv_Cinf hc.smooth hc.deriv_neg hp
        (fun t ht => hc.surj ht) v hv)
  rw [Filter.EventuallyEq.deriv_eq hkeq]
  have hslope : HasDerivAt (Work.OddEnvelope.slopeRight c) ((deriv c σ)⁻¹) t :=
    slopeRight_hasDerivAt hc ht
  have hk : HasDerivAt (Work.OddEnvelope.kSlope p c)
      ((2 * (deriv c σ) ^ 2 - c σ * deriv (deriv c) σ + deriv (deriv p) σ * deriv c σ
        - deriv p σ * deriv (deriv c) σ) / (deriv c σ) ^ 2) σ :=
    hasDerivAt_kSlope hc.smooth hp hσpos hne
  have hcomp := hk.comp t hslope
  show deriv ((Work.OddEnvelope.kSlope p c) ∘ (Work.OddEnvelope.slopeRight c)) t =
    (2 * deriv c σ ^ 2 - c σ * deriv (deriv c) σ + deriv (deriv p) σ * deriv c σ
      - deriv p σ * deriv (deriv c) σ) / deriv c σ ^ 3
  rw [hcomp.deriv]
  field_simp
  try ring

/-! ## The second derivative of the left branch of the envelope profile -/

/-- **The second derivative of the envelope profile on its left branch.**  For `ξ ∈ (0,1)` and
`σ = slopeRight x ξ` (so that `x σ = ξ`),

`f''(-ξ) = (2 x'(σ)² - ξ x''(σ) - h''(σ) x'(σ) + h'(σ) x''(σ)) / x'(σ)³`. -/
theorem deriv_deriv_envelopeProfile_of_neg {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {ξ σ : ℝ}
    (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) (hσ : σ = Work.OddEnvelope.slopeRight x ξ) :
    deriv (deriv (Work.OddEnvelope.envelopeProfile h x y)) (-ξ) =
      (2 * (deriv x σ) ^ 2 - x σ * deriv (deriv x) σ - deriv (deriv h) σ * deriv x σ
        + deriv h σ * deriv (deriv x) σ) / (deriv x σ) ^ 3 := by
  have ht : (-ξ) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith [hξ.2], by linarith [hξ.1]⟩
  -- the profile is the reflected right branch near `-ξ`
  have hev : Work.OddEnvelope.envelopeProfile h x y =ᶠ[𝓝 (-ξ)]
      (fun u => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    rw [Work.OddEnvelope.envelopeProfile_of_neg hu, Work.OddEnvelope.envelopeLeft_eq_negH]
  have h1 : deriv (Work.OddEnvelope.envelopeProfile h x y) =ᶠ[𝓝 (-ξ)]
      deriv (fun u => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u)) :=
    deriv_eventuallyEq hev
  have h2 : deriv (deriv (Work.OddEnvelope.envelopeProfile h x y)) =ᶠ[𝓝 (-ξ)]
      deriv (deriv (fun u => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))) :=
    deriv_eventuallyEq h1
  rw [Filter.EventuallyEq.eq_of_nhds h2]
  -- the second derivative of a reflection
  have hfun : deriv (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))
      = fun u => -deriv (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-u) := by
    funext u
    exact deriv_comp_neg _ u
  rw [hfun]
  have hneg : deriv (fun u : ℝ => -deriv (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-u))
        (-ξ)
      = -deriv (fun u : ℝ => deriv (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-u))
        (-ξ) := by
    rw [show (fun u : ℝ => -deriv (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-u))
        = -(fun u : ℝ => deriv (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x) (-u))
        from rfl, deriv.neg]
  rw [hneg, deriv_comp_neg]
  simp only [neg_neg]
  -- now apply the formula for the right branch
  have hp : ContDiffOn ℝ ∞ (Work.OddEnvelope.negH h) (Set.Ioi 0) := H.smooth_h.neg
  have hfin := deriv_deriv_envelopeRight H.toChordCurve_x hp hξ
  rw [hfin]
  have hxσ : x σ = ξ := by rw [hσ]; exact H.toChordCurve_x.slopeRight_eq hξ
  have h1' : deriv (Work.OddEnvelope.negH h) σ = -deriv h σ := by
    rw [Work.OddEnvelope.deriv_negH]
  have h2' : deriv (deriv (Work.OddEnvelope.negH h)) σ = -deriv (deriv h) σ := by
    rw [Work.OddEnvelope.deriv_deriv_negH]
  rw [← hσ, h1', h2', hxσ]
  ring

/-! ## Numerical facts about the semicircle chord function on the gap -/

/-- `|profileX'| ≤ 1` on the positive axis. -/
private lemma profileX_deriv_abs_le_one {s : ℝ} (hs : 0 < s) :
    |deriv Work.OddEnvelope.profileX s| ≤ 1 := by
  rw [Work.OddCurve.LowSlope.deriv_profileX_eq s]
  have h1 : 0 ≤ s / (1 + s ^ 2) := by positivity
  have h2 : s / (1 + s ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (s - 1)]
  rw [abs_mul, abs_neg, abs_of_nonneg h1,
    abs_of_pos (Work.OddEnvelope.profileX_pos s)]
  calc s / (1 + s ^ 2) * Work.OddEnvelope.profileX s ≤ 1 * 1 :=
        mul_le_mul h2 (le_of_lt (Work.OddEnvelope.profileX_lt_one hs))
          (le_of_lt (Work.OddEnvelope.profileX_pos s)) (by norm_num)
    _ = 1 := by ring

/-- `|profileX''| ≤ 1` on the gap. -/
private lemma profileX_deriv2_abs_le_one {s : ℝ} (h1 : 3 / 4 ≤ s) (h2 : s ≤ 9 / 10) :
    |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 := by
  rw [(Work.OddEnvelope.Close.profileX_deriv_formulas s).2.1]
  have hspos : 0 < s := by linarith
  have hp1 : Work.OddEnvelope.profileX s ≤ 1 :=
    le_of_lt (Work.OddEnvelope.profileX_lt_one hspos)
  have hp0 : 0 ≤ Work.OddEnvelope.profileX s := le_of_lt (Work.OddEnvelope.profileX_pos s)
  have h3 : |2 * s ^ 2 - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have h4 : |Work.OddEnvelope.profileX s ^ 5| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hp0 hp1
  rw [abs_mul]
  calc |2 * s ^ 2 - 1| * |Work.OddEnvelope.profileX s ^ 5| ≤ 1 * 1 :=
        mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- `cStar = 5/√41 < 799/1000`, so that `cStar + 1/1000 < 4/5`. -/
private lemma cStar_add_one_thousandth_lt : Work.OddCurve.LowSlope.cStar + 1 / 1000 < 4 / 5 := by
  have h41 : (0 : ℝ) < Real.sqrt 41 := Real.sqrt_pos.mpr (by norm_num)
  have hc : Work.OddCurve.LowSlope.cStar = 5 / Real.sqrt 41 := by
    rw [Work.OddCurve.LowSlope.cStar, show (1 : ℝ) + (4 / 5) ^ 2 = 41 / 25 by norm_num,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 41)]
    rw [show Real.sqrt (25 : ℝ) = 5 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  have hlt : (5000 : ℝ) / 799 < Real.sqrt 41 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h5 : (5 : ℝ) / Real.sqrt 41 < 799 / 1000 := by
    rw [div_lt_iff₀ h41]
    have h := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 799)
    have h' : (799 : ℝ) * (5000 / 799) = 5000 := by field_simp
    rw [h'] at h
    linarith
  rw [hc]
  linarith

/-! ## Differentiability of `profileX` and Lipschitz bounds on the gap -/

private lemma differentiableAt_profileX (s : ℝ) :
    DifferentiableAt ℝ Work.OddEnvelope.profileX s := by
  have h : Work.OddEnvelope.profileX = fun u : ℝ => (Real.sqrt (1 + u ^ 2))⁻¹ := by
    funext u; simp [Work.OddEnvelope.profileX, one_div]
  rw [h]; fun_prop (disch := positivity)

private lemma differentiableAt_deriv_profileX (s : ℝ) :
    DifferentiableAt ℝ (deriv Work.OddEnvelope.profileX) s := by
  have hfun : deriv Work.OddEnvelope.profileX
      = fun u : ℝ => -u * Work.OddEnvelope.profileX u ^ 3 := by
    funext u; exact (Work.OddEnvelope.Close.profileX_deriv_formulas u).1
  rw [hfun]
  exact (differentiableAt_id.neg).mul ((differentiableAt_profileX s).pow 3)

private lemma differentiableAt_mul_profileX (s : ℝ) :
    DifferentiableAt ℝ (fun u : ℝ => u * Work.OddEnvelope.profileX u) s :=
  differentiableAt_id.mul (differentiableAt_profileX s)

/-- Lipschitz bound for `profileX'` on the gap. -/
private lemma abs_deriv_profileX_sub_le {a b : ℝ}
    (ha : a ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) (hb : b ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) :
    |deriv Work.OddEnvelope.profileX a - deriv Work.OddEnvelope.profileX b| ≤ |a - b| := by
  have hdiff : ∀ x ∈ Set.Icc (3 / 4 : ℝ) (9 / 10),
      DifferentiableAt ℝ (deriv Work.OddEnvelope.profileX) x :=
    fun x _ => differentiableAt_deriv_profileX x
  have hbound : ∀ x ∈ Set.Icc (3 / 4 : ℝ) (9 / 10),
      ‖deriv (deriv Work.OddEnvelope.profileX) x‖ ≤ 1 := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact profileX_deriv2_abs_le_one hx.1 hx.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) ha hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  linarith [h, abs_sub_comm (deriv Work.OddEnvelope.profileX a)
    (deriv Work.OddEnvelope.profileX b), abs_sub_comm a b]

/-- Lipschitz bound for `s ↦ s * profileX s` on the gap. -/
private lemma abs_mul_profileX_sub_le {a b : ℝ}
    (ha : a ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) (hb : b ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) :
    |a * Work.OddEnvelope.profileX a - b * Work.OddEnvelope.profileX b| ≤ |a - b| := by
  have hdiff : ∀ x ∈ Set.Icc (3 / 4 : ℝ) (9 / 10),
      DifferentiableAt ℝ (fun s : ℝ => s * Work.OddEnvelope.profileX s) x :=
    fun x _ => differentiableAt_mul_profileX x
  have hbound : ∀ x ∈ Set.Icc (3 / 4 : ℝ) (9 / 10),
      ‖deriv (fun s : ℝ => s * Work.OddEnvelope.profileX s) x‖ ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [Real.norm_eq_abs]
    have hd : deriv (fun s : ℝ => s * Work.OddEnvelope.profileX s) x
        = Work.OddEnvelope.profileX x ^ 3 := by
      change deriv ((id : ℝ → ℝ) * Work.OddEnvelope.profileX) x
        = Work.OddEnvelope.profileX x ^ 3
      have h := deriv_mul (x := x) differentiableAt_id (differentiableAt_profileX x)
      simp only [Pi.mul_apply, id_eq] at h
      rw [h, show deriv (id : ℝ → ℝ) x = 1 from by simp, one_mul]
      exact (Work.OddEnvelope.Close.profileX_deriv_formulas x).2.2.1
    rw [hd, abs_of_nonneg (pow_nonneg (le_of_lt (Work.OddEnvelope.profileX_pos x)) 3)]
    exact pow_le_one₀ (le_of_lt (Work.OddEnvelope.profileX_pos x))
      (le_of_lt (Work.OddEnvelope.profileX_lt_one hx0))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) ha hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  linarith [h, abs_sub_comm (a * Work.OddEnvelope.profileX a)
    (b * Work.OddEnvelope.profileX b), abs_sub_comm a b]

/-- `profileX x ≥ 2/3` for `0 ≤ x ≤ 9/10`. -/
private lemma two_thirds_le_profileX {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 9 / 10) :
    2 / 3 ≤ Work.OddEnvelope.profileX x := by
  have h1 : 1 + x ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith
  have h2 : Real.sqrt (1 + x ^ 2) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    exact h1
  rw [Work.OddEnvelope.profileX, le_div_iff₀ (Real.sqrt_pos_of_pos (by positivity))]
  linarith

/-- `|x³ - y³| ≤ 3|x - y|` for `|x|,|y| ≤ 1`. -/
private lemma abs_cube_sub_cube_le {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x ^ 3 - y ^ 3| ≤ 3 * |x - y| := by
  have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  have hy' : -1 ≤ y ∧ y ≤ 1 := abs_le.mp hy
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx'.1, hx'.2]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [hy'.1, hy'.2]
  have hxy : |x * y| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg y]
  have h3 : |x ^ 2 + x * y + y ^ 2| ≤ 3 := by
    rw [abs_le]
    constructor
    · nlinarith [(abs_le.mp hxy).1, sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
    · nlinarith [(abs_le.mp hxy).2, hx2, hy2]
  have hfac : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [hfac, abs_mul]
  nlinarith [abs_nonneg (x - y), h3]

/-- `|1/x³ - 1/y³| ≤ 192 |x - y|` for `x, y ∈ [1/2, 1]`. -/
private lemma abs_inv_cube_sub_le {x y : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1)
    (hy : 1 / 2 ≤ y) (hy1 : y ≤ 1) :
    |1 / x ^ 3 - 1 / y ^ 3| ≤ 192 * |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxpos : 0 < x ^ 3 := by positivity
  have hypos : 0 < y ^ 3 := by positivity
  have hcube : |y ^ 3 - x ^ 3| ≤ 3 * |x - y| := by
    have h := abs_cube_sub_cube_le (x := x) (y := y)
      (by rw [abs_of_pos hx0]; exact hx1) (by rw [abs_of_pos hy0]; exact hy1)
    rw [abs_sub_comm] at h
    linarith [h, abs_sub_comm x y]
  have hkey : 1 / x ^ 3 - 1 / y ^ 3 = (y ^ 3 - x ^ 3) / (x ^ 3 * y ^ 3) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos (mul_pos hxpos hypos),
    div_le_iff₀ (mul_pos hxpos hypos)]
  have hden : 1 / 64 ≤ x ^ 3 * y ^ 3 := by
    have h1 : (1 / 8 : ℝ) ≤ x ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hx 3
      norm_num at h
      exact h
    have h2 : (1 / 8 : ℝ) ≤ y ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hy 3
      norm_num at h
      exact h
    calc (1 / 64 : ℝ) = (1 / 8) * (1 / 8) := by norm_num
      _ ≤ x ^ 3 * y ^ 3 := mul_le_mul h1 h2 (by norm_num) (le_of_lt hxpos)
  nlinarith [abs_nonneg (x - y), hcube, hden]

/-- The semicircle second-derivative profile of the gap, `Ψ₀ s = -1/(s · profileX s)³`. -/
private def gapPsi0 (s : ℝ) : ℝ := -(1 / (s * Work.OddEnvelope.profileX s) ^ 3)

/-- **Lipschitz bound for `Ψ₀`** on the gap. -/
private lemma gapPsi0_lipschitz {a b : ℝ}
    (ha : a ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) (hb : b ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) :
    |gapPsi0 a - gapPsi0 b| ≤ 200 * |a - b| := by
  have hA := abs_mul_profileX_sub_le ha hb
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hpa : 2 / 3 ≤ Work.OddEnvelope.profileX a :=
    two_thirds_le_profileX (le_of_lt ha0) (by linarith [ha.2])
  have hpb : 2 / 3 ≤ Work.OddEnvelope.profileX b :=
    two_thirds_le_profileX (le_of_lt hb0) (by linarith [hb.2])
  have hAmin : 1 / 2 ≤ a * Work.OddEnvelope.profileX a := by
    have h := mul_le_mul ha.1 hpa (by norm_num : (0 : ℝ) ≤ 2 / 3) (le_of_lt ha0)
    norm_num at h
    exact h
  have hBmin : 1 / 2 ≤ b * Work.OddEnvelope.profileX b := by
    have h := mul_le_mul hb.1 hpb (by norm_num : (0 : ℝ) ≤ 2 / 3) (le_of_lt hb0)
    norm_num at h
    exact h
  have hAmax : a * Work.OddEnvelope.profileX a ≤ 1 := by
    have := Work.OddEnvelope.profileX_lt_one ha0
    nlinarith [ha.2]
  have hBmax : b * Work.OddEnvelope.profileX b ≤ 1 := by
    have := Work.OddEnvelope.profileX_lt_one hb0
    nlinarith [hb.2]
  have hcube := abs_inv_cube_sub_le hAmin hAmax hBmin hBmax
  have heq : gapPsi0 a - gapPsi0 b
      = -(1 / (a * Work.OddEnvelope.profileX a) ^ 3
          - 1 / (b * Work.OddEnvelope.profileX b) ^ 3) := by
    simp only [gapPsi0]; ring
  rw [heq, abs_neg]
  nlinarith [hcube, abs_nonneg (a - b), hA]

/-- **Lipschitz bound for `H s = ξ / profileX' s + s`** on the gap. -/
private lemma gapH_lipschitz {ξ : ℝ} (hξ : |ξ| ≤ 1) {a b : ℝ}
    (ha : a ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) (hb : b ∈ Set.Icc (3 / 4 : ℝ) (9 / 10)) :
    |(ξ / deriv Work.OddEnvelope.profileX a + a)
      - (ξ / deriv Work.OddEnvelope.profileX b + b)| ≤ 10 * |a - b| := by
  have hpd := abs_deriv_profileX_sub_le ha hb
  have ha3 : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX a| :=
    one_third_le_abs_deriv_profileX ha.1 ha.2
  have hb3 : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX b| :=
    one_third_le_abs_deriv_profileX hb.1 hb.2
  have hpa : 0 < |deriv Work.OddEnvelope.profileX a| := by linarith
  have hpb : 0 < |deriv Work.OddEnvelope.profileX b| := by linarith
  have hne_a : deriv Work.OddEnvelope.profileX a ≠ 0 := abs_pos.mp hpa
  have hne_b : deriv Work.OddEnvelope.profileX b ≠ 0 := abs_pos.mp hpb
  have h1 : |1 / deriv Work.OddEnvelope.profileX a - 1 / deriv Work.OddEnvelope.profileX b|
      ≤ 9 * |a - b| := by
    have hkey : 1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b
        = (deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a)
          / (deriv Work.OddEnvelope.profileX a * deriv Work.OddEnvelope.profileX b) := by
      field_simp
    rw [hkey, abs_div, abs_mul]
    rw [div_le_iff₀ (mul_pos hpa hpb)]
    have hd' : |deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a|
        ≤ |a - b| := by
      rw [abs_sub_comm]; exact hpd
    have hprod : (1 / 9 : ℝ) ≤ |deriv Work.OddEnvelope.profileX a|
        * |deriv Work.OddEnvelope.profileX b| := by
      have h := mul_le_mul ha3 hb3 (by norm_num : (0 : ℝ) ≤ 1 / 3) (le_of_lt hpa)
      norm_num at h
      exact h
    calc |deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a|
        ≤ |a - b| := hd'
      _ = 9 * |a - b| * (1 / 9) := by ring
      _ ≤ 9 * |a - b| * (|deriv Work.OddEnvelope.profileX a|
            * |deriv Work.OddEnvelope.profileX b|) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  have h2 : |(ξ / deriv Work.OddEnvelope.profileX a + a)
      - (ξ / deriv Work.OddEnvelope.profileX b + b)|
      ≤ |ξ| * |1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b| + |a - b| := by
    have hsplit : (ξ / deriv Work.OddEnvelope.profileX a + a)
        - (ξ / deriv Work.OddEnvelope.profileX b + b)
        = ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b) + (a - b) := by
      field_simp
      ring
    rw [hsplit]
    calc |ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b) + (a - b)|
        ≤ |ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b)| + |a - b| := abs_add_le _ _
      _ = |ξ| * |1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b| + |a - b| := by rw [abs_mul]
  have h3 : |ξ| * |1 / deriv Work.OddEnvelope.profileX a
      - 1 / deriv Work.OddEnvelope.profileX b| ≤ 9 * |a - b| := by
    calc |ξ| * |1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b|
        ≤ 1 * (9 * |a - b|) := mul_le_mul hξ h1 (abs_nonneg _) (by norm_num)
      _ = 9 * |a - b| := by ring
  linarith [h2, h3, abs_nonneg (a - b)]

/-- The semicircle identity at a slope: `(2 p'² - p p'')/p'³ = Ψ₀ σ`. -/
private lemma profileX_slope_second {σ : ℝ} (hσ : 0 < σ) :
    (2 * (deriv Work.OddEnvelope.profileX σ) ^ 2
        - Work.OddEnvelope.profileX σ * deriv (deriv Work.OddEnvelope.profileX) σ)
        / (deriv Work.OddEnvelope.profileX σ) ^ 3 = gapPsi0 σ := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := Work.OddEnvelope.Close.profileX_deriv_formulas σ
  have hp : Work.OddEnvelope.profileX σ ≠ 0 := ne_of_gt (Work.OddEnvelope.profileX_pos σ)
  have hs : σ ≠ 0 := ne_of_gt hσ
  rw [hd4, hd1]
  simp only [gapPsi0]
  field_simp
  try ring

end



/-! ## Elementary estimate lemmas for the three deviations -/

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc |a + (-b)| ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- The value deviation on the gap. -/
private lemma gap_value_dev {a b ξ w : ℝ} {η ε : ℝ}
    (hd : |a - b| ≤ 3 * η) (hξ : |ξ| ≤ 1) (hw : |w| ≤ ε) :
    |a * ξ - w - b * ξ| ≤ 3 * η + ε := by
  have hη0 : 0 ≤ η := by linarith [abs_nonneg (a - b), hd]
  have h1 : a * ξ - w - b * ξ = (a - b) * ξ - w := by ring
  rw [h1]
  have h2 := abs_sub_le_abs_add ((a - b) * ξ) w
  rw [abs_mul] at h2
  have h4 : |a - b| * |ξ| ≤ (3 * η) * 1 :=
    mul_le_mul hd hξ (abs_nonneg _) (by linarith)
  linarith [h2, h4, hw]

/-- The first-derivative deviation on the gap. -/
private lemma gap_deriv_dev {a b ξ v v₀ w : ℝ} {η ε : ℝ}
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hH : |(ξ / v₀ + a) + 1 / b| ≤ 10 * |a - b|)
    (hd : |a - b| ≤ 3 * η) (hξ : |ξ| ≤ 1) (hvv : |v - v₀| ≤ η)
    (hv : 1 / 4 ≤ |v|) (hv₀ : 1 / 3 ≤ |v₀|) (hw : |w| ≤ ε) :
    |-(ξ + a * v) / v + w / v - 1 / b| ≤ 100 * (η + ε) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; norm_num at hv
  have hv₀0 : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀; norm_num at hv₀
  have hid : (ξ + a * v) / v + 1 / b = (ξ / v₀ + a) + 1 / b + ξ * (1 / v - 1 / v₀) := by
    field_simp
    ring
  have h1 : |(ξ + a * v) / v + 1 / b| ≤ 10 * |a - b| + |ξ| * |1 / v - 1 / v₀| := by
    rw [hid]
    calc |(ξ / v₀ + a) + 1 / b + ξ * (1 / v - 1 / v₀)|
        ≤ |(ξ / v₀ + a) + 1 / b| + |ξ * (1 / v - 1 / v₀)| := abs_add_le _ _
      _ ≤ 10 * |a - b| + |ξ| * |1 / v - 1 / v₀| := by
          rw [abs_mul]; linarith [hH]
  have h2 : |1 / v - 1 / v₀| ≤ 12 * η := by
    have hkey : 1 / v - 1 / v₀ = (v₀ - v) / (v * v₀) := by field_simp
    rw [hkey, abs_div, abs_mul]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < |v| * |v₀|)]
    have hv' : |v₀ - v| ≤ η := by rw [abs_sub_comm]; exact hvv
    have hprod : (1 / 4) * (1 / 3) ≤ |v| * |v₀| :=
      mul_le_mul hv hv₀ (by norm_num) (by linarith)
    nlinarith [hv', hprod, abs_nonneg (v₀ - v), hη]
  have h3 : |ξ| * |1 / v - 1 / v₀| ≤ 12 * η := by
    calc |ξ| * |1 / v - 1 / v₀| ≤ 1 * (12 * η) :=
          mul_le_mul hξ h2 (abs_nonneg _) (by norm_num)
      _ = 12 * η := by ring
  have h4 : |w / v| ≤ 4 * ε := by
    rw [abs_div, div_le_iff₀ (by linarith : (0 : ℝ) < |v|)]
    nlinarith [hw, hv, hε]
  have hsplit : -(ξ + a * v) / v + w / v - 1 / b
      = -((ξ + a * v) / v + 1 / b) + w / v := by ring
  rw [hsplit]
  have h6 : |-((ξ + a * v) / v + 1 / b) + w / v|
      ≤ |(ξ + a * v) / v + 1 / b| + |w / v| := by
    have h : -((ξ + a * v) / v + 1 / b) + w / v
        = -((ξ + a * v) / v + 1 / b - w / v) := by ring
    rw [h, abs_neg]
    exact abs_sub_le_abs_add ((ξ + a * v) / v + 1 / b) (w / v)
  linarith [h1, h3, h4, h6]

/-- `|v³ - v₀³| ≤ (19/4)|v - v₀|` under the gap bounds on `v`, `v₀`. -/
private lemma abs_cube_sub_le_gap {v v₀ : ℝ} (hv : |v| ≤ 3 / 2) (hv₀ : |v₀| ≤ 1) :
    |v ^ 3 - v₀ ^ 3| ≤ (19 / 4) * |v - v₀| := by
  have hfac : v ^ 3 - v₀ ^ 3 = (v - v₀) * (v ^ 2 + v * v₀ + v₀ ^ 2) := by ring
  have hv2 : |v| ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith [abs_nonneg v]
  have hv₀2 : |v₀| ^ 2 ≤ 1 := by nlinarith [abs_nonneg v₀]
  have hv₀0 : (0 : ℝ) ≤ |v₀| := abs_nonneg _
  have hv0 : (0 : ℝ) ≤ |v| := abs_nonneg _
  have h3 : |v ^ 2 + v * v₀ + v₀ ^ 2| ≤ 19 / 4 := by
    calc |v ^ 2 + v * v₀ + v₀ ^ 2| ≤ |v ^ 2| + |v * v₀| + |v₀ ^ 2| := by
          have a1 := abs_add_le (v ^ 2 + v * v₀) (v₀ ^ 2)
          have a2 := abs_add_le (v ^ 2) (v * v₀)
          linarith
      _ = |v| ^ 2 + |v| * |v₀| + |v₀| ^ 2 := by rw [abs_pow, abs_pow, abs_mul]
      _ ≤ (3 / 2) ^ 2 + (3 / 2) * 1 + 1 := by
          have h4 : |v| * |v₀| ≤ (3 / 2) * 1 := mul_le_mul hv hv₀ hv₀0 (by norm_num)
          linarith
      _ = 19 / 4 := by norm_num
  rw [hfac, abs_mul]
  calc |v - v₀| * |v ^ 2 + v * v₀ + v₀ ^ 2| ≤ |v - v₀| * (19 / 4) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg (v - v₀))
    _ = 19 / 4 * |v - v₀| := by ring

/-- The second-derivative data deviation on the gap. -/
private lemma gap_second_dev {v v₀ X2 p2 ξ p h₁ h₂ : ℝ} {η ε : ℝ}
    (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hvlo : 1 / 4 ≤ |v|) (hvhi : |v| ≤ 3 / 2) (hv₀lo : 1 / 3 ≤ |v₀|) (hv₀hi : |v₀| ≤ 1)
    (hvv : |v - v₀| ≤ η) (hX2 : |X2| ≤ 3 / 2) (hp2 : |p2| ≤ 1) (hp : |p| ≤ 1)
    (hξp : |ξ - p| ≤ η) (hpX : |p2 - X2| ≤ η) (hh₁ : |h₁| ≤ ε) (hh₂ : |h₂| ≤ ε) :
    |(2 * v ^ 2 - h₂ * v - (ξ - h₁) * X2) / v ^ 3 - (2 * v₀ ^ 2 - p * p2) / v₀ ^ 3|
      ≤ 40000 * (η + ε) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hvlo; norm_num at hvlo
  have hv₀0 : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀lo; norm_num at hv₀lo
  have hkey : (2 * v ^ 2 - h₂ * v - (ξ - h₁) * X2) / v ^ 3 - (2 * v₀ ^ 2 - p * p2) / v₀ ^ 3
      = ((2 * v ^ 2 - h₂ * v - (ξ - h₁) * X2) * v₀ ^ 3 - (2 * v₀ ^ 2 - p * p2) * v ^ 3)
        / (v ^ 3 * v₀ ^ 3) := by
    field_simp
  rw [hkey, abs_div, abs_mul, abs_pow, abs_pow]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < |v| ^ 3 * |v₀| ^ 3)]
  have hdec : (2 * v ^ 2 - h₂ * v - (ξ - h₁) * X2) * v₀ ^ 3 - (2 * v₀ ^ 2 - p * p2) * v ^ 3
      = 2 * v ^ 2 * v₀ ^ 2 * (v₀ - v) - h₂ * v * v₀ ^ 3
        + (-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3 + h₁ * X2 * v₀ ^ 3
            + p * p2 * (v ^ 3 - v₀ ^ 3)) := by ring
  rw [hdec]
  have hcube := abs_cube_sub_le_gap hvhi hv₀hi
  have hcube' : |v ^ 3 - v₀ ^ 3| ≤ 19 / 4 * η := by
    calc |v ^ 3 - v₀ ^ 3| ≤ 19 / 4 * |v - v₀| := hcube
      _ ≤ 19 / 4 * η := mul_le_mul_of_nonneg_left hvv (by norm_num)
  have hA : |2 * v ^ 2 * v₀ ^ 2 * (v₀ - v)| ≤ 9 / 2 * η := by
    have hval : |2 * v ^ 2 * v₀ ^ 2 * (v₀ - v)| = 2 * |v| ^ 2 * |v₀| ^ 2 * |v₀ - v| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      try ring
    rw [hval]
    have hv2 : |v| ^ 2 ≤ (3 / 2) ^ 2 := by nlinarith [abs_nonneg v]
    have hv₀2 : |v₀| ^ 2 ≤ 1 := by nlinarith [abs_nonneg v₀]
    have hvv' : |v₀ - v| ≤ η := by rw [abs_sub_comm]; exact hvv
    have h1 : 2 * |v| ^ 2 * |v₀| ^ 2 ≤ 2 * (3 / 2) ^ 2 * 1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hv2 (by positivity)
      · exact hv₀2
      · positivity
      · positivity
    calc 2 * |v| ^ 2 * |v₀| ^ 2 * |v₀ - v| ≤ 2 * (3 / 2) ^ 2 * 1 * η :=
          mul_le_mul h1 hvv' (abs_nonneg _) (by positivity)
      _ = 9 / 2 * η := by ring
  have hB : |h₂ * v * v₀ ^ 3| ≤ 3 / 2 * ε := by
    have hval : |h₂ * v * v₀ ^ 3| = |h₂| * |v| * |v₀| ^ 3 := by
      simp only [abs_mul, abs_pow]
      try ring
    rw [hval]
    have hv₀3 : |v₀| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg v₀) hv₀hi
    have h1 : |h₂| * |v| ≤ ε * (3 / 2) := mul_le_mul hh₂ hvhi (abs_nonneg _) hε
    calc |h₂| * |v| * |v₀| ^ 3 ≤ ε * (3 / 2) * 1 :=
          mul_le_mul h1 hv₀3 (by positivity) (by positivity)
      _ = 3 / 2 * ε := by ring
  have hC : |(-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3 + h₁ * X2 * v₀ ^ 3
      + p * p2 * (v ^ 3 - v₀ ^ 3))| ≤ 47 / 4 * η + 3 / 2 * ε := by
    have hv₀3 : |v₀| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg v₀) hv₀hi
    have h1 : |-(ξ - p) * X2 * v₀ ^ 3| ≤ 3 / 2 * η := by
      have hval : |-(ξ - p) * X2 * v₀ ^ 3| = |ξ - p| * |X2| * |v₀| ^ 3 := by
        simp only [abs_mul, abs_neg, abs_pow]
        try ring
      rw [hval]
      calc |ξ - p| * |X2| * |v₀| ^ 3 ≤ η * (3 / 2) * 1 :=
            mul_le_mul (mul_le_mul hξp hX2 (abs_nonneg _) hη) hv₀3 (by positivity)
              (by positivity)
        _ = 3 / 2 * η := by ring
    have h2 : |p * (p2 - X2) * v₀ ^ 3| ≤ η := by
      have hval : |p * (p2 - X2) * v₀ ^ 3| = |p| * |p2 - X2| * |v₀| ^ 3 := by
        simp only [abs_mul, abs_pow]
      rw [hval]
      calc |p| * |p2 - X2| * |v₀| ^ 3 ≤ 1 * η * 1 :=
            mul_le_mul (mul_le_mul hp hpX (abs_nonneg _) (by norm_num)) hv₀3
              (by positivity) (by positivity)
        _ = η := by ring
    have h3 : |h₁ * X2 * v₀ ^ 3| ≤ 3 / 2 * ε := by
      have hval : |h₁ * X2 * v₀ ^ 3| = |h₁| * |X2| * |v₀| ^ 3 := by
        simp only [abs_mul, abs_pow]
      rw [hval]
      calc |h₁| * |X2| * |v₀| ^ 3 ≤ ε * (3 / 2) * 1 :=
            mul_le_mul (mul_le_mul hh₁ hX2 (abs_nonneg _) hε) hv₀3 (by positivity)
              (by positivity)
        _ = 3 / 2 * ε := by ring
    have h4 : |p * p2 * (v ^ 3 - v₀ ^ 3)| ≤ 19 / 4 * η := by
      have hval : |p * p2 * (v ^ 3 - v₀ ^ 3)| = |p| * |p2| * |v ^ 3 - v₀ ^ 3| := by
        simp only [abs_mul]
        try ring
      rw [hval]
      calc |p| * |p2| * |v ^ 3 - v₀ ^ 3| ≤ 1 * 1 * (19 / 4 * η) :=
            mul_le_mul (mul_le_mul hp hp2 (abs_nonneg _) (by norm_num)) hcube'
              (by positivity) (by positivity)
        _ = 19 / 4 * η := by ring
    have e3 := abs_add_le (-(ξ - p) * X2 * v₀ ^ 3) (p * (p2 - X2) * v₀ ^ 3)
    have e2 := abs_add_le (-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3)
      (h₁ * X2 * v₀ ^ 3)
    have e1 := abs_add_le
      (-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3 + h₁ * X2 * v₀ ^ 3)
      (p * p2 * (v ^ 3 - v₀ ^ 3))
    linarith [e1, e2, e3, h1, h2, h3, h4]
  have hAB : |2 * v ^ 2 * v₀ ^ 2 * (v₀ - v) - h₂ * v * v₀ ^ 3| ≤ 9 / 2 * η + 3 / 2 * ε := by
    have := abs_sub_le_abs_add (2 * v ^ 2 * v₀ ^ 2 * (v₀ - v)) (h₂ * v * v₀ ^ 3)
    linarith [this, hA, hB]
  have hABC : |2 * v ^ 2 * v₀ ^ 2 * (v₀ - v) - h₂ * v * v₀ ^ 3
      + (-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3 + h₁ * X2 * v₀ ^ 3
          + p * p2 * (v ^ 3 - v₀ ^ 3))| ≤ 9 / 2 * η + 3 / 2 * ε + (47 / 4 * η + 3 / 2 * ε) := by
    have := abs_add_le (2 * v ^ 2 * v₀ ^ 2 * (v₀ - v) - h₂ * v * v₀ ^ 3)
      (-(ξ - p) * X2 * v₀ ^ 3 + p * (p2 - X2) * v₀ ^ 3 + h₁ * X2 * v₀ ^ 3
        + p * p2 * (v ^ 3 - v₀ ^ 3))
    linarith [this, hAB, hC]
  have hprod : 1 / 1728 ≤ |v| ^ 3 * |v₀| ^ 3 := by
    have h1 : ((1 : ℝ) / 4) ^ 3 ≤ |v| ^ 3 := pow_le_pow_left₀ (by norm_num) hvlo 3
    have h2 : ((1 : ℝ) / 3) ^ 3 ≤ |v₀| ^ 3 := pow_le_pow_left₀ (by norm_num) hv₀lo 3
    have h3 : (0 : ℝ) ≤ |v| ^ 3 := by positivity
    have h4 : ((1 : ℝ) / 1728) ≤ ((1 : ℝ) / 4) ^ 3 * ((1 : ℝ) / 3) ^ 3 := by norm_num
    calc ((1 : ℝ) / 1728) ≤ ((1 : ℝ) / 4) ^ 3 * ((1 : ℝ) / 3) ^ 3 := h4
      _ ≤ |v| ^ 3 * |v₀| ^ 3 := mul_le_mul h1 h2 (by norm_num) h3
  have hfin : 40000 * (η + ε) * (1 / 1728) ≤ 40000 * (η + ε) * (|v| ^ 3 * |v₀| ^ 3) :=
    mul_le_mul_of_nonneg_left hprod (by positivity)
  nlinarith [hABC, hfin, hη, hε]


/-! ## The main theorem -/

set_option maxHeartbeats 4000000

theorem envelopeLeft_close_of_state_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧
      ∀ {ε η : ℝ} {h X Y : ℝ → ℝ} {Z : ℝ → Work.OddVolterra.St},
      η ≤ η₀ →
      Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      (∀ s ∈ Set.Icc (1 / 2 : ℝ) 1,
        |Z s 0 - Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (fun u : ℝ => Z u 0) s - deriv Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (deriv (fun u : ℝ => Z u 0)) s -
            deriv (deriv Work.OddEnvelope.profileX) s| ≤ η) →
      (∀ s : ℝ, 1 / 2 ≤ s → s ≤ 1 → X s = Z s 0 ∧ Y s = Z s 1) →
      ∀ ξ : ℝ, Work.OddEnvelope.tStar < ξ → ξ < Work.OddCurve.LowSlope.cStar →
        |Work.OddEnvelope.envelopeProfile h X Y (-ξ) - Work.OddEnvelope.semicircle (-ξ)| ≤
            C * (η + ε) ∧
        |deriv (Work.OddEnvelope.envelopeProfile h X Y) (-ξ) -
            deriv Work.OddEnvelope.semicircle (-ξ)| ≤ C * (η + ε) ∧
        |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (-ξ) -
            deriv (deriv Work.OddEnvelope.semicircle) (-ξ)| ≤ C * (η + ε) := by
  refine ⟨1000000, 1 / 1000, by norm_num, by norm_num, ?_⟩
  intro ε η h X Y Z hη hb H hcl hXY ξ hξ1 hξ2
  -- nonnegativity of the two parameters
  have hη0 : 0 ≤ η := by
    have h := (hcl (1 / 2) (by norm_num)).1
    exact le_trans (abs_nonneg _) h
  have hε0 : 0 ≤ ε := by
    have hbd := hb.deriv_bound (k := 0) (by omega) 0
    exact le_trans (abs_nonneg _) (by simpa using hbd)
  -- the point `ξ` and the two slopes
  have hξpos : 0 < ξ := lt_trans Work.OddEnvelope.tStar_pos hξ1
  have hξlt1 : ξ < 1 := lt_trans hξ2 (lt_trans cStar_lt_four_fifths (by norm_num))
  have hξI : ξ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hξpos, hξlt1⟩
  have hξabs : |ξ| ≤ 1 := abs_le.mpr ⟨by linarith, le_of_lt hξlt1⟩
  set σ := Work.OddEnvelope.slopeRight X ξ with hσdef
  have hσpos : 0 < σ := H.toChordCurve_x.slopeRight_pos hξI
  have hXσ : X σ = ξ := H.toChordCurve_x.slopeRight_eq hξI
  have hξ2pos : 0 < 1 - ξ ^ 2 := by nlinarith
  set σ₁ := Real.sqrt (1 - ξ ^ 2) / ξ with hσ₁def
  have hσ₁pos : 0 < σ₁ := by
    rw [hσ₁def]; exact div_pos (Real.sqrt_pos.mpr hξ2pos) hξpos
  have hσ₁ξ : σ₁ * ξ = Real.sqrt (1 - ξ ^ 2) := by
    rw [hσ₁def]; field_simp
  have hprofσ₁ : Work.OddEnvelope.profileX σ₁ = ξ := by
    have hsq : σ₁ ^ 2 = (1 - ξ ^ 2) / ξ ^ 2 := by
      rw [hσ₁def, div_pow, Real.sq_sqrt (le_of_lt hξ2pos)]
    rw [Work.OddEnvelope.profileX,
      show (1 : ℝ) + σ₁ ^ 2 = (1 / ξ) ^ 2 by rw [hsq]; field_simp; ring,
      Real.sqrt_sq (le_of_lt (one_div_pos.mpr hξpos))]
    field_simp
  -- the two slopes lie in `(3/4, 9/10)`
  have hσlt : σ < 9 / 10 := by
    have hX9 : X (9 / 10) = Work.OddEnvelope.tStar := by
      have hτ : (1 : ℝ) - Work.OddEnvelope.tau = 9 / 10 := by norm_num [Work.OddEnvelope.tau]
      rw [← hτ, Work.OddEnvelope.tStar]
      exact H.x_tail _ le_rfl
    by_contra hcon
    have hle : (9 / 10 : ℝ) ≤ σ := le_of_not_gt hcon
    have h9le : ξ ≤ X (9 / 10) := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · have h := H.toChordCurve_x.strictAntiOn (by norm_num : (0 : ℝ) < 9 / 10) hσpos hlt
        rw [hXσ] at h
        exact le_of_lt h
      · rw [heq, hXσ]
    rw [hX9] at h9le
    linarith [hξ1]
  have hσgt : 3 / 4 < σ := by
    have hcl34 : |X (3 / 4) - 4 / 5| ≤ η := by
      have h := (hcl (3 / 4) (by norm_num)).1
      have hxq : X (3 / 4) = Z (3 / 4) 0 :=
        (hXY (3 / 4) (by norm_num) (by norm_num)).1
      rw [hxq]
      rwa [profileX_three_quarters] at h
    by_contra hcon
    have hle : σ ≤ 3 / 4 := le_of_not_gt hcon
    have h34le : X (3 / 4) ≤ ξ := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · have h := H.toChordCurve_x.strictAntiOn hσpos (by norm_num : (0 : ℝ) < 3 / 4) hlt
        rw [hXσ] at h
        exact le_of_lt h
      · rw [← heq, hXσ]
    have hlow : 4 / 5 - η ≤ X (3 / 4) := by
      have := (abs_le.mp hcl34).1
      linarith
    linarith [h34le, hlow, hξ2, hη, cStar_add_one_thousandth_lt]
  have hσ₁gt : 4 / 5 < σ₁ := by
    have hcStar45 : Work.OddCurve.LowSlope.cStar = Work.OddEnvelope.profileX (4 / 5) := by
      rw [Work.OddCurve.LowSlope.cStar, Work.OddEnvelope.profileX, one_div]
    by_contra hcon
    have hle : σ₁ ≤ 4 / 5 := le_of_not_gt hcon
    have h4le : Work.OddEnvelope.profileX (4 / 5) ≤ ξ := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · have h := Work.OddEnvelope.profileX_strictAntiOn hσ₁pos
          (by norm_num : (0 : ℝ) < 4 / 5) hlt
        rw [hprofσ₁] at h
        exact le_of_lt h
      · rw [← heq, hprofσ₁]
    rw [← hcStar45] at h4le
    linarith [hξ2]
  have hσ₁lt : σ₁ < 9 / 10 := by
    have htStar9 : Work.OddEnvelope.profileX (9 / 10) = Work.OddEnvelope.tStar := by
      simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.tau]; norm_num
    by_contra hcon
    have hle : (9 / 10 : ℝ) ≤ σ₁ := le_of_not_gt hcon
    have h9le : ξ ≤ Work.OddEnvelope.profileX (9 / 10) := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · have h := Work.OddEnvelope.profileX_strictAntiOn (by norm_num : (0 : ℝ) < 9 / 10)
          hσ₁pos hlt
        rw [hprofσ₁] at h
        exact le_of_lt h
      · rw [heq, hprofσ₁]
    rw [htStar9] at h9le
    linarith [hξ1]
  have hσI : σ ∈ Set.Icc (3 / 4 : ℝ) (9 / 10) := ⟨le_of_lt hσgt, le_of_lt hσlt⟩
  have hσ₁I : σ₁ ∈ Set.Icc (3 / 4 : ℝ) (9 / 10) := ⟨by linarith, le_of_lt hσ₁lt⟩
  -- the distance between the two slopes
  have hσdiff : |σ - σ₁| ≤ 3 * η := by
    have h := abs_sub_le_three_abs_profileX_sub hσI.1 hσI.2 hσ₁I.1 hσ₁I.2
    have h2 : |Work.OddEnvelope.profileX σ - Work.OddEnvelope.profileX σ₁| ≤ η := by
      have hcl' := (hcl σ ⟨by linarith [hσgt], by linarith [hσlt]⟩).1
      have hxq : X σ = Z σ 0 := hXY σ (by linarith [hσgt]) (by linarith [hσlt]) |>.1
      rw [← hxq, hXσ] at hcl'
      rw [hprofσ₁, abs_sub_comm]
      exact hcl'
    linarith [h, h2]
  -- the derivative data at `σ`
  have hXYev : X =ᶠ[𝓝 σ] (fun u : ℝ => Z u 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show σ ∈ Set.Ioo (1 / 2 : ℝ) 1 from ⟨by linarith [hσgt], by linarith [hσlt]⟩)]
      with u hu
    exact (hXY u (le_of_lt hu.1) (le_of_lt hu.2)).1
  have hdX : deriv X σ = deriv (fun u : ℝ => Z u 0) σ := Filter.EventuallyEq.deriv_eq hXYev
  have hddX : deriv (deriv X) σ = deriv (deriv (fun u : ℝ => Z u 0)) σ :=
    Filter.EventuallyEq.deriv_eq (deriv_eventuallyEq hXYev)
  have hclσ := hcl σ ⟨by linarith [hσgt], by linarith [hσlt]⟩
  have hd1 : |deriv X σ - deriv Work.OddEnvelope.profileX σ| ≤ η := by
    rw [hdX]; exact hclσ.2.1
  have hd2 : |deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ| ≤ η := by
    rw [hddX]; exact hclσ.2.2
  have hb1 : |h σ| ≤ ε := by
    have hbd := hb.deriv_bound (k := 0) (by omega) σ
    simpa using hbd
  have hb2 : |deriv h σ| ≤ ε := by
    have hbd := hb.deriv_bound (k := 1) (by omega) σ
    simpa [iteratedDeriv_one] using hbd
  have hb3 : |deriv (deriv h) σ| ≤ ε := by
    have hbd := hb.deriv_bound (k := 2) (by omega) σ
    have e : iteratedDeriv 2 h σ = deriv (deriv h) σ := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rwa [e] at hbd
  -- the bounds on the jets used by the estimates
  have hp1 : |Work.OddEnvelope.profileX σ| ≤ 1 := by
    rw [abs_of_pos (Work.OddEnvelope.profileX_pos σ)]
    exact le_of_lt (Work.OddEnvelope.profileX_lt_one hσpos)
  have hp2 : |deriv (deriv Work.OddEnvelope.profileX) σ| ≤ 1 :=
    profileX_deriv2_abs_le_one hσI.1 hσI.2
  have hpX : |deriv (deriv Work.OddEnvelope.profileX) σ - deriv (deriv X) σ| ≤ η := by
    rw [abs_sub_comm]; exact hd2
  have hX2 : |deriv (deriv X) σ| ≤ 3 / 2 := by
    have h := abs_add_le (deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ)
      (deriv (deriv Work.OddEnvelope.profileX) σ)
    have h' : |deriv (deriv X) σ|
        ≤ |deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ|
          + |deriv (deriv Work.OddEnvelope.profileX) σ| := by
      simpa using h
    linarith [h', hd2, hp2, hη]
  have hv₀lo : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX σ| :=
    one_third_le_abs_deriv_profileX hσI.1 hσI.2
  have hv₀hi : |deriv Work.OddEnvelope.profileX σ| ≤ 1 :=
    profileX_deriv_abs_le_one hσpos
  have hvlo : 1 / 4 ≤ |deriv X σ| := by
    have h := abs_add_le (deriv Work.OddEnvelope.profileX σ - deriv X σ) (deriv X σ)
    have h' : |deriv Work.OddEnvelope.profileX σ|
        ≤ |deriv Work.OddEnvelope.profileX σ - deriv X σ| + |deriv X σ| := by
      simpa using h
    have h3 : |deriv Work.OddEnvelope.profileX σ - deriv X σ| ≤ η := by
      rw [abs_sub_comm]; exact hd1
    linarith [h', h3, hv₀lo, hη]
  have hvhi : |deriv X σ| ≤ 3 / 2 := by
    have h := abs_add_le (deriv X σ - deriv Work.OddEnvelope.profileX σ)
      (deriv Work.OddEnvelope.profileX σ)
    have h' : |deriv X σ|
        ≤ |deriv X σ - deriv Work.OddEnvelope.profileX σ|
          + |deriv Work.OddEnvelope.profileX σ| := by
      simpa using h
    linarith [h', hd1, hv₀hi, hη]
  have hξp : |ξ - Work.OddEnvelope.profileX σ| ≤ η := by
    have hcl' := hclσ.1
    have hxq : X σ = Z σ 0 := hXY σ (by linarith [hσgt]) (by linarith [hσlt]) |>.1
    rw [← hxq, hXσ] at hcl'
    exact hcl'
  have hvne : deriv X σ ≠ 0 := by
    intro hzero; rw [hzero] at hvlo; norm_num at hvlo
  -- the value `H σ₁`
  have hHσ₁ : ξ / deriv Work.OddEnvelope.profileX σ₁ + σ₁ = -1 / σ₁ := by
    have hd : deriv Work.OddEnvelope.profileX σ₁ = -σ₁ * ξ ^ 3 := by
      rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ₁).1, hprofσ₁]
    have hsq : σ₁ ^ 2 * ξ ^ 2 = 1 - ξ ^ 2 := by
      rw [← mul_pow, hσ₁ξ, Real.sq_sqrt (le_of_lt hξ2pos)]
    rw [hd]
    field_simp
    nlinarith [hsq]
  have hH : |(ξ / deriv Work.OddEnvelope.profileX σ + σ) + 1 / σ₁| ≤ 10 * |σ - σ₁| := by
    have h := gapH_lipschitz hξabs hσI hσ₁I
    rw [hHσ₁] at h
    have h' : (ξ / deriv Work.OddEnvelope.profileX σ + σ) - (-1 / σ₁)
        = (ξ / deriv Work.OddEnvelope.profileX σ + σ) + 1 / σ₁ := by ring
    rwa [h'] at h
  -- the value of the profile on the left branch
  have hval_slope : Work.OddEnvelope.envelopeProfile h X Y (-ξ) = σ * ξ - h σ := by
    have ht : (-ξ) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith [hξlt1], by linarith [hξpos]⟩
    rw [Work.OddEnvelope.envelopeProfile_of_neg ht, Work.OddEnvelope.envelopeLeft]
    have hsl : Work.OddEnvelope.slopeLeft X (-ξ) = σ := by
      rw [Work.OddEnvelope.slopeLeft, neg_neg, hσdef, Work.OddEnvelope.slopeRight]
    rw [hsl]
    ring
  have hsem_val : Work.OddEnvelope.semicircle (-ξ) = σ₁ * ξ := by
    rw [Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
  -- **estimate 1**
  have hval1 : |Work.OddEnvelope.envelopeProfile h X Y (-ξ) - Work.OddEnvelope.semicircle (-ξ)|
      ≤ 1000000 * (η + ε) := by
    rw [hval_slope, hsem_val]
    have h := gap_value_dev (a := σ) (b := σ₁) (ξ := ξ) (w := h σ) hσdiff hξabs hb1
    linarith [h, hη0, hε0]
  -- **estimate 2**
  have hder1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (-ξ)
      - deriv Work.OddEnvelope.semicircle (-ξ)| ≤ 1000000 * (η + ε) := by
    have hprof_deriv : deriv (Work.OddEnvelope.envelopeProfile h X Y) (-ξ)
        = -(ξ + σ * deriv X σ - deriv h σ) / deriv X σ := by
      have ht : (-ξ) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith [hξlt1], by linarith [hξpos]⟩
      rw [Work.OddEnvelope.deriv_envelopeProfile_of_neg H ht]
      have hsl : Work.OddEnvelope.slopeRight X (-(-ξ)) = σ := by
        rw [neg_neg, hσdef, Work.OddEnvelope.slopeRight]
      rw [hsl, Work.OddEnvelope.kSlope, hXσ, Work.OddEnvelope.deriv_negH]
      ring_nf
    have hsemi_deriv : deriv Work.OddEnvelope.semicircle (-ξ) = 1 / σ₁ := by
      rw [Work.OddEnvelope.Semicircle.deriv_semicircle
        ⟨by linarith [hξlt1], by linarith [hξpos]⟩, neg_neg,
        Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
      field_simp
    rw [hprof_deriv, hsemi_deriv]
    have hgoal : |(-(ξ + σ * deriv X σ - deriv h σ)) / deriv X σ - 1 / σ₁|
        ≤ 1000000 * (η + ε) := by
      have heq : (-(ξ + σ * deriv X σ - deriv h σ)) / deriv X σ - 1 / σ₁
          = -(ξ + σ * deriv X σ) / deriv X σ + deriv h σ / deriv X σ - 1 / σ₁ := by
        field_simp
        ring
      rw [heq]
      have h := gap_deriv_dev (a := σ) (b := σ₁) (ξ := ξ) (v := deriv X σ)
        (v₀ := deriv Work.OddEnvelope.profileX σ) (w := deriv h σ) hη0 hε0 hH hσdiff hξabs
        hd1 hvlo hv₀lo hb2
      linarith [h, hη0, hε0]
    exact hgoal
  -- **estimate 3**
  have hder2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (-ξ)
      - deriv (deriv Work.OddEnvelope.semicircle) (-ξ)| ≤ 1000000 * (η + ε) := by
    have hprof2 : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (-ξ)
        = (2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
            + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 := by
      rw [deriv_deriv_envelopeProfile_of_neg H hξI hσdef, hXσ]
    have hsemi2 : deriv (deriv Work.OddEnvelope.semicircle) (-ξ) = gapPsi0 σ₁ := by
      rw [deriv_deriv_semicircle ⟨by linarith [hξlt1], by linarith [hξpos]⟩]
      have hL : Work.OddEnvelope.semicircle (-ξ) = σ₁ * ξ := by
        rw [Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
      have hR : gapPsi0 σ₁ = -(1 / (σ₁ * ξ) ^ 3) := by
        simp only [gapPsi0, hprofσ₁]
      rw [hL, hR]
    rw [hprof2, hsemi2]
    have hdata : |(2 * (deriv X σ) ^ 2 - deriv (deriv h) σ * deriv X σ
          - (ξ - deriv h σ) * deriv (deriv X) σ) / (deriv X σ) ^ 3
        - (2 * (deriv Work.OddEnvelope.profileX σ) ^ 2
            - Work.OddEnvelope.profileX σ * deriv (deriv Work.OddEnvelope.profileX) σ)
          / (deriv Work.OddEnvelope.profileX σ) ^ 3| ≤ 40000 * (η + ε) :=
      gap_second_dev (v := deriv X σ) (v₀ := deriv Work.OddEnvelope.profileX σ)
        (X2 := deriv (deriv X) σ) (p2 := deriv (deriv Work.OddEnvelope.profileX) σ)
        (ξ := ξ) (p := Work.OddEnvelope.profileX σ) (h₁ := deriv h σ)
        (h₂ := deriv (deriv h) σ) hη0 hε0 hvlo hvhi hv₀lo hv₀hi hd1 hX2 hp2 hp1
        hξp hpX hb2 hb3
    have hpsi : |(2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
        + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 - gapPsi0 σ|
        ≤ 40000 * (η + ε) := by
      rw [← profileX_slope_second hσpos]
      have heq : (2 * (deriv X σ) ^ 2 - deriv (deriv h) σ * deriv X σ
            - (ξ - deriv h σ) * deriv (deriv X) σ)
          = (2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
              + deriv h σ * deriv (deriv X) σ) := by ring
      rw [← heq]
      exact hdata
    have hlip : |gapPsi0 σ - gapPsi0 σ₁| ≤ 200 * |σ - σ₁| := gapPsi0_lipschitz hσI hσ₁I
    have hsplit : (2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
          + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 - gapPsi0 σ₁
        = (((2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
              + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 - gapPsi0 σ)
            + (gapPsi0 σ - gapPsi0 σ₁)) := by ring
    rw [hsplit]
    have hsum := abs_add_le ((2 * (deriv X σ) ^ 2 - ξ * deriv (deriv X) σ
        - deriv (deriv h) σ * deriv X σ + deriv h σ * deriv (deriv X) σ)
        / (deriv X σ) ^ 3 - gapPsi0 σ) (gapPsi0 σ - gapPsi0 σ₁)
    linarith [hsum, hpsi, hlip, hσdiff, hη0, hε0]
  exact ⟨hval1, hder1, hder2⟩

end Work.OddCurve.LowSlope
