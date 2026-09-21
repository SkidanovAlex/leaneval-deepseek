import Mathlib
import Submission.Work.OddCurve.Free.ChordCurveFree
import Submission.Work.OddVolterra.Free.free_slope_api
import Submission.Work.OddVolterra.Free.free_profile_continuity
import Submission.Work.OddVolterra.Free.envProfileFree_chord
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free
import Submission.Work.OddVolterra.Free.envelopeRight_deriv_Ioo
import Submission.Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free
import Submission.Work.OddEnvelope.Main

/-!
# Concavity and non-degeneracy of the untruncated (free-tip) envelope profile

`Work.OddVolterra.Free.envProfileFree h x y` is the envelope profile of a free-tip envelope curve
`Work.OddCurve.Free.IsEnvelopeCurveFree h x y`: the right branch `envelopeRight h y` for `t > 0`,
the left branch `envelopeLeft h x` for `t < 0` and `1` at `0`.  Unlike
`Work.OddEnvelope.envelopeProfile` it is *not* truncated at `±1`, so the tip of the curve can be
any positive number.

This file proves, with the tip left free, the structural properties of that profile needed by the
spherical-Radon step (`Work.OddVolterra.Free.cent_inertia_of_datum_ball_free`):

* the derivative on each branch and at `0`;
* strict antitonicity of `deriv (envProfileFree h x y)` on a section interval, hence **concavity**
  of the profile on `Icc (-(x c)) (y c)`;
* **positivity of the radicand** `rad0 (envProfileFree h x y) s t` on the open section
  `Ioo (-(x s)) (y s)`.

The concavity argument is the source's (`Work.OddEnvelope.strictConcaveOn_envelopeProfile`): the
logarithmic derivative `kSlope h y` is strictly increasing (`H.shape_y`) while the inverse slope
`slopeRight y` is strictly decreasing, so `deriv` of the right branch is strictly decreasing; the
mirrored statement holds on the left branch, and `deriv (envProfileFree h x y) 0 = 0` (the profile
is the semicircle near `0`, `Work.OddCurve.Free.envelopeProfile_eq_semicircle_free`).
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {h x y : ℝ → ℝ}

/-! ## Surjectivity of the two branches onto a section -/

/-- The right branch `y` of a free-tip envelope curve realises every point of `(0, y c]`. -/
lemma exists_slope_y_lt (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (y c)) : ∃ σ : ℝ, 0 < σ ∧ y σ = t := by
  obtain ⟨σ, -, hσpos, hσ⟩ := H.toChordCurveFree_y.exists_slope_of_mem_Ioc hc ht.1 ht.2.le
  exact ⟨σ, hσpos, hσ⟩

/-- The left branch `x` of a free-tip envelope curve realises every point of `(0, x c]`. -/
lemma exists_slope_x_lt (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (x c)) : ∃ σ : ℝ, 0 < σ ∧ x σ = t := by
  obtain ⟨σ, -, hσpos, hσ⟩ := H.toChordCurveFree_x.exists_slope_of_mem_Ioc hc ht.1 ht.2.le
  exact ⟨σ, hσpos, hσ⟩

/-! ## The derivative of the untruncated profile -/

/-- The derivative of the profile on the right branch. -/
theorem deriv_envProfileFree_of_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c t : ℝ}
    (hc : 0 < c) (ht : t ∈ Set.Ioo (0 : ℝ) (y c)) :
    deriv (envProfileFree h x y) t =
      Work.OddEnvelope.kSlope h y (Work.OddEnvelope.slopeRight y t) := by
  have hev : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeRight h y := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact envProfileFree_of_pos hu.1
  rw [Filter.EventuallyEq.deriv_eq hev]
  exact envelopeRight_deriv_Ioo H.smooth_y H.y_deriv_neg H.smooth_h
    (fun t ht => exists_slope_y_lt H hc ht) t ht

/-- The derivative of the profile on the left branch. -/
theorem deriv_envProfileFree_of_neg (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c t : ℝ}
    (hc : 0 < c) (ht : t ∈ Set.Ioo (-(x c)) (0 : ℝ)) :
    deriv (envProfileFree h x y) t =
      -Work.OddEnvelope.kSlope (Work.OddEnvelope.negH h) x
        (Work.OddEnvelope.slopeRight x (-t)) := by
  have hneg : -t ∈ Set.Ioo (0 : ℝ) (x c) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hev : envProfileFree h x y =ᶠ[𝓝 t]
      (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with u hu
    rw [envProfileFree_of_neg hu, Work.OddEnvelope.envelopeLeft_eq_negH]
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_comp_neg]
  congr 1
  exact envelopeRight_deriv_Ioo H.smooth_x H.x_deriv_neg H.smooth_h.neg
    (fun t ht => exists_slope_x_lt H hc ht) (-t) hneg

/-- The derivative of the profile at `0` is `0` (the profile is the semicircle near `0`). -/
theorem deriv_envProfileFree_zero (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    deriv (envProfileFree h x y) 0 = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
    ⟨by linarith [Work.OddEnvelope.tStar_pos], Work.OddEnvelope.tStar_pos⟩
  have h1 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hev : envProfileFree h x y =ᶠ[𝓝 (0 : ℝ)] Work.OddEnvelope.semicircle := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem, isOpen_Ioo.mem_nhds h1] with u hu hu1
    rw [envProfileFree_eq_envelopeProfile hu1]
    exact Work.OddCurve.Free.envelopeProfile_eq_semicircle_free H hu
  rw [Filter.EventuallyEq.deriv_eq hev,
    Work.OddEnvelope.Semicircle.deriv_semicircle ⟨by norm_num, by norm_num⟩]
  simp

/-- The derivative of the profile is negative on the right branch (for `t ∈ (0, y c)`). -/
theorem deriv_envProfileFree_neg (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c t : ℝ}
    (hc : 0 < c) (ht : t ∈ Set.Ioo (0 : ℝ) (y c)) : deriv (envProfileFree h x y) t < 0 := by
  rw [deriv_envProfileFree_of_pos H hc ht]
  obtain ⟨σ, hσpos, hσ⟩ := exists_slope_y_lt H hc ht
  have hσ' : Work.OddEnvelope.slopeRight y t = σ :=
    H.toChordCurveFree_y.slopeRight_eq_of hσpos hσ
  rw [hσ', Work.OddEnvelope.kSlope]
  exact div_neg_of_pos_of_neg (H.mono_y σ hσpos) (H.y_deriv_neg σ hσpos)

/-- The derivative of the profile is positive on the left branch (for `t ∈ (-(x c), 0)`). -/
theorem deriv_envProfileFree_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c t : ℝ}
    (hc : 0 < c) (ht : t ∈ Set.Ioo (-(x c)) (0 : ℝ)) : 0 < deriv (envProfileFree h x y) t := by
  rw [deriv_envProfileFree_of_neg H hc ht]
  have hneg : -t ∈ Set.Ioo (0 : ℝ) (x c) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨σ, hσpos, hσ⟩ := exists_slope_x_lt H hc hneg
  have hσ' : Work.OddEnvelope.slopeRight x (-t) = σ :=
    H.toChordCurveFree_x.slopeRight_eq_of hσpos hσ
  rw [hσ', Work.OddEnvelope.kSlope]
  have hnum : 0 < x σ + σ * deriv x σ + deriv (Work.OddEnvelope.negH h) σ := by
    have hmon := H.mono_x σ hσpos
    have h1 : deriv (Work.OddEnvelope.negH h) σ = -deriv h σ := by
      rw [Work.OddEnvelope.deriv_negH]
    rw [h1]; linarith
  exact neg_pos.mpr (div_neg_of_pos_of_neg hnum (H.x_deriv_neg σ hσpos))

/-! ## Monotonicity of the inverse slopes -/

/-- `slopeRight y` is strictly decreasing on `(0, y c)`. -/
theorem slopeRight_strictAntiOn_y (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ}
    (hc : 0 < c) : StrictAntiOn (Work.OddEnvelope.slopeRight y) (Set.Ioo (0 : ℝ) (y c)) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := exists_slope_y_lt H hc ht₁
  obtain ⟨σ₂, hσ₂pos, hσ₂⟩ := exists_slope_y_lt H hc ht₂
  have h1 : Work.OddEnvelope.slopeRight y t₁ = σ₁ := H.toChordCurveFree_y.slopeRight_eq_of hσ₁pos hσ₁
  have h2 : Work.OddEnvelope.slopeRight y t₂ = σ₂ := H.toChordCurveFree_y.slopeRight_eq_of hσ₂pos hσ₂
  rw [h1, h2]
  by_contra hle
  push_neg at hle
  rcases lt_or_eq_of_le hle with hlt' | heq
  · have hanti := H.toChordCurveFree_y.strictAntiOn hσ₁pos hσ₂pos hlt'
    rw [hσ₁, hσ₂] at hanti
    exact absurd hanti (not_lt.mpr hlt.le)
  · have hxy : t₁ = t₂ := by rw [← hσ₁, heq, hσ₂]
    exact absurd hxy hlt.ne

/-- `slopeRight x` is strictly decreasing on `(0, x c)`. -/
theorem slopeRight_strictAntiOn_x (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ}
    (hc : 0 < c) : StrictAntiOn (Work.OddEnvelope.slopeRight x) (Set.Ioo (0 : ℝ) (x c)) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := exists_slope_x_lt H hc ht₁
  obtain ⟨σ₂, hσ₂pos, hσ₂⟩ := exists_slope_x_lt H hc ht₂
  have h1 : Work.OddEnvelope.slopeRight x t₁ = σ₁ := H.toChordCurveFree_x.slopeRight_eq_of hσ₁pos hσ₁
  have h2 : Work.OddEnvelope.slopeRight x t₂ = σ₂ := H.toChordCurveFree_x.slopeRight_eq_of hσ₂pos hσ₂
  rw [h1, h2]
  by_contra hle
  push_neg at hle
  rcases lt_or_eq_of_le hle with hlt' | heq
  · have hanti := H.toChordCurveFree_x.strictAntiOn hσ₁pos hσ₂pos hlt'
    rw [hσ₁, hσ₂] at hanti
    exact absurd hanti (not_lt.mpr hlt.le)
  · have hxy : t₁ = t₂ := by rw [← hσ₁, heq, hσ₂]
    exact absurd hxy hlt.ne

/-! ## Strict antitonicity of the derivative -/

/-- `kSlope h y` is strictly increasing on `(0,∞)` (`H.shape_y`). -/
lemma kSlope_strictMonoOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    StrictMonoOn (Work.OddEnvelope.kSlope h y) (Set.Ioi 0) :=
  Work.OddEnvelope.Shape.kSlope_strictMonoOn_Cinf H.smooth_y H.y_deriv_neg H.smooth_h H.shape_y

/-- `kSlope (negH h) x` is strictly increasing on `(0,∞)` (`H.shape_x`). -/
lemma kSlope_negH_strictMonoOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    StrictMonoOn (Work.OddEnvelope.kSlope (Work.OddEnvelope.negH h) x) (Set.Ioi 0) := by
  refine Work.OddEnvelope.Shape.kSlope_strictMonoOn_Cinf H.smooth_x H.x_deriv_neg
    H.smooth_h.neg ?_
  intro s hs
  have hsh := H.shape_x s hs
  have h1 : deriv (Work.OddEnvelope.negH h) s = -deriv h s := by
    rw [Work.OddEnvelope.deriv_negH]
  have h2 : deriv (deriv (Work.OddEnvelope.negH h)) s = -deriv (deriv h) s := by
    rw [Work.OddEnvelope.deriv_deriv_negH]
  rw [h1, h2]
  linarith

/-- **The derivative of the untruncated profile is strictly decreasing** on a section interval. -/
theorem strictAntiOn_deriv_envProfileFree (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {c : ℝ} (hc : 0 < c) :
    StrictAntiOn (deriv (envProfileFree h x y)) (Set.Ioo (-(x c)) (y c)) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  have ht1a : -(x c) < t₁ := ht₁.1
  have ht1b : t₁ < y c := ht₁.2
  have ht2a : -(x c) < t₂ := ht₂.1
  have ht2b : t₂ < y c := ht₂.2
  rcases lt_trichotomy t₁ 0 with h1neg | h1zero | h1pos
  · rcases lt_trichotomy t₂ 0 with h2neg | h2zero | h2pos
    · -- both strictly negative
      have ht1' : t₁ ∈ Set.Ioo (-(x c)) 0 := ⟨ht1a, h1neg⟩
      have ht2' : t₂ ∈ Set.Ioo (-(x c)) 0 := ⟨ht2a, h2neg⟩
      have hu1 : -t₁ ∈ Set.Ioo (0 : ℝ) (x c) := ⟨by linarith, by linarith⟩
      have hu2 : -t₂ ∈ Set.Ioo (0 : ℝ) (x c) := ⟨by linarith, by linarith⟩
      obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := exists_slope_x_lt H hc hu1
      obtain ⟨σ₂, hσ₂pos, hσ₂⟩ := exists_slope_x_lt H hc hu2
      have h1 : Work.OddEnvelope.slopeRight x (-t₁) = σ₁ :=
        H.toChordCurveFree_x.slopeRight_eq_of hσ₁pos hσ₁
      have h2 : Work.OddEnvelope.slopeRight x (-t₂) = σ₂ :=
        H.toChordCurveFree_x.slopeRight_eq_of hσ₂pos hσ₂
      have hlt' : -t₂ < -t₁ := by linarith
      have hσlt : σ₁ < σ₂ := by
        have hanti := slopeRight_strictAntiOn_x H hc hu2 hu1 hlt'
        rwa [h1, h2] at hanti
      have hK := kSlope_negH_strictMonoOn H hσ₁pos hσ₂pos hσlt
      rw [deriv_envProfileFree_of_neg H hc ht1', deriv_envProfileFree_of_neg H hc ht2', h1, h2]
      linarith
    · -- `t₁ < 0 = t₂`
      rw [h2zero, deriv_envProfileFree_zero H]
      exact deriv_envProfileFree_pos H hc ⟨ht1a, h1neg⟩
    · -- `t₁ < 0 < t₂`
      have h2' : 0 < deriv (envProfileFree h x y) t₁ :=
        deriv_envProfileFree_pos H hc ⟨ht1a, h1neg⟩
      have h3 : deriv (envProfileFree h x y) t₂ < 0 :=
        deriv_envProfileFree_neg H hc ⟨h2pos, ht2b⟩
      linarith
  · -- `t₁ = 0 < t₂`
    rw [h1zero, deriv_envProfileFree_zero H]
    exact deriv_envProfileFree_neg H hc ⟨by linarith [h1zero, hlt], ht2b⟩
  · -- `0 < t₁ < t₂`
    have ht1' : t₁ ∈ Set.Ioo (0 : ℝ) (y c) := ⟨h1pos, ht1b⟩
    have ht2' : t₂ ∈ Set.Ioo (0 : ℝ) (y c) := ⟨lt_trans h1pos hlt, ht2b⟩
    obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := exists_slope_y_lt H hc ht1'
    obtain ⟨σ₂, hσ₂pos, hσ₂⟩ := exists_slope_y_lt H hc ht2'
    have h1 : Work.OddEnvelope.slopeRight y t₁ = σ₁ :=
      H.toChordCurveFree_y.slopeRight_eq_of hσ₁pos hσ₁
    have h2 : Work.OddEnvelope.slopeRight y t₂ = σ₂ :=
      H.toChordCurveFree_y.slopeRight_eq_of hσ₂pos hσ₂
    have hσlt : σ₂ < σ₁ := by
      have hanti := slopeRight_strictAntiOn_y H hc ht1' ht2' hlt
      rwa [h1, h2] at hanti
    have hK := kSlope_strictMonoOn H hσ₂pos hσ₁pos hσlt
    rw [deriv_envProfileFree_of_pos H hc ht1', deriv_envProfileFree_of_pos H hc ht2', h1, h2]
    linarith

/-! ## Concavity of the untruncated profile on a section -/

/-- `-(x c) < y c` for every positive slope. -/
lemma neg_x_lt_y (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ} (hc : 0 < c) :
    -(x c) < y c := by
  have h1 := H.pos_x hc
  have h2 := H.pos_y hc
  linarith

/-- **The untruncated envelope profile is strictly concave on every section `[-(x c), y c]`.** -/
theorem strictConcaveOn_envProfileFree_Icc (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {c : ℝ} (hc : 0 < c) :
    StrictConcaveOn ℝ (Set.Icc (-(x c)) (y c)) (envProfileFree h x y) := by
  have hcont : ContinuousOn (envProfileFree h x y) (Set.Icc (-(x c)) (y c)) :=
    continuousOn_envProfileFree H hc
  have hanti : StrictAntiOn (deriv (envProfileFree h x y))
      (interior (Set.Icc (-(x c)) (y c))) := by
    rw [interior_Icc]
    exact strictAntiOn_deriv_envProfileFree H hc
  exact StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _) hcont hanti

/-- **The untruncated envelope profile is concave on every section `[-(x c), y c]`.** -/
theorem concaveOn_envProfileFree_Icc (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ}
    (hc : 0 < c) : ConcaveOn ℝ (Set.Icc (-(x c)) (y c)) (envProfileFree h x y) :=
  (strictConcaveOn_envProfileFree_Icc H hc).concaveOn

/-- **Positivity of the radicand of the untruncated profile on the cut section.**  The radicand
is the shifted one, `Work.OddCurve.rad h (envProfileFree h x y) s t`; for slopes where the bump
vanishes (`h s = 0`) it is `Work.OddCurve.LowSlope.rad0` (`Work.OddCurve.LowSlope.rad0_eq_rad`). -/
theorem envProfileFree_sub_sq_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ}
    (hs : 0 < s) : ∀ t ∈ Set.Ioo (-(x s)) (y s),
      0 < Work.OddCurve.rad h (envProfileFree h x y) s t := by
  have hxs : 0 < x s := H.pos_x hs
  have hys : 0 < y s := H.pos_y hs
  have hab : -(x s) < y s := by linarith
  have hsmx : ContDiffOn ℝ ∞ x (Set.Ioi 0) := H.smooth_x
  have hsmy : ContDiffOn ℝ ∞ y (Set.Ioi 0) := H.smooth_y
  have hdcx : ∀ u : ℝ, 0 < u → deriv x u < 0 := fun u hu => H.x_deriv_neg u hu
  have hdcy : ∀ u : ℝ, 0 < u → deriv y u < 0 := fun u hu => H.y_deriv_neg u hu
  have hpx : ∀ u : ℝ, 0 < u → 0 < x u := fun u hu => H.pos_x hu
  have hpy : ∀ u : ℝ, 0 < u → 0 < y u := fun u hu => H.pos_y hu
  obtain ⟨hchordy, hchordx⟩ := envProfileFree_chord h x y hsmx hsmy hdcx hdcy hpx hpy
  have hy : envProfileFree h x y (y s) = s * y s + h s := hchordy s hs
  have hx : envProfileFree h x y (-(x s)) = -(s * (-(x s)) + h s) := hchordx s hs
  have hposy : 0 < s * y s + h s := envCurveRight_pos H hs
  have hnegx : s * (-(x s)) + h s < 0 := by
    have hcl := envCurveLeft_pos H hs
    linarith
  intro t ht
  have hkey := Work.OddEnvelope.NonDegenerate.sq_gt_sq_of_concaveOn_of_ends hab
    (concaveOn_envProfileFree_Icc H hs) hx hy hnegx hposy t ht
  rw [Work.OddCurve.rad]
  linarith

end

end Work.OddVolterra.Free
