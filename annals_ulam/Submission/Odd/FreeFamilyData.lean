import Mathlib
import Submission.Work.OddCurve.Free.Final
import Submission.Work.OddCurve.Free.Endgame
import Submission.Work.OddVolterra.Free.envProfileFreeConcave
import Submission.Work.OddVolterra.Free.envProfileFreeTips
import Submission.Work.OddVolterra.Free.envProfileFree_chord
import Submission.Work.OddVolterra.Free.rad_nonpos_outside_free
import Submission.Work.OddVolterra.Free.semicircleCurveFree
import Submission.Work.OddVolterra.Free.envelopeRight_contDiffOn_Ioo
import Submission.Odd.BallMoment
import Submission.Odd.BumpData

/-!
# The odd-dimensional family data from the free-tip chord curve

`Work.OddCurve.Free.odd_curve_exists_free_written_unconditional` produces, for every sufficiently
small flat bump `h`, a chord curve `(x, y)` with `Work.OddCurve.Free.IsEnvelopeCurveFree h x y`
(free tips: the limits of `x` and `y` at `0⁺` are the two tips `bX`, `bY` of the body) together with
the two moment equations on `(0,1]` for the *untruncated* envelope profile
`Work.OddVolterra.Free.envProfileFree h x y`.

This file turns that into `Submission.Odd.OddFamilyData d`:

* the profile is truncated to its actual support `[-bX, bY]` — `envProfileFree` is defined through
  `Work.OddEnvelope.slopeRight`, which is `Function.invFunOn` and hence an opaque constant outside
  the range, so truncation is what makes the support statement true; the two functions agree on
  every section;
* the moment equations are extended from `(0,1]` to all slopes `s > 0`: for `s ≥ 1` the curve is
  the semicircle's and the profile is the semicircle on the section, so both equations are the unit
  ball's (`Work.OddCurve.ball_moment_identity`);
* the profile data on `[-bX, bY]` (positivity, smoothness, strict concavity, continuity, the two
  tip values) are assembled from the `Work.OddVolterra.Free` chapter;
* `Work.OddCurve.Free.oddFamilyData_of_momentEquationsGeneralFull` (the general-interval endgame)
  finishes.

The main result is `Submission.Odd.odd_floating_family_data_free`.
-/

namespace Submission.Odd

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

set_option autoImplicit false

variable {d : ℕ}
variable {h x y : ℝ → ℝ}
variable {bX bY : ℝ}

local notation "τ" => Work.OddEnvelope.tau

/-- The free profile truncated to its actual support. -/
noncomputable def truncFree (bX bY : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => if t ∈ Set.Ioo (-bX) bY then f t else 0

lemma truncFree_support (bX bY : ℝ) (f : ℝ → ℝ) :
    Function.support (truncFree bX bY f) ⊆ Set.Icc (-bX) bY := by
  intro t ht
  by_contra hc
  have h1 : t ∉ Set.Ioo (-bX) bY := fun h => hc ⟨le_of_lt h.1, le_of_lt h.2⟩
  exact ht (by simp only [truncFree, if_neg h1, Pi.zero_apply])

lemma truncFree_eq_of_mem (bX bY : ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (-bX) bY) :
    truncFree bX bY f t = f t := by
  simp only [truncFree, if_pos ht]

/-- The two tips of a free-tip chord curve. -/
noncomputable def tipX (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) : ℝ :=
  Classical.choose H.x_tendsto_free
noncomputable def tipY (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) : ℝ :=
  Classical.choose H.y_tendsto_free

lemma tipX_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) : 0 < tipX H :=
  (Classical.choose_spec H.x_tendsto_free).1
lemma tipY_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) : 0 < tipY H :=
  (Classical.choose_spec H.y_tendsto_free).1
lemma tendsto_tipX (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 (tipX H)) :=
  (Classical.choose_spec H.x_tendsto_free).2
lemma tendsto_tipY (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 (tipY H)) :=
  (Classical.choose_spec H.y_tendsto_free).2

lemma tStar_lt_tipX (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    Work.OddEnvelope.tStar < tipX H := by
  have htau : 0 < 1 - τ := by norm_num [Work.OddEnvelope.tau]
  have h := Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_x
    (tendsto_tipX H) (1 - τ) htau
  have hx1 : x (1 - τ) = Work.OddEnvelope.profileX (1 - τ) := H.x_tail _ le_rfl
  rw [hx1] at h
  simpa [Work.OddEnvelope.tStar, Work.OddEnvelope.tau] using h

lemma tStar_lt_tipY (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) :
    Work.OddEnvelope.tStar < tipY H := by
  have htau : 0 < 1 - τ := by norm_num [Work.OddEnvelope.tau]
  have h := Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_y
    (tendsto_tipY H) (1 - τ) htau
  have hy1 : y (1 - τ) = Work.OddEnvelope.profileX (1 - τ) := H.y_tail _ le_rfl
  rw [hy1] at h
  simpa [Work.OddEnvelope.tStar, Work.OddEnvelope.tau] using h

/-- In the transition window's `t`-range the free profile is the unit semicircle. -/
theorem envProfileFree_eq_semicircle_of_abs_lt (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {t : ℝ} (ht : |t| < Work.OddEnvelope.tStar) : Work.OddVolterra.Free.envProfileFree h x y t =
      Work.OddEnvelope.semicircle t := by
  have htau : 0 < 1 - τ := by norm_num [Work.OddEnvelope.tau]
  have htStar1 : Work.OddEnvelope.tStar < 1 := Work.OddEnvelope.tStar_lt_one
  have htabs1 : |t| < 1 := lt_trans ht htStar1
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · obtain ⟨σ, hσpos, hσ⟩ := H.toChordCurveFree_x.exists_slope_of_mem_Ioo (tendsto_tipX H)
      (show -t ∈ Set.Ioo (0 : ℝ) (tipX H) from
        ⟨by linarith [abs_lt.mp ht], by linarith [tStar_lt_tipX H, abs_lt.mp ht]⟩)
    have hσgt : 1 - τ < σ := by
      by_contra hle
      have hle' : σ ≤ 1 - τ := le_of_not_gt hle
      have hmono : x (1 - τ) ≤ x σ := by
        rcases eq_or_lt_of_le hle' with hh | hh
        · rw [hh]
        · exact le_of_lt (H.strictAntiOn_x hσpos htau hh)
      have hx1 : x (1 - τ) = Work.OddEnvelope.profileX (1 - τ) := H.x_tail _ le_rfl
      have hle2 : Work.OddEnvelope.tStar ≤ -t := by
        rw [Work.OddEnvelope.tStar, ← hx1]
        exact le_trans hmono (le_of_eq hσ)
      linarith [abs_lt.mp ht]
    have hh0 : h σ = 0 := H.h_eq_zero_of_gt hσgt
    have hxs : x σ = Work.OddEnvelope.profileX σ := H.x_tail σ (le_of_lt hσgt)
    have hslope' : Work.OddEnvelope.slopeRight x (-t) = σ := by
      rw [Work.OddEnvelope.slopeRight, ← hσ]
      exact H.strictAntiOn_x.injOn.leftInvOn_invFunOn hσpos
    have hslope : Work.OddEnvelope.slopeLeft x t = σ := by
      rw [show Work.OddEnvelope.slopeLeft x t = Work.OddEnvelope.slopeRight x (-t) from rfl]
      exact hslope'
    have ht' : t = - Work.OddEnvelope.profileX σ := by
      rw [show t = -(x σ) from by rw [hσ]; ring, hxs]
    rw [Work.OddVolterra.Free.envProfileFree_of_neg hneg, Work.OddEnvelope.envelopeLeft,
      hslope, hh0, add_zero]
    have hkey : σ * t = - Work.OddEnvelope.semicircle t := by
      calc σ * t = σ * (-(Work.OddEnvelope.profileX σ)) := by rw [ht']
        _ = -(σ * Work.OddEnvelope.profileX σ) := by ring
        _ = -(Work.OddEnvelope.semicircle (Work.OddEnvelope.profileX σ)) := by
              rw [Work.OddEnvelope.mul_profileX_eq_semicircle hσpos]
        _ = -(Work.OddEnvelope.semicircle t) := by
              rw [ht', Work.OddEnvelope.semicircle_even]
    rw [hkey, neg_neg]
  · subst hzero
    rw [Work.OddVolterra.Free.envProfileFree_zero, Work.OddEnvelope.semicircle]
    norm_num
  · obtain ⟨σ, hσpos, hσ⟩ := H.toChordCurveFree_y.exists_slope_of_mem_Ioo (tendsto_tipY H)
      (show t ∈ Set.Ioo (0 : ℝ) (tipY H) from
        ⟨hpos, by linarith [tStar_lt_tipY H, abs_lt.mp ht]⟩)
    have hσgt : 1 - τ < σ := by
      by_contra hle
      have hle' : σ ≤ 1 - τ := le_of_not_gt hle
      have hmono : y (1 - τ) ≤ y σ := by
        rcases eq_or_lt_of_le hle' with hh | hh
        · rw [hh]
        · exact le_of_lt (H.strictAntiOn_y hσpos htau hh)
      have hy1 : y (1 - τ) = Work.OddEnvelope.profileX (1 - τ) := H.y_tail _ le_rfl
      have hle2 : Work.OddEnvelope.tStar ≤ t := by
        rw [Work.OddEnvelope.tStar, ← hy1]
        exact le_trans hmono (le_of_eq hσ)
      linarith [abs_lt.mp ht]
    have hh0 : h σ = 0 := H.h_eq_zero_of_gt hσgt
    have hys : y σ = Work.OddEnvelope.profileX σ := H.y_tail σ (le_of_lt hσgt)
    have hslope : Work.OddEnvelope.slopeRight y t = σ := by
      rw [Work.OddEnvelope.slopeRight, ← hσ]
      exact H.strictAntiOn_y.injOn.leftInvOn_invFunOn hσpos
    have ht' : t = Work.OddEnvelope.profileX σ := by
      rw [show t = y σ from hσ.symm, hys]
    rw [Work.OddVolterra.Free.envProfileFree_of_pos hpos, Work.OddEnvelope.envelopeRight,
      hslope, hh0, add_zero, ht', Work.OddEnvelope.mul_profileX_eq_semicircle hσpos]

lemma envProfileFree_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    {t : ℝ} (ht : t ∈ Set.Ioo (-bX) bY) : 0 < Work.OddVolterra.Free.envProfileFree h x y t := by
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · obtain ⟨σ, hσpos, hσ⟩ := H.toChordCurveFree_x.exists_slope_of_mem_Ioo hXl
      (show -t ∈ Set.Ioo (0 : ℝ) bX from ⟨by linarith, by linarith [ht.1]⟩)
    have hchord := (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y
      H.x_deriv_neg H.y_deriv_neg (fun s hs => H.pos_x hs) (fun s hs => H.pos_y hs)).2 σ hσpos
    have ht_eq : -(x σ) = t := by rw [hσ]; ring
    rw [ht_eq] at hchord
    have hpos' := Work.OddVolterra.Free.envCurveLeft_pos H hσpos
    rw [hchord]
    nlinarith [hpos', hσ]
  · subst hzero
    rw [Work.OddVolterra.Free.envProfileFree_zero]
    norm_num
  · obtain ⟨σ, hσpos, hσ⟩ := H.toChordCurveFree_y.exists_slope_of_mem_Ioo hYl
      (show t ∈ Set.Ioo (0 : ℝ) bY from ⟨hpos, ht.2⟩)
    have hchord := (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y
      H.x_deriv_neg H.y_deriv_neg (fun s hs => H.pos_x hs) (fun s hs => H.pos_y hs)).1 σ hσpos
    rw [hσ] at hchord
    have hpos' := Work.OddVolterra.Free.envCurveRight_pos H hσpos
    rw [hchord]
    rw [hσ] at hpos'
    exact hpos'

lemma envProfileFree_contDiffOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY)) :
    ContDiffOn ℝ ∞ (Work.OddVolterra.Free.envProfileFree h x y) (Set.Ioo (-bX) bY) := by
  intro t ht
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds ht)]
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) bX, ∃ σ : ℝ, 0 < σ ∧ x σ = z :=
      fun z hz => H.toChordCurveFree_x.exists_slope_of_mem_Ioo hXl hz
    have hCinf : ContDiffOn ℝ ∞ (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x)
        (Set.Ioo (0 : ℝ) bX) :=
      Work.OddVolterra.Free.envelopeRight_contDiffOn_Ioo H.smooth_x H.x_deriv_neg
        H.smooth_h.neg hsurj
    have hneg' : ContDiffOn ℝ ∞ (fun u : ℝ => -u) (Set.Ioo (-bX) 0) := by fun_prop
    have hcomp : ContDiffOn ℝ ∞
        (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))
        (Set.Ioo (-bX) 0) :=
      hCinf.comp hneg' (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    have heq : (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))
        = Work.OddEnvelope.envelopeLeft h x := by
      funext u
      exact (Work.OddEnvelope.envelopeLeft_eq_negH h x u).symm
    rw [heq] at hcomp
    have hAt : ContDiffAt ℝ ∞ (Work.OddEnvelope.envelopeLeft h x) t :=
      hcomp.contDiffAt (isOpen_Ioo.mem_nhds ⟨ht.1, hneg⟩)
    have hev : Work.OddVolterra.Free.envProfileFree h x y =ᶠ[𝓝 t]
        Work.OddEnvelope.envelopeLeft h x :=
      Filter.eventually_of_mem (isOpen_Iio.mem_nhds hneg)
        (fun u hu => Work.OddVolterra.Free.envProfileFree_of_neg hu)
    exact hAt.congr_of_eventuallyEq hev
  · subst hzero
    have hev : Work.OddVolterra.Free.envProfileFree h x y =ᶠ[𝓝 (0 : ℝ)]
        Work.OddEnvelope.semicircle := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) Work.OddEnvelope.tStar_pos] with u hu
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hu
      exact envProfileFree_eq_semicircle_of_abs_lt H hu
    have hAtω : ContDiffAt ℝ ω Work.OddEnvelope.semicircle 0 :=
      (Work.OddEnvelope.Semicircle.contDiffOn_semicircle.contDiffAt
        (isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Set.Ioo (-1) 1)))
    have hAt : ContDiffAt ℝ ∞ Work.OddEnvelope.semicircle 0 := hAtω.of_le le_top
    exact hAt.congr_of_eventuallyEq hev
  · have hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) bY, ∃ σ : ℝ, 0 < σ ∧ y σ = z :=
      fun z hz => H.toChordCurveFree_y.exists_slope_of_mem_Ioo hYl hz
    have hCinf : ContDiffOn ℝ ∞ (Work.OddEnvelope.envelopeRight h y) (Set.Ioo (0 : ℝ) bY) :=
      Work.OddVolterra.Free.envelopeRight_contDiffOn_Ioo H.smooth_y H.y_deriv_neg H.smooth_h hsurj
    have hAt : ContDiffAt ℝ ∞ (Work.OddEnvelope.envelopeRight h y) t :=
      hCinf.contDiffAt (isOpen_Ioo.mem_nhds ⟨hpos, ht.2⟩)
    have hev : Work.OddVolterra.Free.envProfileFree h x y =ᶠ[𝓝 t]
        Work.OddEnvelope.envelopeRight h y :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hpos)
        (fun u hu => Work.OddVolterra.Free.envProfileFree_of_pos hu)
    exact hAt.congr_of_eventuallyEq hev

lemma truncFree_contDiffOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY)) :
    ContDiffOn ℝ ∞ (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
      (Set.Ioo (-bX) bY) :=
  (envProfileFree_contDiffOn H hXl hYl).congr
    (fun t ht => truncFree_eq_of_mem bX bY (Work.OddVolterra.Free.envProfileFree h x y) ht)

lemma exists_section_of_mem (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    {t : ℝ} (ht : t ∈ Set.Ioo (-bX) bY) : ∃ c > 0, t ∈ Set.Ioo (-(x c)) (y c) := by
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), -t < x c :=
    hXl.eventually (isOpen_Ioi.mem_nhds (show -t < bX by linarith [ht.1]))
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), t < y c :=
    hYl.eventually (isOpen_Ioi.mem_nhds ht.2)
  obtain ⟨c, hc, hcpos⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact ⟨c, hcpos, by linarith [hc.1], hc.2⟩

lemma truncFree_deriv_eq (f : ℝ → ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (-bX) bY) :
    deriv (truncFree bX bY f) t = deriv f t := by
  have hev : truncFree bX bY f =ᶠ[𝓝 t] f :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun u hu => truncFree_eq_of_mem bX bY f hu)
  have hd := Filter.EventuallyEq.deriv_eq hev
  simpa using hd

lemma truncFree_strictAntiOn_deriv (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY)) :
    StrictAntiOn (deriv (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y)))
      (Set.Ioo (-bX) bY) := by
  intro t₁ ht₁ t₂ ht₂ hlt
  rw [truncFree_deriv_eq _ ht₁, truncFree_deriv_eq _ ht₂]
  obtain ⟨c₁, hc₁pos, hc₁⟩ := exists_section_of_mem H hXl hYl ht₁
  obtain ⟨c₂, hc₂pos, hc₂⟩ := exists_section_of_mem H hXl hYl ht₂
  set c : ℝ := min c₁ c₂ with hcdef
  have hcpos : 0 < c := lt_min hc₁pos hc₂pos
  have hxmono : x c₁ ≤ x c := by
    rcases eq_or_lt_of_le (min_le_left c₁ c₂) with hh | hh
    · rw [← hh]
    · exact le_of_lt (H.strictAntiOn_x hcpos hc₁pos hh)
  have hymono : y c₁ ≤ y c := by
    rcases eq_or_lt_of_le (min_le_left c₁ c₂) with hh | hh
    · rw [← hh]
    · exact le_of_lt (H.strictAntiOn_y hcpos hc₁pos hh)
  have hxmono2 : x c₂ ≤ x c := by
    rcases eq_or_lt_of_le (min_le_right c₁ c₂) with hh | hh
    · rw [← hh]
    · exact le_of_lt (H.strictAntiOn_x hcpos hc₂pos hh)
  have hymono2 : y c₂ ≤ y c := by
    rcases eq_or_lt_of_le (min_le_right c₁ c₂) with hh | hh
    · rw [← hh]
    · exact le_of_lt (H.strictAntiOn_y hcpos hc₂pos hh)
  refine Work.OddVolterra.Free.strictAntiOn_deriv_envProfileFree H hcpos
    ⟨by linarith [hc₁.1, hxmono], by linarith [hc₁.2, hymono]⟩
    ⟨by linarith [hc₂.1, hxmono2], by linarith [hc₂.2, hymono2]⟩ hlt

/-- A function which is continuous on an open interval and whose limit at the left endpoint
exists is continuous within the closed interval at that endpoint. -/
lemma continuousWithinAt_Icc_of_tendsto_Ioo {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hlim : Tendsto g (𝓝[Set.Ioo a b] a) (𝓝 c)) (ha : g a = c) :
    ContinuousWithinAt g (Set.Icc a b) a := by
  show Tendsto g (𝓝[Set.Icc a b] a) (𝓝 (g a))
  rw [ha, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε hε
  refine ⟨min δ (b - a), lt_min hδpos (by linarith), fun x hx hxd => ?_⟩
  have hxd' : dist x a < δ := lt_of_lt_of_le hxd (min_le_left _ _)
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]
    simpa [ha] using hε
  · refine hδ (x := x) ⟨h, ?_⟩ hxd'
    have h2 : dist x a < b - a := lt_of_lt_of_le hxd (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at h2
    linarith [h2.2]

/-- The same at the right endpoint: it suffices that the limit holds along `Ioo 0 b`. -/
lemma continuousWithinAt_Icc_of_tendsto_Ioo_right {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hbpos : 0 < b) (hlim : Tendsto g (𝓝[Set.Ioo (0 : ℝ) b] b) (𝓝 c)) (hb : g b = c) :
    ContinuousWithinAt g (Set.Icc a b) b := by
  show Tendsto g (𝓝[Set.Icc a b] b) (𝓝 (g b))
  rw [hb, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε hε
  refine ⟨min δ (min b (b - a)), lt_min hδpos (lt_min hbpos (by linarith)),
    fun x hx hxd => ?_⟩
  have hxd' : dist x b < δ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hb2 : dist x b < min b (b - a) := lt_of_lt_of_le hxd (min_le_right _ _)
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h]
    simpa [hb] using hε
  · have hxpos : 0 < x := by
      have h3 : dist x b < b := lt_of_lt_of_le hb2 (min_le_left _ _)
      rw [Real.dist_eq, abs_of_neg (by linarith)] at h3
      linarith
    exact hδ (x := x) ⟨hxpos, h⟩ hxd'

lemma tendsto_envProfileFree_left_tip (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hbX : 0 < bX) (hbY : 0 < bY) :
    Tendsto (Work.OddVolterra.Free.envProfileFree h x y)
      (𝓝[Set.Ioo (-bX) bY] (-bX)) (𝓝 0) := by
  have h := Work.OddVolterra.Free.tendsto_envProfileFreeLeft_at_tip H hXl hbX
  have hneg : Tendsto (fun u : ℝ => -u) (𝓝[Set.Ioo (-bX) bY] (-bX))
      (𝓝[Set.Ioo (0 : ℝ) bX] bX) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun u : ℝ => -u) (𝓝 (-bX)) (𝓝 (-(-bX))) :=
        (continuous_neg.tendsto (-bX))
      simpa using h1.mono_left nhdsWithin_le_nhds
    · have hmem0 : Set.Iio (0 : ℝ) ∈ 𝓝[Set.Ioo (-bX) bY] (-bX) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show -bX < 0 by linarith))
      filter_upwards [self_mem_nhdsWithin, hmem0] with u hu hu0
      rw [Set.mem_Iio] at hu0
      exact ⟨by linarith, by linarith [hu.1]⟩
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun u => by simp)) (h.comp hneg)

lemma truncFree_continuousOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    (hbX : 0 < bX) (hbY : 0 < bY) :
    ContinuousOn (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
      (Set.Icc (-bX) bY) := by
  intro t ht
  have hab : -bX < bY := by linarith
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · rw [← h1]
    have hlim := tendsto_envProfileFree_left_tip (bY := bY) H hXl hbX hbY
    have hg : Tendsto (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
        (𝓝[Set.Ioo (-bX) bY] (-bX)) (𝓝 0) :=
      hlim.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
        (fun u hu => (truncFree_eq_of_mem bX bY _ hu).symm))
    have hval : truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) (-bX) = 0 := by
      simp only [truncFree, if_neg (by simp : ¬ (-bX) ∈ Set.Ioo (-bX) bY)]
    exact continuousWithinAt_Icc_of_tendsto_Ioo hab hg hval
  · rcases eq_or_lt_of_le ht.2 with h2 | h2
    · rw [h2]
      have hlim := Work.OddVolterra.Free.tendsto_envProfileFree_at_tip H hYl hbY
      have hg : Tendsto (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
          (𝓝[Set.Ioo (0:ℝ) bY] bY) (𝓝 0) :=
        hlim.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
          (fun u hu => (truncFree_eq_of_mem bX bY _
            ⟨by linarith [hu.1, hbX], hu.2⟩).symm))
      have hval : truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) bY = 0 := by
        simp only [truncFree, if_neg (by simp : ¬ bY ∈ Set.Ioo (-bX) bY)]
      exact continuousWithinAt_Icc_of_tendsto_Ioo_right hab hbY hg hval
    · have hmem : t ∈ Set.Ioo (-bX) bY := ⟨h1, h2⟩
      have hcont : ContinuousOn (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
          (Set.Ioo (-bX) bY) := (truncFree_contDiffOn H hXl hYl).continuousOn
      have hIcc : Set.Icc (-bX) bY ∈ 𝓝 t :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hmem)
          (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
      have hthis : Tendsto (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
          (𝓝[Set.Ioo (-bX) bY] t)
          (𝓝 (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t)) :=
        hcont.continuousWithinAt hmem
      rw [nhdsWithin_eq_nhds.2 (isOpen_Ioo.mem_nhds hmem)] at hthis
      show Tendsto (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y))
        (𝓝[Set.Icc (-bX) bY] t)
        (𝓝 (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t))
      rw [nhdsWithin_eq_nhds.2 hIcc]
      exact hthis

lemma truncFree_strictConcaveOn (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    (hbX : 0 < bX) (hbY : 0 < bY) :
    StrictConcaveOn ℝ (Set.Icc (-bX) bY)
      (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y)) :=
  StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
    (truncFree_continuousOn H hXl hYl hbX hbY)
    ((truncFree_strictAntiOn_deriv H hXl hYl).mono (by rw [interior_Icc]))

lemma truncFree_pos (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    {t : ℝ} (ht : t ∈ Set.Ioo (-bX) bY) :
    0 < truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t := by
  rw [truncFree_eq_of_mem bX bY _ ht]
  exact envProfileFree_pos H hXl hYl ht

lemma truncFree_inside (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY)) (hbX : 0 < bX)
    {s : ℝ} (hs : 0 < s) : truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) (y s) =
      s * y s + h s := by
  have hmem : y s ∈ Set.Ioo (-bX) bY :=
    ⟨by linarith [H.pos_y hs, hbX],
     Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_y hYl s hs⟩
  rw [truncFree_eq_of_mem bX bY _ hmem]
  exact (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y H.x_deriv_neg
    H.y_deriv_neg (fun s hs => H.pos_x hs) (fun s hs => H.pos_y hs)).1 s hs

end Submission.Odd

namespace Submission.Odd
open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval
set_option autoImplicit false

variable {h x y : ℝ → ℝ} {bX bY : ℝ}

/-- The numerical comparison `profileX 1 < tStar`. -/
lemma profileX_one_lt_tStar : Work.OddEnvelope.profileX 1 < Work.OddEnvelope.tStar := by
  rw [Work.OddEnvelope.tStar]
  refine Work.OddEnvelope.profileX_strictAntiOn ?_ ?_ ?_
  · norm_num [Work.OddEnvelope.tau]
  · norm_num
  · norm_num [Work.OddEnvelope.tau]

/-- On the section of a slope `s ≥ 1` the truncated free profile is the unit semicircle. -/
lemma truncFree_eq_semicircle_of_one_le (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXt : Work.OddEnvelope.tStar < bX) (hYt : Work.OddEnvelope.tStar < bY) {s : ℝ} (hs : 1 ≤ s) :
    ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX s)) (Work.OddEnvelope.profileX s),
      truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t =
        Work.OddEnvelope.semicircle t := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  intro t ht
  have htabs : |t| ≤ Work.OddEnvelope.profileX s := by
    rw [abs_le]; exact ⟨ht.1, ht.2⟩
  have hle : Work.OddEnvelope.profileX s ≤ Work.OddEnvelope.profileX 1 := by
    rcases eq_or_lt_of_le hs with hh | hh
    · rw [hh]
    · exact le_of_lt (Work.OddEnvelope.profileX_strictAntiOn (by norm_num) hs0 hh)
  have hlt : |t| < Work.OddEnvelope.tStar :=
    lt_of_le_of_lt htabs (lt_of_le_of_lt hle profileX_one_lt_tStar)
  have hmem : t ∈ Set.Ioo (-bX) bY :=
    ⟨by linarith [abs_lt.mp hlt, hXt], by linarith [abs_lt.mp hlt, hYt]⟩
  rw [truncFree_eq_of_mem bX bY _ hmem]
  exact envProfileFree_eq_semicircle_of_abs_lt H hlt

/-- The first moment equation beyond the transition window: it is the ball's. -/
lemma truncFree_momentA_big (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXt : Work.OddEnvelope.tStar < bX) (hYt : Work.OddEnvelope.tStar < bY)
    (n : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    (∫ t in (-x s)..(y s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
          (s * t + h s) ^ 2) ^ n *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t + h s) ^ 2)) =
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt (1 + s ^ 2) := by
  have hτ : 1 - Work.OddCurve.tau ≤ s := by
    rw [show Work.OddCurve.tau = (1 / 10 : ℝ) from rfl]; linarith
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsx : x s = Work.OddEnvelope.profileX s := H.x_tail s hτ
  have hsy : y s = Work.OddEnvelope.profileX s := H.y_tail s hτ
  have hh0 : h s = 0 := H.h_eq_zero_of_gt (by
    rw [show Work.OddCurve.tau = (1 / 10 : ℝ) from rfl]; linarith)
  have hprof := truncFree_eq_semicircle_of_one_le H hXt hYt hs
  rw [hsx, hsy]
  simp only [hh0, add_zero]
  have hcongr : (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 - (s * t) ^ 2) ^ n *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t) ^ 2)) =
      ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith [Work.OddEnvelope.profileX_pos s])] at ht
    have hsem := hprof t ht
    have h1 : Work.OddEnvelope.profileX s < 1 := Work.OddEnvelope.profileX_lt_one hs0
    have htabs : |t| ≤ Work.OddEnvelope.profileX s := by
      rw [abs_le]; exact ⟨ht.1, ht.2⟩
    have ht1 : t ^ 2 ≤ 1 := by nlinarith [abs_le.mp (le_of_lt (lt_of_le_of_lt htabs h1))]
    have hsemi : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
      rw [Work.OddEnvelope.semicircle]
      exact Real.sq_sqrt (by linarith)
    rw [hsem, hsemi]
  rw [hcongr]
  exact (Work.OddCurve.ball_moment_identity n s).1

/-- The second moment equation beyond the transition window: the ball's vanishing one. -/
lemma truncFree_momentB_big (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXt : Work.OddEnvelope.tStar < bX) (hYt : Work.OddEnvelope.tStar < bY)
    (n : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    (∫ t in (-x s)..(y s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
          (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t + h s) ^ 2) * (t + deriv h s)) = 0 := by
  have hτ : 1 - Work.OddCurve.tau ≤ s := by
    rw [show Work.OddCurve.tau = (1 / 10 : ℝ) from rfl]; linarith
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsx : x s = Work.OddEnvelope.profileX s := H.x_tail s hτ
  have hsy : y s = Work.OddEnvelope.profileX s := H.y_tail s hτ
  have hh0 : h s = 0 := H.h_eq_zero_of_gt (by
    rw [show Work.OddCurve.tau = (1 / 10 : ℝ) from rfl]; linarith)
  have hd0 : deriv h s = 0 := by
    have hmem : Set.Ioi (1 - Work.OddCurve.tau) ∈ 𝓝 s :=
      isOpen_Ioi.mem_nhds (by
        show (1:ℝ) - Work.OddCurve.tau < s
        rw [show Work.OddCurve.tau = (1 / 10 : ℝ) from rfl]; linarith)
    have hev : h =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) :=
      Filter.eventually_of_mem hmem (fun u hu => H.h_eq_zero_of_gt hu)
    have hd := Filter.EventuallyEq.deriv_eq hev
    simpa using hd
  have hprof := truncFree_eq_semicircle_of_one_le H hXt hYt hs
  rw [hsx, hsy]
  simp only [hh0, add_zero, hd0, add_zero]
  have hcongr : (∫ t in (-(Work.OddEnvelope.profileX s))..(Work.OddEnvelope.profileX s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 - (s * t) ^ 2) ^ (n - 1) *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t) ^ 2) * t) =
      ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith [Work.OddEnvelope.profileX_pos s])] at ht
    have hsem := hprof t ht
    have h1 : Work.OddEnvelope.profileX s < 1 := Work.OddEnvelope.profileX_lt_one hs0
    have htabs : |t| ≤ Work.OddEnvelope.profileX s := by
      rw [abs_le]; exact ⟨ht.1, ht.2⟩
    have ht1 : t ^ 2 ≤ 1 := by nlinarith [abs_le.mp (le_of_lt (lt_of_le_of_lt htabs h1))]
    have hsemi : Work.OddEnvelope.semicircle t ^ 2 = 1 - t ^ 2 := by
      rw [Work.OddEnvelope.semicircle]
      exact Real.sq_sqrt (by linarith)
    rw [hsem, hsemi]
  rw [hcongr]
  exact (Work.OddCurve.ball_moment_identity n s).2

end Submission.Odd

namespace Submission.Odd
open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval
set_option autoImplicit false

variable {h x y : ℝ → ℝ} {bX bY : ℝ}

/-- The left chord identity for the truncated free profile. -/
lemma truncFree_inside_left (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hbY : 0 < bY)
    {s : ℝ} (hs : 0 < s) : truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) (-(x s)) =
      -(s * (-(x s)) + h s) := by
  have hxs : x s < bX :=
    Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_x hXl s hs
  have hmem : -(x s) ∈ Set.Ioo (-bX) bY := ⟨by linarith, by linarith [H.pos_x hs, hbY]⟩
  rw [truncFree_eq_of_mem bX bY _ hmem]
  exact (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y H.x_deriv_neg
    H.y_deriv_neg (fun s hs => H.pos_x hs) (fun s hs => H.pos_y hs)).2 s hs

/-- On a section the truncated free profile is the free profile. -/
lemma truncFree_eqOn_section (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    (hbX : 0 < bX) (hbY : 0 < bY) {s : ℝ} (hs : 0 < s) :
    ∀ t ∈ Set.uIcc (-(x s)) (y s),
      truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t =
        Work.OddVolterra.Free.envProfileFree h x y t := by
  have hxs : x s < bX :=
    Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_x hXl s hs
  have hys : y s < bY :=
    Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_y hYl s hs
  have hcs : -(x s) ≤ y s := by linarith [H.pos_x hs, H.pos_y hs]
  intro t ht
  rw [Set.uIcc_of_le hcs] at ht
  exact truncFree_eq_of_mem bX bY _ ⟨by linarith [ht.1, hxs], by linarith [ht.2, hys]⟩

/-- The section of a positive slope lies inside the support interval. -/
lemma section_mem (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hXl : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hYl : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY))
    (hbX : 0 < bX) (hbY : 0 < bY) {s : ℝ} (hs : 0 < s) :
    -(x s) ∈ Set.Ioo (-bX) bY ∧ y s ∈ Set.Ioo (-bX) bY :=
  ⟨⟨by linarith [Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_x hXl s hs],
    by linarith [H.pos_x hs, hbY]⟩,
   ⟨by linarith [H.pos_y hs, hbX],
    Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi H.strictAntiOn_y hYl s hs⟩⟩

/-- **The odd-dimensional family data from the free-tip chord curve.** -/
theorem odd_floating_family_data_free {d : ℕ} (hd : 3 ≤ d) [NeZero d] (hdodd : Odd d) :
    OddFamilyData d := by
  have hdodd0 : Odd d := hdodd
  obtain ⟨n, hdn⟩ := hdodd0
  have hn : 1 ≤ n := by omega
  obtain ⟨ε, hε, Hcur⟩ :=
    Work.OddCurve.Free.odd_curve_exists_free_written_unconditional n hn
  obtain ⟨h, hh_cont, hsupp_ioo, hsupp_icc, hne, h0, hflat, hbnd, hpos⟩ :=
    exists_odd_bump (2 * n + 2) ε hε
  obtain ⟨C, x, y, hICF, hA, hB⟩ := Hcur h hne hh_cont hsupp_ioo hbnd hflat
  obtain ⟨bX, hbXpos, hXl⟩ := hICF.x_tendsto_free
  obtain ⟨bY, hbYpos, hYl⟩ := hICF.y_tendsto_free
  have hXt : Work.OddEnvelope.tStar < bX := by
    have h := Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi hICF.strictAntiOn_x hXl
      (1 - Work.OddEnvelope.tau) (by norm_num [Work.OddEnvelope.tau])
    have hx1 : x (1 - Work.OddEnvelope.tau) =
        Work.OddEnvelope.profileX (1 - Work.OddEnvelope.tau) := hICF.x_tail _ le_rfl
    rw [hx1] at h
    simpa [Work.OddEnvelope.tStar] using h
  have hYt : Work.OddEnvelope.tStar < bY := by
    have h := Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi hICF.strictAntiOn_y hYl
      (1 - Work.OddEnvelope.tau) (by norm_num [Work.OddEnvelope.tau])
    have hy1 : y (1 - Work.OddEnvelope.tau) =
        Work.OddEnvelope.profileX (1 - Work.OddEnvelope.tau) := hICF.y_tail _ le_rfl
    rw [hy1] at h
    simpa [Work.OddEnvelope.tStar] using h
  have hC : C = Work.OddCurve.refConst n := by
    have h1 := hA 1 (by norm_num) le_rfl
    have h2 := truncFree_momentA_big (bX := bX) (bY := bY) hICF hXt hYt n (le_refl (1:ℝ))
    have h1' : (∫ t in (-x 1)..(y 1),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
          (1 * t + h 1) ^ 2) ^ n *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (1 * t + h 1) ^ 2)) = C / Real.sqrt (1 + 1 ^ 2) := by
      rw [← h1]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [truncFree_eqOn_section hICF hXl hYl hbXpos hbYpos (by norm_num : (0:ℝ) < 1) t ht]
    have h3 : C / Real.sqrt (1 + 1 ^ 2) =
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt (1 + 1 ^ 2) := by
      rw [← h1', h2]
    rw [show (1:ℝ) + 1 ^ 2 = 2 by norm_num] at h3
    exact (div_left_inj' (by positivity : Real.sqrt 2 ≠ 0)).mp h3
  have hA_all : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
          (s * t + h s) ^ 2) ^ n *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t + h s) ^ 2)) = Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2) := by
    intro s hs
    rcases lt_or_ge s 1 with hlt | hge
    · have h1 := hA s hs hlt.le
      rw [hC] at h1
      rw [← h1]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [truncFree_eqOn_section hICF hXl hYl hbXpos hbYpos hs t ht]
    · exact truncFree_momentA_big (bX := bX) (bY := bY) hICF hXt hYt n hge
  have hB_all : ∀ s : ℝ, 0 < s →
      (∫ t in (-x s)..(y s),
        (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
          (s * t + h s) ^ 2) ^ (n - 1) *
          Real.sqrt (truncFree bX bY (Work.OddVolterra.Free.envProfileFree h x y) t ^ 2 -
            (s * t + h s) ^ 2) * (t + deriv h s)) = 0 := by
    intro s hs
    rcases lt_or_ge s 1 with hlt | hge
    · have h1 := hB s hs hlt.le
      rw [← h1]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [truncFree_eqOn_section hICF hXl hYl hbXpos hbYpos hs t ht]
    · exact truncFree_momentB_big (bX := bX) (bY := bY) hICF hXt hYt n hge
  exact Work.OddCurve.Free.oddFamilyData_of_momentEquationsGeneralFull (d := d) hd hdodd n hdn hn
    hbXpos hbYpos (truncFree_support bX bY _)
    (truncFree_contDiffOn hICF hXl hYl)
    (truncFree_strictConcaveOn hICF hXl hYl hbXpos hbYpos)
    (truncFree_continuousOn hICF hXl hYl hbXpos hbYpos)
    (by simp only [truncFree, if_neg (by simp : ¬ (-bX) ∈ Set.Ioo (-bX) bY)])
    (by simp only [truncFree, if_neg (by simp : ¬ bY ∈ Set.Ioo (-bX) bY)])
    (fun t ht => truncFree_pos hICF hXl hYl ht)
    hh_cont h0 hpos hsupp_icc
    (fun s hs => by
      obtain ⟨hR, hL⟩ := Work.OddVolterra.Free.envProfileFree_chord h x y hICF.smooth_x
        hICF.smooth_y hICF.x_deriv_neg hICF.y_deriv_neg (fun s hs => hICF.pos_x hs)
        (fun s hs => hICF.pos_y hs)
      refine ⟨hICF.pos_x hs, hICF.pos_y hs, ?_, ?_⟩
      · rw [truncFree_inside hICF hYl hbXpos hs]
      · rw [truncFree_inside_left hICF hXl hbYpos hs]
        ring)
    (fun s hs => section_mem hICF hXl hYl hbXpos hbYpos hs)
    hA_all hB_all

end Submission.Odd
