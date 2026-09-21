import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddVolterra.Free.free_slope_api
import Submission.Work.OddCurve.LowSlope.chord_eq_radial

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

/-!
# The radial graph identity for the free-tip low-slope reconstruction

`Work.OddCurve.LowSlope.rhoNew R r` is the radial function of the body reconstructed from the glued
Radon data, whose chord-endpoint curve is the two-piece curve
`(Work.OddCurve.LowSlope.lowSlopeCurveX r X, Work.OddCurve.LowSlope.lowSlopeCurveY R Y)`.  The
identity proved here says that the radial point `rhoNew R r u · (u, √(1-u²))` lies on the graph of
the envelope profile of that curve:

`rhoNew R r u * √(1-u²) = envProfileFree h x y (rhoNew R r u * u)`.

This is the `hgraph` hypothesis of
`Work.OddVolterra.Free.momentEqs_lowSlopes_of_datum_ball_free` in the free-tip setting.

The two-piece curve is the anchor's `(X, Y)` on the slopes `σ ≥ 3/4` and the radial
parametrisation `σ ↦ R(arctan σ) cos(arctan σ)` (resp. `r`) below.  Accordingly the proof splits
along the value of `u`:

* for `|u| > 4/5` the radial slope `tan (arccos |u|)` is `< 3/4`, so the point `rhoNew R r u · u`
  is *by definition* the chord endpoint of slope `tan (arccos |u|)` of the reconstructed curve,
  and the chord identity for `envProfileFree` gives the value, the bump `h` vanishing below `3/4`;
* for `|u| ≤ 4/5` the `hcap` hypothesis identifies `rhoNew R r u` with the anchor's radial function
  `ρa`; the radial point is then a chord endpoint of the *anchor's* curve at a slope `≥ 3/4`
  (because it lies to the left of the corner point, which is the assertion
  `Y (3/4) = ρa (4/5) · (4/5)` proved below by the uniqueness of the linear intersection), and on
  the slopes `≥ 3/4` the reconstructed curve coincides with the anchor's.
-/

/-- The bump of an envelope curve vanishes strictly below the transition window
`[1 - 2τ, 1 - τ] = [4/5, 9/10]`; in particular `h (3/4) = 0`. -/
lemma h_eq_zero_of_lt_three_quarters {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) {σ : ℝ} (hσ : σ < 3 / 4) : h σ = 0 := by
  by_contra hne
  have hmem : σ ∈ Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) :=
    H.h_support (Function.mem_support.mpr hne)
  rw [Set.mem_Icc] at hmem
  have hτ : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by norm_num [Work.OddEnvelope.tau]
  rw [hτ] at hmem
  linarith [hmem.1]

/-- The bump vanishes at the low threshold `3/4` (which lies strictly below the support window). -/
lemma h_eq_zero_of_three_quarters {h X Y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y) : h (3 / 4) = 0 := by
  by_contra hne
  have hmem : (3 / 4 : ℝ) ∈
      Set.Icc (1 - 2 * Work.OddEnvelope.tau) (1 - Work.OddEnvelope.tau) :=
    H.h_support (Function.mem_support.mpr hne)
  rw [Set.mem_Icc] at hmem
  have hτ : (1 : ℝ) - 2 * Work.OddEnvelope.tau = 4 / 5 := by norm_num [Work.OddEnvelope.tau]
  rw [hτ] at hmem
  linarith [hmem.1]

/-- **The anchor's right chord endpoint at slope `3/4` is the radial point at `u = 4/5`.**  Both
points lie on the line `t ↦ (3/4) t` (the bump vanishes at `3/4`), whence they coincide by the
uniqueness of the linear intersection with a strictly concave profile. -/
lemma anchor_radial_pt_Y {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) :
    Y (3 / 4) = ρ (4 / 5) * (4 / 5) := by
  have h34 : h (3 / 4) = 0 := h_eq_zero_of_three_quarters H
  have hconc := Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hf0 : Work.OddEnvelope.envelopeProfile h X Y 0 = 1 :=
    Work.OddEnvelope.envelopeProfile_zero
  have ha : Y (3 / 4) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨H.toChordCurve_y.pos (by norm_num), H.toChordCurve_y.lt_one (by norm_num)⟩
  have hfa : Work.OddEnvelope.envelopeProfile h X Y (Y (3 / 4)) = (3 / 4) * Y (3 / 4) := by
    rw [Work.OddEnvelope.envelopeProfile_root_right H (by norm_num), h34, add_zero]
  have hsqrt : Real.sqrt (1 - (4 / 5 : ℝ) ^ 2) = 3 / 5 := by
    have h1 : (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 := by norm_num
    rw [h1, Real.sqrt_sq (by norm_num)]
  set b : ℝ := ρ (4 / 5) * (4 / 5) with hb
  have hbpos : 0 < b := mul_pos (hpos (4 / 5) (by norm_num)) (by norm_num)
  have hfb : Work.OddEnvelope.envelopeProfile h X Y b = (3 / 4) * b := by
    rw [hb, ← hgraph (4 / 5) (by norm_num), hsqrt]; ring
  have hbne : Work.OddEnvelope.envelopeProfile h X Y b ≠ 0 := by rw [hfb]; positivity
  have hbmem : b ∈ Set.Icc (-1 : ℝ) 1 := Work.OddEnvelope.envelopeProfile_support hbne
  have hbIoo : b ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨hbpos, ?_⟩
    rcases lt_or_eq_of_le hbmem.2 with h | h
    · exact h
    · exfalso
      rw [h, Work.OddEnvelope.envelopeProfile_right_end] at hfb
      norm_num at hfb
  exact (Work.OddCurve.LowSlope.eq_linear_unique_pos hconc hf0 ha hfa b hbIoo hfb).symm

/-- **The anchor's left chord endpoint at slope `3/4` is the radial point at `u = -4/5`.** -/
lemma anchor_radial_pt_X {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) :
    X (3 / 4) = ρ (-(4 / 5)) * (4 / 5) := by
  have h34 : h (3 / 4) = 0 := h_eq_zero_of_three_quarters H
  have hconc := Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hf0 : Work.OddEnvelope.envelopeProfile h X Y 0 = 1 :=
    Work.OddEnvelope.envelopeProfile_zero
  have ha : -(X (3 / 4)) ∈ Set.Ioo (-1 : ℝ) 0 := by
    have hp : 0 < X (3 / 4) := H.toChordCurve_x.pos (s := 3 / 4) (by norm_num)
    have hl : X (3 / 4) < 1 := H.toChordCurve_x.lt_one (s := 3 / 4) (by norm_num)
    exact ⟨by linarith, by linarith⟩
  have hfa : Work.OddEnvelope.envelopeProfile h X Y (-(X (3 / 4))) =
      -((3 / 4) * (-(X (3 / 4)))) := by
    rw [Work.OddEnvelope.envelopeProfile_root_left H (by norm_num), h34]
    ring
  have hsqrt : Real.sqrt (1 - (-(4 / 5) : ℝ) ^ 2) = 3 / 5 := by
    have h1 : (1 : ℝ) - (-(4 / 5)) ^ 2 = (3 / 5) ^ 2 := by norm_num
    rw [h1, Real.sqrt_sq (by norm_num)]
  set b : ℝ := ρ (-(4 / 5)) * (-(4 / 5)) with hb
  have hbneg : b < 0 := by
    rw [hb]
    nlinarith [hpos (-(4 / 5)) (by norm_num)]
  have hfb : Work.OddEnvelope.envelopeProfile h X Y b = -((3 / 4) * b) := by
    rw [hb, ← hgraph (-(4 / 5)) (by norm_num), hsqrt]
    ring
  have hbne : Work.OddEnvelope.envelopeProfile h X Y b ≠ 0 := by
    rw [hfb]; exact ne_of_gt (by nlinarith [hbneg])
  have hbmem : b ∈ Set.Icc (-1 : ℝ) 1 := Work.OddEnvelope.envelopeProfile_support hbne
  have hbIoo : b ∈ Set.Ioo (-1 : ℝ) 0 := by
    refine ⟨?_, hbneg⟩
    rcases lt_or_eq_of_le hbmem.1 with h | h
    · exact h
    · exfalso
      rw [← h, Work.OddEnvelope.envelopeProfile_left_end] at hfb
      norm_num at hfb
  have huniq := Work.OddCurve.LowSlope.eq_linear_unique_neg hconc hf0 ha hfa b hbIoo hfb
  rw [hb] at huniq
  have h2 : ρ (-(4 / 5)) * (-(4 / 5)) = -(ρ (-(4 / 5)) * (4 / 5)) := by ring
  linarith [huniq, h2]

/-- `tan (arccos u) > 0` for `0 < u < 1`. -/
lemma tan_arccos_pos {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 < Real.tan (Real.arccos u) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two ((Real.arccos_pos).mpr hu1)
    ((Real.arccos_lt_pi_div_two).mpr hu)

/-- `tan (arccos u) < 3/4` for `4/5 < u < 1`: the radial slope of the outer region of the
reconstruction, which is the threshold of the two-piece curve. -/
lemma tan_arccos_lt_three_quarters {u : ℝ} (hu : 4 / 5 < u) (hu1 : u < 1) :
    Real.tan (Real.arccos u) < 3 / 4 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hcos : Real.cos (Real.arccos u) = u := Real.cos_arccos (by linarith) (le_of_lt hu1)
  have hsin : Real.sin (Real.arccos u) = Real.sqrt (1 - u ^ 2) := Real.sin_arccos u
  have hsq : (4 / 5 : ℝ) ^ 2 < u ^ 2 := by nlinarith
  rw [Real.tan_eq_sin_div_cos, hsin, hcos, div_lt_iff₀ hu0]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 3 / 4 * u)]
  refine Real.sqrt_lt_sqrt (by nlinarith) ?_
  nlinarith

theorem envProfileFree_hgraph (n : ℕ) (hn : 1 ≤ n) {ε η : ℝ} {h X Y ρa R r : ℝ → ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 1000)
    (hb : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h)
    (hne : h ≠ 0)
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hanc : Work.OddVolterra.Free.IsAnchorRadial h X Y ρa)
    (hfr : Work.OddCurve.Free.IsEnvelopeCurveFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
        (Work.OddCurve.LowSlope.lowSlopeCurveY R Y))
    (hbnd : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      1 - η ≤ R α ∧ 1 - η ≤ r α ∧ |deriv R α| ≤ η * α ∧ |deriv r α| ≤ η * α ∧
        |deriv (deriv R) α| ≤ η ∧ |deriv (deriv r) α| ≤ η)
    (hcap : ∀ u : ℝ, |u| ≤ 4 / 5 → Work.OddCurve.LowSlope.rhoNew R r u = ρa u) :
    ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      Work.OddCurve.LowSlope.rhoNew R r u * Real.sqrt (1 - u ^ 2) =
        Work.OddVolterra.Free.envProfileFree h (Work.OddCurve.LowSlope.lowSlopeCurveX r X)
          (Work.OddCurve.LowSlope.lowSlopeCurveY R Y)
          (Work.OddCurve.LowSlope.rhoNew R r u * u) := by
  intro u hu
  set x : ℝ → ℝ := Work.OddCurve.LowSlope.lowSlopeCurveX r X with hxdef
  set y : ℝ → ℝ := Work.OddCurve.LowSlope.lowSlopeCurveY R Y with hydef
  have hfr' : Work.OddCurve.Free.IsEnvelopeCurveFree h x y := by
    rw [hxdef, hydef]; exact hfr
  have hchord := Work.OddVolterra.Free.envProfileFree_chord h x y hfr'.smooth_x hfr'.smooth_y
    hfr'.x_deriv_neg hfr'.y_deriv_neg (fun s hs => hfr'.pos_x hs) (fun s hs => hfr'.pos_y hs)
  have hY34 : Y (3 / 4) = ρa (4 / 5) * (4 / 5) :=
    anchor_radial_pt_Y H hanc.1 hanc.2.2.2.1
  have hX34 : X (3 / 4) = ρa (-(4 / 5)) * (4 / 5) :=
    anchor_radial_pt_X H hanc.1 hanc.2.2.2.1
  have hRpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < R α := by
    intro α hα
    have h1 := (hbnd α hα).1
    have h2 : (0 : ℝ) < 1 - η := by linarith
    linarith
  have hrpos : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), 0 < r α := by
    intro α hα
    have h1 := (hbnd α hα).2.1
    have h2 : (0 : ℝ) < 1 - η := by linarith
    linarith
  have hYmono := H.toChordCurve_y.strictAntiOn
  have hXmono := H.toChordCurve_x.strictAntiOn
  have hTmono := hanc.2.2.1.monotoneOn
  rcases lt_trichotomy u 0 with hu_neg | hu_zero | hu_pos
  · -- ## `u < 0`
    rcases le_or_gt (-(4 / 5)) u with hge | hlt
    · -- ### `-4/5 ≤ u < 0`: the anchor's region
      have hru : Work.OddCurve.LowSlope.rhoNew R r u = ρa u :=
        hcap u (by rw [abs_of_neg hu_neg]; linarith)
      rw [hru]
      set t : ℝ := ρa u * u with ht
      have ht_neg : t < 0 := by
        rw [ht]; exact mul_neg_of_pos_of_neg (hanc.1 u hu) hu_neg
      have hm : ρa (-(4 / 5)) * (-(4 / 5)) ≤ ρa u * u :=
        hTmono (show -(4 / 5 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hu hge
      have hc' : -(ρa u * u) ≤ X (3 / 4) := by
        have hm' : ρa (-(4 / 5)) * (-(4 / 5)) = -(ρa (-(4 / 5)) * (4 / 5)) := by ring
        rw [hX34]; linarith
      have hc : -t ≤ X (3 / 4) := by rw [ht]; exact hc'
      have hclt1 : -t < 1 := lt_of_le_of_lt hc (H.toChordCurve_x.lt_one (by norm_num))
      have hcpos : 0 < -t := by rw [ht]; linarith
      set σ0 : ℝ := Work.OddEnvelope.slopeRight X (-t) with hσ0
      have hXσ : X σ0 = -t := H.toChordCurve_x.slopeRight_eq ⟨hcpos, hclt1⟩
      have hσ0pos : 0 < σ0 := H.toChordCurve_x.slopeRight_pos ⟨hcpos, hclt1⟩
      have hσ0ge : 3 / 4 ≤ σ0 := by
        by_contra hcon
        rw [not_le] at hcon
        have hlt' : X (3 / 4) < X σ0 :=
          hXmono (show σ0 ∈ Set.Ioi (0 : ℝ) from hσ0pos)
            (show (3 / 4 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hcon
        rw [hXσ] at hlt'
        linarith [hc]
      have hxσ : x σ0 = -t := by
        rw [hxdef, Work.OddCurve.LowSlope.lowSlopeCurveX_of_ge hσ0ge, hXσ]
      have hsl : Work.OddEnvelope.slopeLeft x t = σ0 := by
        rw [hσ0]; exact hfr'.slopeLeft_eq_of hσ0pos hxσ
      have hslX : Work.OddEnvelope.slopeLeft X t = σ0 := by rw [hσ0]; rfl
      have ht_Ioo : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hclt1], by linarith [ht_neg]⟩
      have hchord2 := hchord.2 σ0 hσ0pos
      rw [hxσ, neg_neg] at hchord2
      have hEnvt : Work.OddEnvelope.envelopeProfile h X Y t = -(σ0 * t + h σ0) := by
        rw [← Work.OddVolterra.Free.envProfileFree_eq_envelopeProfile ht_Ioo,
          Work.OddVolterra.Free.envProfileFree, if_neg (not_lt.mpr ht_neg.le), if_pos ht_neg]
        unfold Work.OddEnvelope.envelopeLeft
        rw [hslX]
      rw [hchord2, ← hEnvt, ht]
      exact hanc.2.2.2.1 u hu
    · -- ### `u < -4/5`: the radial piece
      set v : ℝ := -u with hv
      have hv_pos : 0 < v := by rw [hv]; linarith
      have hv45 : 4 / 5 < v := by rw [hv]; linarith
      have hv1 : v < 1 := by rw [hv]; linarith [hu.1]
      have huv : u = -v := by rw [hv]; ring
      have hvsq : (1 : ℝ) - u ^ 2 = 1 - v ^ 2 := by rw [huv]; ring
      have hru : Work.OddCurve.LowSlope.rhoNew R r u = r (Real.arccos v) := by
        rw [Work.OddCurve.LowSlope.rhoNew_of_neg hu_neg, ← hv]
      rw [hru]
      set t : ℝ := r (Real.arccos v) * u with ht
      have hmem_arccos : Real.arccos v ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨le_of_lt ((Real.arccos_pos).mpr hv1),
         le_of_lt ((Real.arccos_lt_pi_div_two).mpr hv_pos)⟩
      have hrv_pos : 0 < r (Real.arccos v) := hrpos _ hmem_arccos
      have ht_neg : t < 0 := by
        rw [ht]; exact mul_neg_of_pos_of_neg hrv_pos hu_neg
      have hσpos : 0 < Real.tan (Real.arccos v) := tan_arccos_pos hv_pos hv1
      have hσlt : Real.tan (Real.arccos v) < 3 / 4 := tan_arccos_lt_three_quarters hv45 hv1
      have harctan : Real.arctan (Real.tan (Real.arccos v)) = Real.arccos v :=
        Real.arctan_tan (by have := Real.arccos_nonneg v; linarith [Real.pi_pos])
          ((Real.arccos_lt_pi_div_two).mpr hv_pos)
      have hxσ : x (Real.tan (Real.arccos v)) = -t := by
        rw [hxdef, Work.OddCurve.LowSlope.lowSlopeCurveX_of_lt hσlt, harctan,
          Real.cos_arccos (by linarith) (le_of_lt hv1), ht, huv]
        ring
      have hsl : Work.OddEnvelope.slopeLeft x t = Real.tan (Real.arccos v) :=
        hfr'.slopeLeft_eq_of hσpos hxσ
      have hchord2 := hchord.2 (Real.tan (Real.arccos v)) hσpos
      rw [hxσ, neg_neg] at hchord2
      rw [hchord2, h_eq_zero_of_lt_three_quarters H hσlt, add_zero]
      rw [ht, hvsq, huv, Real.tan_eq_sin_div_cos, Real.sin_arccos v,
        Real.cos_arccos (by linarith) (le_of_lt hv1)]
      have hv0 : v ≠ 0 := ne_of_gt hv_pos
      field_simp
  · -- ## `u = 0`
    subst hu_zero
    have hru : Work.OddCurve.LowSlope.rhoNew R r 0 = 1 := by
      rw [hcap 0 (by norm_num), hanc.2.2.2.2]
    rw [hru]
    simp [Work.OddVolterra.Free.envProfileFree]
  · -- ## `u > 0`
    rcases le_or_gt u (4 / 5) with hle | hgt
    · -- ### `0 < u ≤ 4/5`: the anchor's region
      have hru : Work.OddCurve.LowSlope.rhoNew R r u = ρa u :=
        hcap u (by rw [abs_of_pos hu_pos]; exact hle)
      rw [hru]
      set t : ℝ := ρa u * u with ht
      have ht_pos : 0 < t := by
        rw [ht]; exact mul_pos (hanc.1 u hu) hu_pos
      have ht_le : t ≤ Y (3 / 4) := by
        have hm := hTmono hu (show (4 / 5 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num) hle
        rw [ht, hY34]; exact hm
      have ht_lt1 : t < 1 := lt_of_le_of_lt ht_le (H.toChordCurve_y.lt_one (by norm_num))
      set σ0 : ℝ := Work.OddEnvelope.slopeRight Y t with hσ0
      have hYσ : Y σ0 = t := H.toChordCurve_y.slopeRight_eq ⟨ht_pos, ht_lt1⟩
      have hσ0pos : 0 < σ0 := H.toChordCurve_y.slopeRight_pos ⟨ht_pos, ht_lt1⟩
      have hσ0ge : 3 / 4 ≤ σ0 := by
        by_contra hcon
        rw [not_le] at hcon
        have hlt' : Y (3 / 4) < Y σ0 :=
          hYmono (show σ0 ∈ Set.Ioi (0 : ℝ) from hσ0pos)
            (show (3 / 4 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hcon
        rw [hYσ] at hlt'
        linarith
      have hyσ : y σ0 = t := by
        rw [hydef, Work.OddCurve.LowSlope.lowSlopeCurveY_of_ge hσ0ge, hYσ]
      have hmain := hchord.1 σ0 hσ0pos
      rw [hyσ] at hmain
      have hroot := Work.OddEnvelope.envelopeProfile_root_right H hσ0pos
      rw [hYσ] at hroot
      rw [hmain, ← hroot, ht]
      exact hanc.2.2.2.1 u hu
    · -- ### `u > 4/5`: the radial piece
      have hu1 : u < 1 := hu.2
      have hru : Work.OddCurve.LowSlope.rhoNew R r u = R (Real.arccos u) :=
        Work.OddCurve.LowSlope.rhoNew_of_nonneg (le_of_lt hu_pos)
      rw [hru]
      have hσpos : 0 < Real.tan (Real.arccos u) := tan_arccos_pos hu_pos hu1
      have hσlt : Real.tan (Real.arccos u) < 3 / 4 := tan_arccos_lt_three_quarters hgt hu1
      have harctan : Real.arctan (Real.tan (Real.arccos u)) = Real.arccos u :=
        Real.arctan_tan (by have := Real.arccos_nonneg u; linarith [Real.pi_pos])
          ((Real.arccos_lt_pi_div_two).mpr hu_pos)
      have hyσ : y (Real.tan (Real.arccos u)) = R (Real.arccos u) * u := by
        rw [hydef, Work.OddCurve.LowSlope.lowSlopeCurveY_of_lt hσlt, harctan,
          Real.cos_arccos (by linarith) (le_of_lt hu1)]
      rw [← hyσ, hchord.1 (Real.tan (Real.arccos u)) hσpos, hyσ,
        h_eq_zero_of_lt_three_quarters H hσlt, add_zero,
        Real.tan_eq_sin_div_cos, Real.sin_arccos,
        Real.cos_arccos (by linarith) (le_of_lt hu1)]
      have hu0 : u ≠ 0 := ne_of_gt hu_pos
      field_simp

end

end Work.OddVolterra.Free
