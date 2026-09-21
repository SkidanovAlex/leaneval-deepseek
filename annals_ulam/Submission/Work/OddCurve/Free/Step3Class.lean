import Submission.Work.OddCurve.Free.Halves
import Submission.Work.OddCurve.Free.Reduction
import Submission.Work.OddCurve.Free.Step2
import Submission.Work.OddCurve.Free.momentEqsOn_Ioc_one_of_smallSlopes_free
import Submission.Work.OddVolterra.Free.Defs

/-!
# The corrected interface of the odd chord curve: bump class `C^{2n+2}`, untruncated profile

This file fixes the interface that the final assembly of the odd case must consume, and reduces
the corrected deliverable to the single `Prop` `LowSlopeExtensionFreeClass n` (paper Step 3).

## The three corrections to the literal request

1. **The bump class is `C^{2n+2}`, not `C²`.**  The construction differentiates the anchor's
   profile up to order `n + 1` (the spherical-Radon reconstruction) and the curve's `C²`-closeness
   costs `‖h‖_{C^{n+3}}`; for `k ≤ n + 1` that is `‖h‖_{C^{2n+2}}`.  The intermediate class
   `C^{n+3}` of `Work.OddCurve.Free.Halves` is *refuted* for `n ≥ 2`
   (`Submission/Work/OddVolterra/Free/NOTES_free_tips.md`).  Since `ε` is existential, raising the
   order costs the caller nothing: the bump is produced by `Submission.Odd.exists_odd_bump (2*n+2)`.

2. **The tips are free** (`IsEnvelopeCurveFree`): the reconstruction gives tips at `ρ(±1)`, which
   is a determined functional of the bump and is *not* `1`
   (`Submission/Work/OddCurve/NOTES_SESSION5.md`).  The endgame
   `Work.OddCurve.Free.oddFamilyData_of_momentEquationsGeneralFull` accepts an arbitrary
   `[-R₁, R₂]`, so this costs nothing.

3. **The profile is the untruncated `Work.OddVolterra.Free.envProfileFree`, not
   `Work.OddEnvelope.envelopeProfile`.**  `envelopeProfile` is defined to be `0` outside `[-1,1]`;
   for free tips the body's profile is positive on `(1, ρ(1))`, where the truncated profile is
   `0`, so the two *moment integrals differ* (the sections extend beyond `1`).  The two profiles
   agree on `|t| < 1` (`envProfileFree_eq_envelopeProfile`), which is why the tip-normalised
   statements (in which the tips are `±1`) are unaffected.

## Contents

* `SmallSlopeEqsFree` — the two moment equations on the transition slopes for the untruncated
  profile;
* `LowSlopeExtensionFreeClass` — **paper Step 3 in the corrected interface, the single remaining
  mathematical input**;
* `SmallSlopeCurveExistsFreeClass`, `OddCurveExistsFreeClass` — the transition-slope curve and the
  deliverable in the corrected interface, and their assembly from
  `Work.OddCurve.Free.AnchorWindowFree` (Step 2, proved) and `LowSlopeExtensionFreeClass`;
* `odd_curve_exists_free_written_class` — the corrected deliverable written out textually.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- The two moment equations on the transition slopes `0 < s ≤ 1 - τ`, for the **untruncated**
profile `Work.OddVolterra.Free.envProfileFree` — the profile of the body when the tips are not
normalised to `±1`. -/
def SmallSlopeEqsFree (n : ℕ) (h x y : ℝ → ℝ) : Prop :=
  MomentEqsOn n (refConst n) h x y (Work.OddVolterra.Free.envProfileFree h x y)
    (Set.Ioc 0 (1 - tau))

/-- The `C^{2n+2}` bump class is contained in the `C^{n+3}` class of the construction
(`n + 3 ≤ 2n + 2` for `n ≥ 1`). -/
theorem isSmallFlatBumpThree_of_class {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} {h : ℝ → ℝ}
    (hb : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h) :
    Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h :=
  ⟨hb.1, hb.2.1, fun k hk s => hb.2.2.1 k (by omega) s, hb.2.2.2⟩

/-- **The low-slope half of the odd construction (paper Step 3) in the corrected interface.**

For every bump `h ≠ 0` small in `C^{2n+2}` and every *anchor* envelope curve `(X, Y)` of `h`
(tip-normalised, as Step 2 produces it) satisfying the two moment equations on the transition
slopes `1 - 3τ < s ≤ 1`, there is a curve `(x, y)` which

* is a free-tip envelope curve, `C²`-close to the semicircle's chord function;
* and satisfies the two moment equations on **all** slopes `0 < s ≤ 1`, with the profile realised
  as the untruncated envelope `Work.OddVolterra.Free.envProfileFree h x y`.

**This is the single remaining mathematical input of the odd case.** -/
def LowSlopeExtensionFreeClass (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ,
    Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h → h ≠ 0 →
    Work.OddEnvelope.IsEnvelopeCurve h X Y → LowSlope.CloseToProfileX X →
    LowSlope.CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      IsEnvelopeCurveFree h x y ∧ LowSlope.CloseToProfileX x ∧ LowSlope.CloseToProfileX y ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
          refConst n / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0)

/-- The transition-slope curve in the corrected interface. -/
def SmallSlopeCurveExistsFreeClass (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
    Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h → h ≠ 0 →
    ∃ x y : ℝ → ℝ, IsEnvelopeCurveFree h x y ∧ SmallSlopeEqsFree n h x y

/-- The corrected deliverable: for every bump small in `C^{2n+2}` there is a free-tip envelope
curve whose untruncated profile satisfies both moment equations on all slopes `0 < s ≤ 1`. -/
def OddCurveExistsFreeClass (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
    Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h → h ≠ 0 →
    ∃ C : ℝ, ∃ x y : ℝ → ℝ,
      IsEnvelopeCurveFree h x y ∧
        MomentEqsOn n C h x y (Work.OddVolterra.Free.envProfileFree h x y) (Set.Ioc 0 1)

/-- **The two halves give the transition-slope curve**, in the corrected interface.  Step 2 is the
proved `Work.OddCurve.Free.AnchorWindowFree` (at the smaller class `C^{n+3}`, which contains
`C^{2n+2}`), Step 3 is `LowSlopeExtensionFreeClass`. -/
theorem smallSlopeCurveExistsFreeClass_of_halves (n : ℕ) (hn : 1 ≤ n)
    (ha : AnchorWindowFree n) (he : LowSlopeExtensionFreeClass n) :
    SmallSlopeCurveExistsFreeClass n := by
  obtain ⟨ε₁, hε₁, ha⟩ := ha
  obtain ⟨ε₂, hε₂, he⟩ := he
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun h hb hne => ?_⟩
  have hb₁ : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε₁ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k (by omega) s) (min_le_left _ _), hb.2.2.2⟩
  obtain ⟨X, Y, hX, hcX, hcY, hma, hmb⟩ := ha h hb₁ hne
  have hb₂ : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε₂ h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) (min_le_right _ _), hb.2.2.2⟩
  obtain ⟨x, y, hx, hxc, hyc, hmA, hmB⟩ := he h X Y hb₂ hne hX hcX hcY hma hmb
  refine ⟨x, y, hx, ?_⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  exact hmA s hs.1 (by linarith [hs.2, tau_pos])
  exact hmB s hs.1 (by linarith [hs.2, tau_pos])


/-! ## The tail: from the transition slopes to all slopes, for the untruncated profile -/

/-- On the slopes `s > 1 - τ` the section `[-(x s), y s]` is inside `(-1,1)` (the curve is the
semicircle's there), so the truncated and the untruncated profile agree on it. -/
private lemma section_subset_Ioo_of_tail {h x y : ℝ → ℝ} (H : IsEnvelopeCurveFree h x y)
    {s : ℝ} (hs : 1 - tau < s) :
    ∀ t ∈ Set.uIcc (-(x s)) (y s), t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hpos : (0 : ℝ) < 1 - Work.OddEnvelope.tau := by norm_num [Work.OddEnvelope.tau]
  have hs' : (1 - Work.OddEnvelope.tau : ℝ) < s := hs
  have hsq : (1 - Work.OddEnvelope.tau) ^ 2 ≤ s ^ 2 := by nlinarith
  have hle : Work.OddEnvelope.profileX s ≤ Work.OddEnvelope.tStar := by
    rw [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX, Work.OddEnvelope.profileX]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_le_sqrt (by linarith))
  have hxs : x s = Work.OddEnvelope.profileX s := H.x_tail s hs.le
  have hys : y s = Work.OddEnvelope.profileX s := H.y_tail s hs.le
  have hneg : -(x s) ≤ y s := by
    rw [hxs, hys]
    linarith [Work.OddEnvelope.profileX_pos s]
  intro t ht
  rw [Set.uIcc_of_le hneg, Set.mem_Icc] at ht
  constructor
  · rw [hxs] at ht
    linarith [ht.1, hle, Work.OddEnvelope.tStar_lt_one]
  · rw [hys] at ht
    linarith [ht.2, hle, Work.OddEnvelope.tStar_lt_one]

/-- On the slopes `s > 1 - τ` the two profiles agree on the section, so the volume moment
integrals coincide. -/
theorem momentA_eq_envelopeProfile_of_tail (n : ℕ) {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 1 - tau < s) :
    momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
      momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s := by
  simp only [momentA, rad]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Work.OddVolterra.Free.envProfileFree_eq_envelopeProfile (section_subset_Ioo_of_tail H hs t ht)]

/-- The same for the centroid moment integral. -/
theorem momentB_eq_envelopeProfile_of_tail (n : ℕ) {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurveFree h x y) {s : ℝ} (hs : 1 - tau < s) :
    momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
      momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s := by
  simp only [momentB, rad]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Work.OddVolterra.Free.envProfileFree_eq_envelopeProfile (section_subset_Ioo_of_tail H hs t ht)]

/-- **The two moment equations on all slopes `0 < s ≤ 1`, for the untruncated profile**, from the
transition-slope equations and the semicircular tail. -/
theorem momentEqsOn_free_of_smallSlopeEqsFree (n : ℕ) {h x y : ℝ → ℝ}
    (H : IsEnvelopeCurveFree h x y)
    (hz : ∀ s : ℝ, 1 - tau < s → Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0))
    (hsmall : SmallSlopeEqsFree n h x y) :
    MomentEqsOn n (refConst n) h x y (Work.OddVolterra.Free.envProfileFree h x y)
      (Set.Ioc 0 1) := by
  obtain ⟨hA, hB⟩ := hsmall
  obtain ⟨tA, tB⟩ := tail_moment_eqs_free n H hz
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · by_cases hle : s ≤ 1 - tau
    · exact hA s ⟨hs.1, hle⟩
    · rw [momentA_eq_envelopeProfile_of_tail n H (lt_of_not_ge hle)]
      exact tA s ⟨lt_of_not_ge hle, hs.2⟩
  · by_cases hle : s ≤ 1 - tau
    · exact hB s ⟨hs.1, hle⟩
    · rw [momentB_eq_envelopeProfile_of_tail n H (lt_of_not_ge hle)]
      exact tB s ⟨lt_of_not_ge hle, hs.2⟩

/-- **The transition-slope curve gives the corrected deliverable.** -/
theorem oddCurveExistsFreeClass_of_smallSlopeCurveExistsFreeClass (n : ℕ) (hn : 1 ≤ n)
    (H : SmallSlopeCurveExistsFreeClass n) : OddCurveExistsFreeClass n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hb hne => ?_⟩
  obtain ⟨x, y, hfr, hsl⟩ := H' h hb hne
  refine ⟨refConst n, x, y, hfr, ?_⟩
  refine momentEqsOn_free_of_smallSlopeEqsFree n hfr (fun s hs => ?_) hsl
  filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
  by_contra hmem
  exact absurd (hb.2.1 (Function.mem_support.mpr hmem)).2 (not_lt.mpr ht.le)

/-- **The corrected deliverable from Step 3 alone.** -/
theorem oddCurveExistsFreeClass_of_lowSlopeExtensionFreeClass (n : ℕ) (hn : 1 ≤ n)
    (HL : LowSlopeExtensionFreeClass n) : OddCurveExistsFreeClass n :=
  oddCurveExistsFreeClass_of_smallSlopeCurveExistsFreeClass n hn
    (smallSlopeCurveExistsFreeClass_of_halves n hn (anchorWindowFree n hn) HL)


/-! ## The same statement in the shape of the sibling chapter's composition target -/

/-- **The single remaining input of the odd case**, in exactly the shape of the (in-flight)
`Work.OddVolterra.Free.lowSlopeThreeFree_nonzero`: paper Step 3 with free tips, at the bump class
`C^{2n+2}`, and with the untruncated profile `envProfileFree`.

This is the same statement as `LowSlopeExtensionFreeClass` up to the order of the binders, so the
two are interchangeable; it is recorded separately so that the composition can be handed to a
prover in either chapter, and so that a proof of one is a proof of the other. -/
def LowSlopeThreeFreeC (n : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ,
    Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h → h ≠ 0 →
    Work.OddEnvelope.IsEnvelopeCurve h X Y → LowSlope.CloseToProfileX X →
    LowSlope.CloseToProfileX Y →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        refConst n / Real.sqrt (1 + s ^ 2)) →
    (∀ s : ℝ, 1 - 3 * tau < s → s ≤ 1 →
      momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
    ∃ x y : ℝ → ℝ,
      IsEnvelopeCurveFree h x y ∧ LowSlope.CloseToProfileX x ∧ LowSlope.CloseToProfileX y ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        momentA n h x y (Work.OddVolterra.Free.envProfileFree h x y) s =
          refConst n / Real.sqrt (1 + s ^ 2)) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 →
        momentB n h x y (Work.OddVolterra.Free.envProfileFree h x y) s = 0)

theorem lowSlopeExtensionFreeClass_of_lowSlopeThreeFreeC (n : ℕ) (H : LowSlopeThreeFreeC n) :
    LowSlopeExtensionFreeClass n := H

theorem lowSlopeThreeFreeC_of_lowSlopeExtensionFreeClass (n : ℕ)
    (H : LowSlopeExtensionFreeClass n) : LowSlopeThreeFreeC n := H

/-- **The corrected deliverable from the Step-3 input in either shape.** -/
theorem oddCurveExistsFreeClass_of_lowSlopeThreeFreeC (n : ℕ) (hn : 1 ≤ n)
    (H : LowSlopeThreeFreeC n) : OddCurveExistsFreeClass n :=
  oddCurveExistsFreeClass_of_lowSlopeExtensionFreeClass n hn
    (lowSlopeExtensionFreeClass_of_lowSlopeThreeFreeC n H)

/-- **The corrected deliverable, written out textually.**  The shape of the request with
`IsEnvelopeCurve` replaced by `IsEnvelopeCurveFree`, the bump class raised to `C^{2n+2}`
(so that `Submission.Odd.exists_odd_bump (2 * n + 2) ε` instantiates it) and the profile taken to
be the untruncated `Work.OddVolterra.Free.envProfileFree` (the truncated `envelopeProfile` is `0`
outside `[-1,1]`, whereas the reconstruction's tips are at `ρ(±1) = 1 + O(ε)`, so the two
*integrals* differ for small slopes). -/
theorem odd_curve_exists_free_written_class (n : ℕ) (hn : 1 ≤ n)
    (H : OddCurveExistsFreeClass n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, h ≠ 0 →
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ k : ℕ, k ≤ 2 * n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        IsEnvelopeCurveFree h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 -
                (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddVolterra.Free.envProfileFree h x y t ^ 2 -
                (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hne hcont hsupp hbnd hflat => ?_⟩
  have hsupp' : Function.support h ⊆
      Set.Ioo (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro t ht
    have h := hsupp ht
    simpa [Work.OddVolterra.tau] using h
  have hflat' : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
      s < 1 - 2 * Work.OddVolterra.tau + η → h s = 0 := by
    obtain ⟨η, hη, hf⟩ := hflat
    exact ⟨η, hη, fun s hs hs' => hf s (by simpa [Work.OddVolterra.tau] using hs)
      (by simpa [Work.OddVolterra.tau] using hs')⟩
  have hb : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h :=
    ⟨hcont, hsupp', hbnd, hflat'⟩
  obtain ⟨C, x, y, hfr, hme⟩ := H' h hb hne
  exact ⟨C, x, y, hfr, fun s hs hs1 => hme.1 s ⟨hs, hs1⟩, fun s hs hs1 => hme.2 s ⟨hs, hs1⟩⟩

end

end Free
end Work.OddCurve
