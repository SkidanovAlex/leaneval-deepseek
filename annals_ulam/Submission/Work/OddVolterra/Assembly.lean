import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddEnvelope.MainClose

/-!
# Assembly of the transition-slope curve

This file isolates the two pieces the final theorem `Work.OddVolterra.odd_cap_curve` is assembled
from:

* `CurveData n h x y` — the transition-slope curve produced by the Volterra construction
  (`Work.OddVolterra.Existence.odd_transition_curve`): it carries exactly the data that the
  envelope chapter `Work.OddEnvelope` consumes, together with the Volterra equation of the paper;
* the bridge `Work.OddVolterra.Bridge.momentEqs_of_volterra` — the two moment equations for the
  envelope profile `Work.OddEnvelope.envelopeProfile h x y`, obtained from the Volterra equation
  by the row identities and Abel's inversion.

The assembly below only uses those two inputs plus the (proved) envelope chapter.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra

open Commons.Geometry.Ulam

noncomputable section

/-- The transition-slope curve: the data produced by the Volterra construction of the odd case,
in exactly the form the envelope chapter `Work.OddEnvelope` consumes.  `δ = 1/100` is the
closeness radius of `Work.OddEnvelope.odd_envelope_profile_of_close`; the curve is required to be
`C²`-close to the semicircle chord function in that radius. -/
structure CurveData (n : ℕ) (h : ℝ → ℝ) (x y : ℝ → ℝ) : Prop where
  smooth_x : ContDiffOn ℝ ∞ x (Set.Ioi 0)
  smooth_y : ContDiffOn ℝ ∞ y (Set.Ioi 0)
  deriv_x_neg : ∀ s : ℝ, 0 < s → deriv x s < 0
  deriv_y_neg : ∀ s : ℝ, 0 < s → deriv y s < 0
  pos_x : ∀ s : ℝ, 0 < s → 0 < x s
  pos_y : ∀ s : ℝ, 0 < s → 0 < y s
  close_h : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
    |deriv (deriv h) s| ≤ 1 / 100
  tendsto_x : Filter.Tendsto x (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 1)
  tendsto_y : Filter.Tendsto y (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 1)
  tail_x : ∀ s : ℝ, 1 - tau ≤ s → x s = profileX s
  tail_y : ∀ s : ℝ, 1 - tau ≤ s → y s = profileX s
  close_x : ∀ s : ℝ, 0 < s → |x s - profileX s| ≤ 1 / 100 ∧
    |deriv x s - deriv profileX s| ≤ 1 / 100 ∧
    |deriv (deriv x) s - deriv (deriv profileX) s| ≤ 1 / 100
  close_y : ∀ s : ℝ, 0 < s → |y s - profileX s| ≤ 1 / 100 ∧
    |deriv y s - deriv profileX s| ≤ 1 / 100 ∧
    |deriv (deriv y) s - deriv (deriv profileX) s| ≤ 1 / 100
  volterra : VolterraEqOn n h x y (Set.Ioo 0 1)

/-- Antivacuity for the envelope profile: at slope `1` (and at any slope `s > 0`) the cutting
section is non-degenerate, because the envelope chapter proves the radicand positive on the open
section. -/
theorem nondegenerate_envelopeProfile (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    Nondegenerate h x y (Work.OddEnvelope.envelopeProfile h x y) := by
  refine ⟨1, by norm_num, 0, ⟨?_, ?_⟩, ?_⟩
  · linarith [(H.toChordCurve_x.pos (show (0 : ℝ) < 1 by norm_num))]
  · linarith [(H.toChordCurve_y.pos (show (0 : ℝ) < 1 by norm_num))]
  · have h := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
      (Work.OddEnvelope.concaveOn_envelopeProfile H) (show (0 : ℝ) < 1 by norm_num)
      0 ⟨by linarith [(H.toChordCurve_x.pos (show (0 : ℝ) < 1 by norm_num))],
          by linarith [(H.toChordCurve_y.pos (show (0 : ℝ) < 1 by norm_num))]⟩
    simpa [psi, line] using h

/-- **The transition-slope deliverable, assembled from the two pieces.**

`Hex` is the output of the Volterra construction (`Existence/odd_transition_curve`): for every
admissible perturbation `h` it produces a curve with the `CurveData` of the envelope chapter.
`Hbridge` is the bridge `Bridge.momentEqs_of_volterra`: from the Volterra equation it derives the
two moment equations for the envelope profile.  The conclusion is the assignment's
`odd_cap_curve`, with the envelope `f` realised as `Work.OddEnvelope.envelopeProfile h x y` and
the anti-vacuity clause `Nondegenerate` supplied by `nondegenerate_envelopeProfile`. -/
theorem odd_cap_curve_of_pieces (n : ℕ) (hn : 1 ≤ n)
    (Hex : ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∃ x y : ℝ → ℝ, CurveData n h x y)
    (Hbridge : ∀ h x y : ℝ → ℝ, ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      CurveData n h x y →
      MomentEqsOn n (oddSemicircleMomentConstant n) h x y
        (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1)) :
    ∃ C : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h →
        Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
        (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * tau ≤ s → s < 1 - 2 * tau + η → h s = 0) →
        (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
        h 0 = 0 → h ≠ 0 →
        ∃ x y : ℝ → ℝ,
          (∀ s : ℝ, 0 < s → 0 < x s ∧ 0 < y s) ∧
          (∀ s : ℝ, 1 - tau ≤ s → x s = profileX s ∧ y s = profileX s) ∧
          (∀ s : ℝ, 0 < s → |x s - profileX s| ≤ 1 / 2 ∧ |y s - profileX s| ≤ 1 / 2) ∧
          VolterraEqOn n h x y (Set.Ioo 0 1) ∧
          MomentEqsOn n C h x y (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) ∧
          Nondegenerate h x y (Work.OddEnvelope.envelopeProfile h x y) := by
  obtain ⟨ε₀, hε₀, H⟩ := Hex
  refine ⟨oddSemicircleMomentConstant n, min ε₀ (1 / 100), lt_min hε₀ (by norm_num), ?_⟩
  intro h hh hsupp hflat hsmall h0 hne
  have hε' : min ε₀ (1 / 100) ≤ ε₀ := min_le_left _ _
  have h100 : min ε₀ (1 / 100) ≤ 1 / 100 := min_le_right _ _
  have hsmall₀ : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε₀ :=
    fun k hk s => le_trans (hsmall k hk s) hε'
  obtain ⟨x, y, hdata⟩ := H h hh hsupp hflat hsmall₀ h0 hne
  have hhIoi : ContDiffOn ℝ ∞ h (Set.Ioi 0) := hh.contDiffOn
  have hidx : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
      |deriv (deriv h) s| ≤ 1 / 100 := by
    intro s
    have h0' : |iteratedDeriv 0 h s| ≤ min ε₀ (1 / 100) := hsmall 0 (Nat.zero_le _) s
    have h1' : |iteratedDeriv 1 h s| ≤ min ε₀ (1 / 100) := hsmall 1 (by omega) s
    have h2' : |iteratedDeriv 2 h s| ≤ min ε₀ (1 / 100) := hsmall 2 (by omega) s
    have e0 : iteratedDeriv 0 h s = h s := by simp
    have e1 : iteratedDeriv 1 h s = deriv h s := by rw [iteratedDeriv_one]
    have e2 : iteratedDeriv 2 h s = deriv (deriv h) s := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    exact ⟨le_trans (le_of_eq (by rw [e0])) (le_trans h0' h100),
      le_trans (le_of_eq (by rw [e1])) (le_trans h1' h100),
      le_trans (le_of_eq (by rw [e2])) (le_trans h2' h100)⟩
  have hIC := Work.OddEnvelope.Close.isEnvelopeCurve_of_close (hδ := le_rfl)
    hdata.smooth_x hdata.smooth_y hhIoi hdata.deriv_x_neg hdata.deriv_y_neg
    hdata.tendsto_x hdata.tendsto_y hdata.tail_x hdata.tail_y h0 hsupp
    hdata.close_x hdata.close_y hdata.close_h
  refine ⟨x, y, fun s hs => ⟨hdata.pos_x s hs, hdata.pos_y s hs⟩,
    fun s hs => ⟨hdata.tail_x s hs, hdata.tail_y s hs⟩, ?_, hdata.volterra,
    Hbridge h x y hh hsupp hdata, nondegenerate_envelopeProfile n hIC⟩
  intro s hs
  have h1 := (hdata.close_x s hs).1
  have h2 := (hdata.close_y s hs).1
  constructor <;> linarith

end

end Work.OddVolterra
