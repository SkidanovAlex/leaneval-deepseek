import Submission.Work.OddCurve.Free.Halves
import Submission.Work.OddCurve.Glue
import Submission.Work.OddVolterra.Existence.window_solution_three
import Submission.Work.OddVolterra.Existence.exists_isEnvelopeCurve_of_window_solution
import Submission.Work.Anchor.moment_eqs

/-!
# Step 2, in the corrected chain: the anchor exists

The transition-window half of the odd construction (the paper's Step 2) is **already proved** in
this workspace, at the state level:

* `Work.OddVolterra.Existence.WindowSolutionThree n` (`Existence/window_solution_three.lean`) —
  the Volterra system `(hah44)` on the slope window `(1/4, 1)`, with a `C^∞` state `1/1000`-close
  to the ball's (in `C¹`) and with the derivative rows pinned to the derivatives of the curve;
* `Work.OddVolterra.Existence.exists_isEnvelopeCurve_of_window_solution` — from such a state, an
  envelope curve `(X,Y)`, `C^∞` on `(0,∞)`, `1/100`-close to the semicircle's chord function
  (the state is *ramped* back to the semicircle near `s = 0` by the gluing function `gluePhi`, so
  that the anchor's tips *are* at `±1`; this is why the anchor, unlike the final curve, does satisfy
  the tip-normalised interface `IsEnvelopeCurve`);
* `Work.Anchor.moment_eqs` — the two moment equations on `(1/2, 1]` at the `momentF/momentH`
  level.

This file collects those three into `Work.OddCurve.Free.AnchorWindowFree n`
(`= Work.OddVolterra.Existence.AnchorWindowThree n`), i.e. **the Step-2 half of
`Work.OddCurve.Free.LowSlopeExtensionFree`'s input is available unconditionally**.  Consequently
the corrected deliverable of the odd case reduces to the *single* remaining statement

  `Work.OddCurve.Free.LowSlopeExtensionFree n`,

see `oddCurveExistsFreeThree_of_lowSlopeExtensionFree` and
`odd_curve_exists_free_written_three_of_lowSlopeExtensionFree` below.
-/

namespace Work.OddCurve
namespace Free

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise Interval

/-- **The anchor of the transition window exists.**  Proved from the workspace's
`WindowSolutionThree` (the paper's Step 2), the gluing lemma `exists_isEnvelopeCurve_of_window_solution`
and `Work.Anchor.moment_eqs`. -/
theorem anchorWindowFree_of_windowSolutionThree (n : ℕ) (hn : 1 ≤ n)
    (H : Work.OddVolterra.Existence.WindowSolutionThree n) : AnchorWindowFree n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨min ε (1 / 100), lt_min hε (by norm_num), fun h hb hne => ?_⟩
  have hεle : min ε (1 / 100) ≤ ε := min_le_left _ _
  have h100 : min ε (1 / 100) ≤ 1 / 100 := min_le_right _ _
  have hbε : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h :=
    ⟨hb.1, hb.2.1, fun k hk s => le_trans (hb.2.2.1 k hk s) hεle, hb.2.2.2⟩
  -- the bump vanishes at `0`
  have h0 : h 0 = 0 := by
    by_contra hne0
    have hmem := hb.2.1 (Function.mem_support.mpr hne0)
    simp only [Set.mem_Ioo] at hmem
    have hτ : (0 : ℝ) < 1 - 2 * Work.OddVolterra.tau := by
      norm_num [Work.OddVolterra.tau]
    linarith [hmem.1, hmem.2]
  obtain ⟨Z, hZsm, hZsys, hZtail, hZclose, hZderiv, hZsign⟩ := H' h hbε h0 hne
  -- the support, as a closed interval
  have hsuppIcc : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau) :=
    fun t ht => ⟨(hb.2.1 ht).1.le, (hb.2.1 ht).2.le⟩
  -- the three `1/100` bounds on `h`
  have hhsmall : ∀ s : ℝ, |h s| ≤ 1 / 100 ∧ |deriv h s| ≤ 1 / 100 ∧
      |deriv (deriv h) s| ≤ 1 / 100 := fun s =>
    Work.OddVolterra.Existence.IsSmallFlatBumpThree.close_h h100 hb hn s
  -- the anchor curve
  obtain ⟨X, Y, hIC, hclose6, hXY⟩ :=
    Work.OddVolterra.Existence.exists_isEnvelopeCurve_of_window_solution n hn hb.1 hsuppIcc
      hhsmall hZsm hZtail hZclose hZderiv hZsign
  have hcX : LowSlope.CloseToProfileX X := fun s hs =>
    ⟨(hclose6 s hs).1, (hclose6 s hs).2.1, (hclose6 s hs).2.2.1⟩
  have hcY : LowSlope.CloseToProfileX Y := fun s hs =>
    ⟨(hclose6 s hs).2.2.2.1, (hclose6 s hs).2.2.2.2.1, (hclose6 s hs).2.2.2.2.2⟩
  -- the anchor's state agrees with the window solution on `(1/2, 1]`
  have hstate : ∀ u : ℝ, 1 / 2 < u → Work.OddVolterra.stateOf X Y u = Z u := by
    intro u hu
    have heqX : X =ᶠ[𝓝 u] (fun t : ℝ => Z t 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with t ht
      exact (hXY t ht.le).1
    have heqY : Y =ᶠ[𝓝 u] (fun t : ℝ => Z t 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with t ht
      exact (hXY t ht.le).2
    have hd2 : deriv (fun t : ℝ => Z t 0) u = Z u 2 := (hZderiv u (by linarith)).1
    have hd3 : deriv (fun t : ℝ => Z t 1) u = Z u 3 := (hZderiv u (by linarith)).2
    ext i
    fin_cases i
    · simpa [Work.OddVolterra.stateOf] using (hXY u hu.le).1
    · simpa [Work.OddVolterra.stateOf] using (hXY u hu.le).2
    · simpa [Work.OddVolterra.stateOf] using (heqX.deriv_eq.trans hd2)
    · simpa [Work.OddVolterra.stateOf] using (heqY.deriv_eq.trans hd3)
  have hsystem : ∀ s ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s) =
        (∫ σ in s..(1 : ℝ),
            Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) +
          Work.OddVolterra.Xi n h s := by
    intro s hs
    have hs14 : s ∈ Set.Ioo (1 / 4 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    rw [hstate s hs.1, hZsys s hs14]
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le (le_of_lt hs.2)] at hσ
    rw [hstate σ (lt_of_lt_of_le hs.1 hσ.1)]
  obtain ⟨hmA, hmB⟩ := Work.Anchor.moment_eqs n hn hb.1 hsuppIcc hIC hclose6 hsystem
  refine ⟨X, Y, hIC, hcX, hcY, ?_, ?_⟩
  · intro s hs1 hs2
    have hs : (1 / 2 : ℝ) < s := by
      have h : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by
        norm_num [Work.OddVolterra.tau]
      linarith
    rw [momentA_eq_momentF, refConst_eq_oddSemicircleMomentConstant]
    exact hmA s hs hs2
  · intro s hs1 hs2
    have hs : (1 / 2 : ℝ) < s := by
      have h : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by
        norm_num [Work.OddVolterra.tau]
      linarith
    rw [momentB_eq_momentH]
    exact hmB s hs hs2

/-- **Step 2 is unconditional**: the workspace's `window_solution_three` supplies the anchor for
every sufficiently small flat bump. -/
theorem anchorWindowFree (n : ℕ) (hn : 1 ≤ n) : AnchorWindowFree n :=
  anchorWindowFree_of_windowSolutionThree n hn
    (Work.OddVolterra.Existence.window_solution_three n hn)

/-- **The corrected deliverable of the odd case follows from Step 3 alone.**  With Step 2 proved
(`anchorWindowFree`), the single remaining input of the whole odd case is
`Work.OddCurve.Free.LowSlopeExtensionFree n` — the paper's Step 3 (the spherical-Radon,
low-slope extension) *with free tips*. -/
theorem oddCurveExistsFreeThree_of_lowSlopeExtensionFree (n : ℕ) (hn : 1 ≤ n)
    (HL : LowSlopeExtensionFree n) : OddCurveExistsFreeThree n :=
  oddCurveExistsFreeThree_of_halves n hn (anchorWindowFree n hn) HL

/-- The same, written out textually: the corrected deliverable (`IsEnvelopeCurveFree` in place of
`IsEnvelopeCurve`, bump class `C^{n+3}`) from Step 3 alone. -/
theorem odd_curve_exists_free_written_three_of_lowSlopeExtensionFree (n : ℕ) (hn : 1 ≤ n)
    (HL : LowSlopeExtensionFree n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        IsEnvelopeCurveFree h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 -
                (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 -
                (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) :=
  odd_curve_exists_free_written_three n hn
    (oddCurveExistsFreeThree_of_lowSlopeExtensionFree n hn HL)

end

end Free
end Work.OddCurve
