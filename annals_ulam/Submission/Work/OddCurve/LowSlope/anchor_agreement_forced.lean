import Mathlib
import Submission.Work.OddCurve.LowSlope.anchor_close_thousand
import Submission.Work.OddVolterra.Existence.window_solution_three
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball

/-!
# Agreement of two transition-window anchors

Both moment equations of the odd case, imposed on the slopes `1 - 3τ < s ≤ 1`, determine the
chord-endpoint curve `(x,y)` uniquely.  The proof goes through the paper's Volterra system
`(hah44)`: `Work.OddCurve.LowSlope.act_anchor_volterra` turns the two moment equations into a
solution of that system on `(1-3τ, 1)`, and
`Work.OddVolterra.Window.eqOn_of_solves_win` gives uniqueness of solutions of the system on that
window.  The single remaining slope `s = 1` is covered by the tail condition of
`Work.OddEnvelope.IsEnvelopeCurve`.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 1600000

/-- The two `profileX` constants of the workspace agree. -/
lemma profileX_ulam_eq_envelope :
    Commons.Geometry.Ulam.profileX = Work.OddEnvelope.profileX := by
  funext s; rfl

/-- The state curve `(x, y, x', y')` of an envelope curve is continuous on `[b, 1]` for `b > 0`. -/
lemma stateOf_continuousOn_Icc {h x y : ℝ → ℝ} (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    {b : ℝ} (hb : 0 < b) :
    ContinuousOn (Work.OddVolterra.stateOf x y) (Set.Icc b 1) := by
  have hm : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ ∞ g (Set.Ioi (0 : ℝ)) →
      ContinuousOn g (Set.Icc b 1) :=
    fun hg => hg.continuousOn.mono (fun t ht => by rw [Set.mem_Ioi]; linarith [ht.1])
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · simpa [Work.OddVolterra.stateOf] using hm H.smooth_x
  · simpa [Work.OddVolterra.stateOf] using hm H.smooth_y
  · simpa [Work.OddVolterra.stateOf] using
      hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x)
  · simpa [Work.OddVolterra.stateOf] using
      hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y)

/-- On `[b,1]` (`b > 0`) the state of a curve that is `C²`-close to the semicircle's stays in the
`1/2`-ball of the base state. -/
lemma stateOf_close_baseState {x y : ℝ → ℝ}
    (hcx : CloseToProfileX x) (hcy : CloseToProfileX y) {b : ℝ} (hb : 0 < b) :
    ∀ s ∈ Set.Icc b 1, ‖Work.OddVolterra.stateOf x y s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le hb hs.1
  obtain ⟨hx1, hx2, -⟩ := hcx s hs0
  obtain ⟨hy1, hy2, -⟩ := hcy s hs0
  have h1 : |x s - Work.OddEnvelope.profileX s| ≤ 1 / 2 := le_trans hx1 (by norm_num)
  have h2 : |y s - Work.OddEnvelope.profileX s| ≤ 1 / 2 := le_trans hy1 (by norm_num)
  have h3 : |deriv x s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 2 :=
    le_trans hx2 (by norm_num)
  have h4 : |deriv y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 2 :=
    le_trans hy2 (by norm_num)
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i
  · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
      profileX_ulam_eq_envelope] using h1
  · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
      profileX_ulam_eq_envelope] using h2
  · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
      profileX_ulam_eq_envelope] using h3
  · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
      profileX_ulam_eq_envelope] using h4

theorem anchor_agreement_forced (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} {h X Y x y : ℝ → ℝ}
    (hε : ε ≤ 1 / 100)
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h)
    (HX : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (Hx : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hcX : Work.OddCurve.LowSlope.CloseToProfileX X)
    (hcY : Work.OddCurve.LowSlope.CloseToProfileX Y)
    (hcx : Work.OddCurve.LowSlope.CloseToProfileX x)
    (hcy : Work.OddCurve.LowSlope.CloseToProfileX y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hxA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hxB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) :
    ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 → x s = X s ∧ y s = Y s := by
  have hτ7 : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by
    norm_num [Work.OddVolterra.tau]
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hb.1
  have hsuppI : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
    fun t ht => ⟨(hb.2.1 ht).1.le, (hb.2.1 ht).2.le⟩
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hb.2.2.1 k (by omega) s) hε
  -- the Volterra data on the window `[7/10, 1]`
  obtain ⟨L, hL, C, hC, hLip, hBd, hCont⟩ :=
    Work.OddVolterra.Existence.theta_lipschitz_state_ball n hn hh hsuppI hsmall2
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hInj⟩ :=
    Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsuppI hsmall2
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  -- both curves solve the paper's system on the window
  have hvolX : Work.OddVolterra.VolterraEqOn n h X Y
      (Set.Ioo (1 - 3 * Work.OddVolterra.tau) 1) :=
    act_anchor_volterra n hn hb HX hcX hcY hA hB
  have hvolx : Work.OddVolterra.VolterraEqOn n h x y
      (Set.Ioo (1 - 3 * Work.OddVolterra.tau) 1) :=
    act_anchor_volterra n hn hb Hx hcx hcy hxA hxB
  have hZe : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s) =
        (∫ σ in s..(1 : ℝ),
          Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) +
          Work.OddVolterra.Xi n h s :=
    fun s hs => hvolX s (by rw [hτ7]; exact hs)
  have hWe : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf x y s) =
        (∫ σ in s..(1 : ℝ),
          Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf x y σ)) +
          Work.OddVolterra.Xi n h s :=
    fun s hs => hvolx s (by rw [hτ7]; exact hs)
  have hZc : ContinuousOn (Work.OddVolterra.stateOf X Y) (Set.Icc (7 / 10 : ℝ) 1) :=
    stateOf_continuousOn_Icc HX (by norm_num)
  have hWc : ContinuousOn (Work.OddVolterra.stateOf x y) (Set.Icc (7 / 10 : ℝ) 1) :=
    stateOf_continuousOn_Icc Hx (by norm_num)
  have hZb : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      ‖Work.OddVolterra.stateOf X Y s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 :=
    stateOf_close_baseState hcX hcY (by norm_num)
  have hWb : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      ‖Work.OddVolterra.stateOf x y s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 :=
    stateOf_close_baseState hcx hcy (by norm_num)
  -- uniqueness of the Volterra system
  have heq : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1,
      Work.OddVolterra.stateOf X Y s = Work.OddVolterra.stateOf x y s :=
    Work.OddVolterra.Window.eqOn_of_solves_win (n := n) (h := h) (b := (7 / 10 : ℝ))
      hL hc (by norm_num) (by norm_num) hLip hBd hCont hInj hZc hWc hZe hWe hZb hWb
  intro s hs1 hs2
  have hs1' : (7 / 10 : ℝ) < s := by rw [← hτ7]; exact hs1
  rcases lt_or_eq_of_le hs2 with hs2' | hs2'
  · have h := heq s ⟨hs1', hs2'⟩
    have h0 : X s = x s := by
      have := congrFun h 0
      simpa [Work.OddVolterra.stateOf] using this
    have h1 : Y s = y s := by
      have := congrFun h 1
      simpa [Work.OddVolterra.stateOf] using this
    exact ⟨h0.symm, h1.symm⟩
  · subst hs2'
    have hX1 : X 1 = Work.OddEnvelope.profileX 1 :=
      HX.x_tail 1 (by norm_num [Work.OddEnvelope.tau])
    have hY1 : Y 1 = Work.OddEnvelope.profileX 1 :=
      HX.y_tail 1 (by norm_num [Work.OddEnvelope.tau])
    have hx1 : x 1 = Work.OddEnvelope.profileX 1 :=
      Hx.x_tail 1 (by norm_num [Work.OddEnvelope.tau])
    have hy1 : y 1 = Work.OddEnvelope.profileX 1 :=
      Hx.y_tail 1 (by norm_num [Work.OddEnvelope.tau])
    exact ⟨by rw [hx1, hX1], by rw [hy1, hY1]⟩

end

end Work.OddCurve.LowSlope
