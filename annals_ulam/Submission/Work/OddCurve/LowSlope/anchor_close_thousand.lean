import Mathlib
import Submission.Work.OddCurve.LowSlope.volterraRowsOn
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.WinData.window_state_continuous
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.WinData.contDiffOn_Ioi_extension
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.WinData.fderiv_godd_close_box
import Submission.Work.OddVolterra.Window.volterra_unique
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddVolterra.Existence.odd_linearization
import Submission.Work.OddCurveB.Est.dist_fderiv_Godd_le
import Submission.Work.OddVolterra.Existence.window_deriv_close_core

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 1600000

/-- A smooth solution of the paper's system on `(1/4,1)`, equal to the ball state past `9/10`,
`1/2000`-close to it, with the two derivative rows. -/
theorem act_window_setup (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) ∧
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) ∧
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) ∧
        (∀ s : ℝ, s ∈ Set.Icc (1 / 4 : ℝ) 1 →
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2000) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) := by
  have hL1 : Work.OddVolterra.WinData.ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ) :=
    Work.OddVolterra.WinData.thetaM_close_box n hn (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hL4 : Work.OddVolterra.WinData.FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ) :=
    Work.OddVolterra.WinData.fderiv_godd_close_box n hn (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  obtain ⟨εs, hεs, Hs⟩ :=
    Work.OddVolterra.WinData.window_state_continuous n hn hL1 hL4 (1 / 2000) (by norm_num)
  refine ⟨min εs (1 / 100), lt_min hεs (by norm_num), ?_⟩
  intro h hbump hne
  have hbumpW : Work.OddVolterra.Existence.IsSmallFlatBumpThree n εs h :=
    hbump.mono (min_le_left _ _)
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hbump.1
  have hsupp : Function.support h ⊆ Set.Ioo (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau) := hbump.2.1
  have hsuppI : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau) := fun x hx => ⟨(hsupp hx).1.le, (hsupp hx).2.le⟩
  have hflat := hbump.2.2.2
  have hjet := hbump.2.2.1
  have h0 : h 0 = 0 := by
    by_contra hc
    have hx := hsupp (Function.mem_support.mpr hc)
    rw [Set.mem_Ioo] at hx
    have h1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
      norm_num [Work.OddVolterra.tau]
    rw [h1] at hx
    norm_num at hx
  have hsmall100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) (min_le_right _ _)
  have hjetW : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εs :=
    fun k hk s => hbumpW.2.2.1 k (by omega) s
  obtain ⟨Z, hZc, hZeq, hZtail, hZd, hZder⟩ := Hs h hh hsuppI hflat hjetW h0 hne
  have hZc' : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    hZc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  have hZd' : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2 := fun s hs =>
    le_trans (hZd s ⟨hs.1, by linarith [hs.2]⟩) (by norm_num)
  have hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    Work.OddVolterra.WinData.smooth_upgrade n hn h hh hsuppI hflat hsmall100 Z hZc' hZeq hZtail hZd'
  have hZtail910 : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s :=
    fun s hs => hZtail s (by rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; exact hs)
  have h914 : (9 / 10 : ℝ) ≤ 1 - Work.OddVolterra.tau := by
    rw [Work.OddVolterra.Smooth.one_sub_tau_eq]
  obtain ⟨Zf, hZfsm, hZfeq, hZfder⟩ :=
    Work.OddVolterra.WinData.contDiffOn_Ioi_extension hZsm hZtail910
      (fun s hs => (hZder s (le_of_lt hs)).1) (fun s hs => (hZder s (le_of_lt hs)).2)
  refine ⟨Zf, hZfsm.mono (fun x hx => by
      rw [Set.mem_Ioi] at hx ⊢; linarith), ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs14 : (1 / 4 : ℝ) ≤ s := le_of_lt hs.1
    rw [hZfeq s hs14, hZeq s hs]
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hs.2.le] at hσ
    rw [hZfeq σ (le_trans hs14 hσ.1)]
  · intro s hs
    rw [hZfeq s (by linarith [h914, hs]), hZtail910 s hs]
  · intro s hs
    rw [hZfeq s hs.1]; exact hZd s hs
  · intro s hs
    exact hZfder s hs

/-- `deriv` of a `Fin 4`-valued function is the componentwise derivative. -/
lemma act_deriv_apply_coord_local {Z : ℝ → Work.OddVolterra.St} {s : ℝ}
    (hZ : DifferentiableAt ℝ Z s) (i : Fin 4) :
    deriv Z s i = deriv (fun u : ℝ => Z u i) s := by
  have h := fderiv_apply (𝕜 := ℝ) hZ i
  simp only [deriv]
  rw [h]
  rfl

/-- The ball state is differentiable. -/
lemma act_differentiableAt_baseState (s : ℝ) :
    DifferentiableAt ℝ (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s := by
  have hprof : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX :=
    Work.OddCurveB.Est.contDiff_profileX_est
  have hd : DifferentiableAt ℝ Commons.Geometry.Ulam.profileX s :=
    (hprof.differentiable (by simp)).differentiableAt
  have hderiv : DifferentiableAt ℝ (deriv Commons.Geometry.Ulam.profileX) s :=
    (((contDiff_infty_iff_deriv.mp hprof).2).differentiable (by simp)).differentiableAt
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    · first
      | exact hd
      | exact hderiv

lemma act_le_on_Icc_of_le_on_Ioo {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (7 / 10 : ℝ) 1))
    (h : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1, f s ≤ 1 / 1000) :
    ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, f s ≤ 1 / 1000 := by
  intro s hs
  have hs_cl : s ∈ closure (Set.Ioo (7 / 10 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (7 / 10 : ℝ) ≠ 1)]
    exact hs
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp hs_cl
  have hutI : Tendsto u atTop (𝓝[Set.Icc (7 / 10 : ℝ) 1] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hut, Filter.Eventually.of_forall (fun n => Set.Ioo_subset_Icc_self (hu n))⟩
  have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f s)) :=
    (hf.continuousWithinAt hs).tendsto.comp hutI
  exact le_of_tendsto hfu (Filter.Eventually.of_forall (fun n => h (u n) (hu n)))

/-- On the transition window the anchor's state solves the paper's system. -/
theorem act_anchor_volterra (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} {h X Y : ℝ → ℝ}
    (hb : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hcX : CloseToProfileX X) (hcY : CloseToProfileX Y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    Work.OddVolterra.VolterraEqOn n h X Y (Set.Ioo (1 - 3 * Work.OddVolterra.tau) 1) := by
  intro s hs
  have hτ : (0:ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hs0 : 0 < s := lt_of_lt_of_le hτ hs.1.le
  have hs1 : s < 1 := hs.2
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hb.1
  have hclose : ∀ s : ℝ, 0 < s →
      |X s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv X s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv X) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 ∧
      |Y s - Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv Y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 100 ∧
      |deriv (deriv Y) s - deriv (deriv Commons.Geometry.Ulam.profileX) s| ≤ 1 / 100 := by
    intro t ht
    obtain ⟨a1, a2, a3⟩ := hcX t ht
    obtain ⟨b1, b2, b3⟩ := hcY t ht
    exact ⟨a1, a2, a3, b1, b2, b3⟩
  have hmeF : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddVolterra.momentF n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Commons.Geometry.Ulam.oddSemicircleMomentConstant n / Real.sqrt (1 + s ^ 2) := by
    intro t ht1 ht2
    have h := hA t ht1 ht2
    simpa [Work.OddCurve.momentA, Work.OddVolterra.momentF, Work.OddVolterra.momentIntegrand,
      Work.OddCurve.rad, Work.OddVolterra.psi, Work.OddVolterra.line, Work.OddCurve.refConst,
      Commons.Geometry.Ulam.oddSemicircleMomentConstant,
      Commons.Geometry.Ulam.oddSemicircleMomentIntegrand] using h
  have hmeH : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddVolterra.momentH n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0 := by
    intro t ht1 ht2
    have h := hB t ht1 ht2
    simpa [Work.OddCurve.momentB, Work.OddVolterra.momentH, Work.OddVolterra.centroidIntegrand,
      Work.OddCurve.rad, Work.OddVolterra.psi, Work.OddVolterra.lineSlope,
      Work.OddVolterra.line] using h
  have hrows := volterraRowsOn n hn hh hτ (by norm_num [Work.OddVolterra.tau]) H hmeF hmeH
    hclose s hs
  have hint := theta_integrable_close n hn hh H hclose s ⟨hs0, hs1⟩
  have hFTCX : (∫ σ in s..1, deriv X σ) = X 1 - X s := by
    have hcont : ContinuousOn X (Set.Icc s 1) :=
      H.smooth_x.continuousOn.mono (fun x hx => by
        rw [Set.mem_Ioi]
        have h1 : s <= x := by simpa [min_eq_left hs1.le] using hx.1
        linarith)
    have hderiv : ∀ x ∈ Set.Ioo s 1, HasDerivAt X (deriv X x) x := by
      intro x hx
      have hx0 : x ∈ Set.Ioi (0:ℝ) := by rw [Set.mem_Ioi]; linarith [hx.1, hs0]
      have hd : DifferentiableAt ℝ X x :=
        (H.smooth_x.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx0)
      simpa only [deriv] using hd.hasDerivAt
    have hint' : IntervalIntegrable (deriv X) volume s 1 :=
      ((Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x).continuousOn.mono
        (fun x hx => by
          rw [Set.mem_Ioi]
          have h1 : s <= x := by simpa [min_eq_left hs1.le] using hx.1
          linarith)).intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs1.le hcont hderiv hint'
  have hFTCY : (∫ σ in s..1, deriv Y σ) = Y 1 - Y s := by
    have hcont : ContinuousOn Y (Set.Icc s 1) :=
      H.smooth_y.continuousOn.mono (fun x hx => by
        rw [Set.mem_Ioi]
        have h1 : s <= x := by simpa [min_eq_left hs1.le] using hx.1
        linarith)
    have hderiv : ∀ x ∈ Set.Ioo s 1, HasDerivAt Y (deriv Y x) x := by
      intro x hx
      have hx0 : x ∈ Set.Ioi (0:ℝ) := by rw [Set.mem_Ioi]; linarith [hx.1, hs0]
      have hd : DifferentiableAt ℝ Y x :=
        (H.smooth_y.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hx0)
      simpa only [deriv] using hd.hasDerivAt
    have hint' : IntervalIntegrable (deriv Y) volume s 1 :=
      ((Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y).continuousOn.mono
        (fun x hx => by
          rw [Set.mem_Ioi]
          have h1 : s <= x := by simpa [min_eq_left hs1.le] using hx.1
          linarith)).intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs1.le hcont hderiv hint'
  have hX1 : X 1 = Commons.Geometry.Ulam.profileX 1 := by
    simpa [Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX,
      Work.OddEnvelope.tau, Work.OddVolterra.tau]
      using H.x_tail 1 (by norm_num [Work.OddEnvelope.tau])
  have hY1 : Y 1 = Commons.Geometry.Ulam.profileX 1 := by
    simpa [Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX,
      Work.OddEnvelope.tau, Work.OddVolterra.tau]
      using H.y_tail 1 (by norm_num [Work.OddEnvelope.tau])
  have hGodd0 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s)) 0 = X s := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hGodd1 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s)) 1 = Y s := by
    simp [Work.OddVolterra.Godd, Work.OddVolterra.stateOf]
  have hTheta0 : ∀ σ : ℝ,
      (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) 0 = - deriv X σ := by
    intro σ; simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  have hTheta1 : ∀ σ : ℝ,
      (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) 1 = - deriv Y σ := by
    intro σ; simp [Work.OddVolterra.Theta, Work.OddVolterra.stateOf]
  have hXi0 : (Work.OddVolterra.Xi n h s) 0 = X 1 := by
    simp only [Work.OddVolterra.Xi, Matrix.cons_val_zero]
    rw [hX1]
  have hXi1 : (Work.OddVolterra.Xi n h s) 1 = Y 1 := by
    simp only [Work.OddVolterra.Xi, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hY1]
  have hI0 : (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) 0
      = -(X 1 - X s) := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 0) (h := hint)]
    rw [intervalIntegral.integral_congr (fun σ _ => hTheta0 σ), intervalIntegral.integral_neg,
      hFTCX]
  have hI1 : (∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) 1
      = -(Y 1 - Y s) := by
    rw [Work.OddBridge.intervalIntegral_apply_fin4 (i := 1) (h := hint)]
    rw [intervalIntegral.integral_congr (fun σ _ => hTheta1 σ), intervalIntegral.integral_neg,
      hFTCY]
  have h0 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s)) 0
      = ((∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) +
          Work.OddVolterra.Xi n h s) 0 := by
    rw [Pi.add_apply, hGodd0, hI0, hXi0]
    ring
  have h1 : (Work.OddVolterra.Godd n h s (Work.OddVolterra.stateOf X Y s)) 1
      = ((∫ σ in s..1, Work.OddVolterra.Theta n h s σ (Work.OddVolterra.stateOf X Y σ)) +
          Work.OddVolterra.Xi n h s) 1 := by
    rw [Pi.add_apply, hGodd1, hI1, hXi1]
    ring
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact hrows.1
  · exact hrows.2

/-- **The anchor's curve is `1/1000`-close to the semicircle in `C²` on `[1-3τ,1]`.** -/
theorem anchor_close_thousand (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h X Y : ℝ → ℝ,
      Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h → h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau ≤ s → s ≤ 1 →
        |X s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
        |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
        |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 ∧
        |Y s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
        |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
        |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 := by
  obtain ⟨Cw, εw, hCw, hεw, hεw100, hWclose⟩ := Work.OddVolterra.Existence.window_deriv_close_core n hn
  obtain ⟨εc, hεc, Hc⟩ := act_window_setup n hn
  have hden : (0 : ℝ) < 2000 * (Cw + 1) := by positivity
  set ε₀ : ℝ := min (min εc εw) (min (1 / 100) (1 / (2000 * (Cw + 1)))) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (lt_min hεc hεw) (lt_min (by norm_num) (by positivity))
  have hε₀c : ε₀ ≤ εc := by
    rw [hε₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₀w : ε₀ ≤ εw := by
    rw [hε₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₀100 : ε₀ ≤ 1 / 100 := by
    rw [hε₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀rec : ε₀ ≤ 1 / (2000 * (Cw + 1)) := by
    rw [hε₀def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hCwε : Cw * ε₀ ≤ 1 / 2000 := by
    have h1 : Cw * ε₀ ≤ Cw * (1 / (2000 * (Cw + 1))) :=
      mul_le_mul_of_nonneg_left hε₀rec hCw.le
    have h2 : Cw * (1 / (2000 * (Cw + 1))) ≤ 1 / 2000 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith
    linarith
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro h X Y hb hne H hcX hcY hA hB
  have hτ : (0 : ℝ) < 1 - 3 * Work.OddVolterra.tau := by norm_num [Work.OddVolterra.tau]
  have hτ7 : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by norm_num [Work.OddVolterra.tau]
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hb.1
  have hsuppI : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
    fun x hx => ⟨(hb.2.1 hx).1.le, (hb.2.1 hx).2.le⟩
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hb.2.2.1 k (by omega) s) hε₀100
  -- the window solution
  obtain ⟨Z, hZsm, hZeq, hZtail, hZd, hZder⟩ := Hc h (hb.mono hε₀c) hne
  -- the anchor's system
  have hvol := act_anchor_volterra n hn hb H hcX hcY hA hB
  -- uniqueness
  obtain ⟨L, hL, C1, hC1, hLip, hBd, hCont⟩ :=
    Work.OddVolterra.Existence.theta_lipschitz_state_ball n hn hh hsuppI hsmall2
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hInj⟩ :=
    Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsuppI hsmall2
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  have hZc : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) :=
    hZsm.continuousOn.mono (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
  have hdXc : ContinuousOn (deriv X) (Set.Icc (7 / 10 : ℝ) 1) :=
    (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x).continuousOn.mono
      (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
  have hdYc : ContinuousOn (deriv Y) (Set.Icc (7 / 10 : ℝ) 1) :=
    (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y).continuousOn.mono
      (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
  have hWc : ContinuousOn (Work.OddVolterra.stateOf X Y) (Set.Icc (7 / 10 : ℝ) 1) := by
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · simpa [Work.OddVolterra.stateOf] using
        H.smooth_x.continuousOn.mono (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
    · simpa [Work.OddVolterra.stateOf] using
        H.smooth_y.continuousOn.mono (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
    · simpa [Work.OddVolterra.stateOf] using hdXc
    · simpa [Work.OddVolterra.stateOf] using hdYc
  have hZb : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 := by
    intro s hs
    rw [← dist_eq_norm]
    exact le_trans (hZd s ⟨by linarith [hs.1], hs.2⟩) (by norm_num)
  have hWb : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      ‖Work.OddVolterra.stateOf X Y s - Work.OddVolterra.baseState s‖ ≤ 1 / 2 := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    obtain ⟨hX1, hX2, -⟩ := hcX s hs0
    obtain ⟨hY1, hY2, -⟩ := hcY s hs0
    have h1 : |X s - Work.OddEnvelope.profileX s| ≤ 1 / 2 := le_trans hX1 (by norm_num)
    have h2 : |Y s - Work.OddEnvelope.profileX s| ≤ 1 / 2 := le_trans hY1 (by norm_num)
    have h3 : |deriv X s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 2 :=
      le_trans hX2 (by norm_num)
    have h4 : |deriv Y s - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 2 :=
      le_trans hY2 (by norm_num)
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i
    · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
        Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX] using h1
    · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
        Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX] using h2
    · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
        Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX] using h3
    · simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState, Real.norm_eq_abs,
        Work.OddEnvelope.profileX, Commons.Geometry.Ulam.profileX] using h4
  have heq : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1,
      Z s = Work.OddVolterra.stateOf X Y s :=
    Work.OddVolterra.Window.eqOn_of_solves_win (n := n) (h := h) hL hc
      (by norm_num) (by norm_num) hLip hBd hCont hInj hZc hWc
      (fun s hs => hZeq s ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs => hvol s ⟨by linarith [hs.1], hs.2⟩)
      hZb hWb
  -- the six bounds on the open interval
  have hkey : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1,
      |X s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
      |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
      |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 ∧
      |Y s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
      |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 ∧
      |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 := by
    intro s hs
    have hs14 : (1 / 4 : ℝ) ≤ s := by linarith [hs.1]
    have hs0 : 0 < s := by linarith [hs.1]
    have hZs : Z s = Work.OddVolterra.stateOf X Y s := heq s hs
    have hZdiff : DifferentiableAt ℝ Z s :=
      (hZsm.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds (by linarith [hs.1] : (1 / 4 : ℝ) < s))
    have hdist : dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2000 :=
      hZd s ⟨hs14, by linarith [hs.2]⟩
    have hbase2 : (Work.OddVolterra.baseState s) 2 = deriv Commons.Geometry.Ulam.profileX s := by
      simp [Work.OddVolterra.baseState]
    have hbase3 : (Work.OddVolterra.baseState s) 3 = deriv Commons.Geometry.Ulam.profileX s := by
      simp [Work.OddVolterra.baseState]
    have hcoord : ∀ i : Fin 4,
        |(Z s) i - (Work.OddVolterra.baseState s) i| ≤ 1 / 2000 := by
      intro i
      have h5 := norm_le_pi_norm (Z s - Work.OddVolterra.baseState s) i
      rw [dist_eq_norm] at hdist
      simpa [Pi.sub_apply, Real.norm_eq_abs] using le_trans h5 hdist
    have hZ0 : X s = Z s 0 := by
      rw [hZs]; rfl
    have hZ1 : Y s = Z s 1 := by
      rw [hZs]; rfl
    have hZ2 : deriv X s = Z s 2 := by
      rw [hZs]; rfl
    have hZ3 : deriv Y s = Z s 3 := by
      rw [hZs]; rfl
    -- the second derivatives
    have hevX : X =ᶠ[𝓝 s] (fun u => Z u 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      rw [heq u hu]; rfl
    have hevY : Y =ᶠ[𝓝 s] (fun u => Z u 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      rw [heq u hu]; rfl
    have hevDX : deriv X =ᶠ[𝓝 s] (fun u => Z u 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      have hu14 : (1 / 4 : ℝ) ≤ u := by linarith [hu.1]
      have hXu : X =ᶠ[𝓝 u] (fun v => Z v 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
        rw [heq v hv]; rfl
      rw [hXu.deriv_eq, (hZder u hu14).1]
    have hevDY : deriv Y =ᶠ[𝓝 s] (fun u => Z u 3) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      have hu14 : (1 / 4 : ℝ) ≤ u := by linarith [hu.1]
      have hYu : Y =ᶠ[𝓝 u] (fun v => Z v 1) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
        rw [heq v hv]; rfl
      rw [hYu.deriv_eq, (hZder u hu14).2]
    have hddX : |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 := by
      have e1 : deriv (deriv X) s = deriv (fun u => Z u 2) s := hevDX.deriv_eq
      have e2 : deriv (fun u => Z u 2) s = deriv Z s 2 := (act_deriv_apply_coord_local hZdiff 2).symm
      have e3 : deriv (deriv Work.OddEnvelope.profileX) s
          = deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 2 := by
        rw [act_deriv_apply_coord_local (act_differentiableAt_baseState s) 2]
        rfl
      rw [e1, e2, e3]
      have h5 : |deriv Z s 2 - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 2|
          ≤ dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) := by
        rw [dist_eq_norm]
        have h6 := norm_le_pi_norm
          (deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) 2
        simpa [Pi.sub_apply, Real.norm_eq_abs] using h6
      have h7 : dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
          ≤ 1 / 1000 := by
        by_cases hle : s ≤ 9 / 10
        · have h1 := hWclose h Z ε₀ hε₀pos hε₀w hb hZsm hZeq hZtail
            (fun u hu => le_trans (hZd u ⟨by linarith [hu.1], hu.2⟩) (by norm_num)) s
            ⟨le_of_lt hs.1, hle⟩
          linarith [hCwε]
        · have hlt : (9 / 10 : ℝ) < s := not_le.mp hle
          have hevZ : Z =ᶠ[𝓝 s] (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
            filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
            exact hZtail u (le_of_lt hu)
          rw [hevZ.deriv_eq, dist_self]; norm_num
      linarith
    have hddY : |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 := by
      have e1 : deriv (deriv Y) s = deriv (fun u => Z u 3) s := hevDY.deriv_eq
      have e2 : deriv (fun u => Z u 3) s = deriv Z s 3 := (act_deriv_apply_coord_local hZdiff 3).symm
      have e3 : deriv (deriv Work.OddEnvelope.profileX) s
          = deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 3 := by
        rw [act_deriv_apply_coord_local (act_differentiableAt_baseState s) 3]
        rfl
      rw [e1, e2, e3]
      have h5 : |deriv Z s 3 - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 3|
          ≤ dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) := by
        rw [dist_eq_norm]
        have h6 := norm_le_pi_norm
          (deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) 3
        simpa [Pi.sub_apply, Real.norm_eq_abs] using h6
      have h7 : dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
          ≤ 1 / 1000 := by
        by_cases hle : s ≤ 9 / 10
        · have h1 := hWclose h Z ε₀ hε₀pos hε₀w hb hZsm hZeq hZtail
            (fun u hu => le_trans (hZd u ⟨by linarith [hu.1], hu.2⟩) (by norm_num)) s
            ⟨le_of_lt hs.1, hle⟩
          linarith [hCwε]
        · have hlt : (9 / 10 : ℝ) < s := not_le.mp hle
          have hevZ : Z =ᶠ[𝓝 s] (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
            filter_upwards [isOpen_Ioi.mem_nhds hlt] with u hu
            exact hZtail u (le_of_lt hu)
          rw [hevZ.deriv_eq, dist_self]; norm_num
      linarith
    refine ⟨?_, ?_, hddX, ?_, ?_, hddY⟩
    · rw [hZ0]
      have h := hcoord 0
      have e0 : (Work.OddVolterra.baseState s) 0 = Commons.Geometry.Ulam.profileX s := by
        simp [Work.OddVolterra.baseState]
      rw [e0] at h
      exact le_trans h (by norm_num)
    · rw [hZ2]
      have h := hcoord 2
      rw [hbase2] at h
      exact le_trans h (by norm_num)
    · rw [hZ1]
      have h := hcoord 1
      have e1 : (Work.OddVolterra.baseState s) 1 = Commons.Geometry.Ulam.profileX s := by
        simp [Work.OddVolterra.baseState]
      rw [e1] at h
      exact le_trans h (by norm_num)
    · rw [hZ3]
      have h := hcoord 3
      rw [hbase3] at h
      exact le_trans h (by norm_num)
  -- extend to the closed interval by continuity
  have hprofCont : ContinuousOn Work.OddEnvelope.profileX (Set.Icc (7 / 10 : ℝ) 1) :=
    (Work.OddCurveB.Est.contDiff_profileX_est.continuous).continuousOn
  have hdprofCont : ContinuousOn (deriv Work.OddEnvelope.profileX) (Set.Icc (7 / 10 : ℝ) 1) :=
    (Work.OddCurveB.Est.contDiff_profileX_est.continuous_deriv (by simp)).continuousOn
  have hd2profCont : ContinuousOn (deriv (deriv Work.OddEnvelope.profileX)) (Set.Icc (7 / 10 : ℝ) 1) :=
    (((contDiff_infty_iff_deriv.mp Work.OddCurveB.Est.contDiff_profileX_est).2).continuous_deriv
      (by simp)).continuousOn
  have hm : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi (0 : ℝ)) →
      ContinuousOn g (Set.Icc (7 / 10 : ℝ) 1) := by
    intro g hg
    refine hg.continuousOn.mono ?_
    intro x hx
    rw [Set.mem_Ioi]
    linarith [hx.1]
  have hXcont : ContinuousOn X (Set.Icc (7 / 10 : ℝ) 1) := hm H.smooth_x
  have hderXcont : ContinuousOn (deriv X) (Set.Icc (7 / 10 : ℝ) 1) :=
    hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x)
  have hddXcont : ContinuousOn (deriv (deriv X)) (Set.Icc (7 / 10 : ℝ) 1) :=
    hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi
      (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_x))
  have hYcont : ContinuousOn Y (Set.Icc (7 / 10 : ℝ) 1) := hm H.smooth_y
  have hderYcont : ContinuousOn (deriv Y) (Set.Icc (7 / 10 : ℝ) 1) :=
    hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y)
  have hddYcont : ContinuousOn (deriv (deriv Y)) (Set.Icc (7 / 10 : ℝ) 1) :=
    hm (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi
      (Work.OddVolterra.KernelExt.contDiffOn_deriv_Ioi H.smooth_y))
  have h1 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |X s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hXcont.sub hprofCont).abs
      (fun t ht => (hkey t ht).1)
  have h2 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hderXcont.sub hdprofCont).abs
      (fun t ht => (hkey t ht).2.1)
  have h3 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hddXcont.sub hd2profCont).abs
      (fun t ht => (hkey t ht).2.2.1)
  have h4 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |Y s - Work.OddEnvelope.profileX s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hYcont.sub hprofCont).abs
      (fun t ht => (hkey t ht).2.2.2.1)
  have h5 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hderYcont.sub hdprofCont).abs
      (fun t ht => (hkey t ht).2.2.2.2.1)
  have h6 : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 1000 :=
    act_le_on_Icc_of_le_on_Ioo (hddYcont.sub hd2profCont).abs
      (fun t ht => (hkey t ht).2.2.2.2.2)
  intro s hs1 hs2
  have hs1' : (7 / 10 : ℝ) ≤ s := by rw [← hτ7]; exact hs1
  exact ⟨h1 s ⟨hs1', hs2⟩, h2 s ⟨hs1', hs2⟩, h3 s ⟨hs1', hs2⟩,
    h4 s ⟨hs1', hs2⟩, h5 s ⟨hs1', hs2⟩, h6 s ⟨hs1', hs2⟩⟩

end

end Work.OddCurve.LowSlope
