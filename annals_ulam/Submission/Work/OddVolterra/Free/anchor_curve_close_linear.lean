import Mathlib
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddCurve.LowSlope.Extension
import Submission.Work.OddCurve.LowSlope.anchor_close_thousand
import Submission.Work.OddVolterra.Existence.window_state_linear_close
import Submission.Work.OddCurveB.Step2.WindowC1
import Submission.Work.OddCurve.LowSlope.anchor_agreement_forced
import Submission.Work.OddCurveB.Est.dist_fderiv_Godd_le

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

set_option maxHeartbeats 3000000

/-- Componentwise bound by the sup-norm on the state space `St = Fin 4 → ℝ`. -/
lemma anchor_free_abs_le_norm (v w : Work.OddVolterra.St) (i : Fin 4) :
    |v i - w i| ≤ ‖v - w‖ := by
  have h := norm_le_pi_norm (v - w) i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at h

/-- A bound known on `(7/10, 1)` for a function continuous on `[7/10, 1]` extends to the closed
interval. -/
lemma anchor_free_le_on_Icc_of_le_on_Ioo {f : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousOn f (Set.Icc (7 / 10 : ℝ) 1))
    (h : ∀ s ∈ Set.Ioo (7 / 10 : ℝ) 1, f s ≤ c) :
    ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, f s ≤ c := by
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

/-- **The anchor's curve is `C · ε`-close to the semicircle in `C²` on `[1-3τ,1]`.**

The `ε`-linear version of `Work.OddCurve.LowSlope.anchor_close_thousand`.  For `ε` below the
Step-2 threshold the rigidity (`Work.OddVolterra.Window.eqOn_of_solves_win`) identifies the
anchor with the window solution of Ryabogin's Step 2 (`WindowSolutionThree`, whose state is
`1/1000`-close to the ball state together with its derivative), and
`Work.OddVolterra.Existence.window_state_linear_close` upgrades that to the `ε`-linear estimate.
For `ε` above the threshold the absolute `1/100`-closeness coming from `CloseToProfileX` already
dominates `C · ε`. -/
theorem anchor_curve_close_linear (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ} {h X Y : ℝ → ℝ},
      Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
      h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau ≤ s → s ≤ 1 →
        |X s - Work.OddEnvelope.profileX s| ≤ C * ε ∧
        |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ C * ε ∧
        |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ C * ε ∧
        |Y s - Work.OddEnvelope.profileX s| ≤ C * ε ∧
        |deriv Y s - deriv Work.OddEnvelope.profileX s| ≤ C * ε ∧
        |deriv (deriv Y) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ C * ε := by
  obtain ⟨Cl, hClpos, hLin⟩ := Work.OddVolterra.Existence.window_state_linear_close n hn
  obtain ⟨ε₃, hε₃pos, H₃⟩ := Work.OddCurveB.Step2.w_windowSolutionThree n hn
  set εs : ℝ := min ε₃ (1 / 100) with hεsdef
  have hεspos : 0 < εs := lt_min hε₃pos (by norm_num)
  have hεs3 : εs ≤ ε₃ := min_le_left _ _
  have hεs100 : εs ≤ 1 / 100 := min_le_right _ _
  set C : ℝ := max (max Cl 1) (1 / (100 * εs)) + 1 with hCdef
  have hCge1 : (1 : ℝ) ≤ C := by
    have hmax : (1 : ℝ) ≤ max (max Cl 1) (1 / (100 * εs)) :=
      le_trans (le_max_right Cl 1) (le_max_left _ _)
    rw [hCdef]; linarith
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hCge1
  have hCgeCl : Cl ≤ C := by
    have hmax : Cl ≤ max (max Cl 1) (1 / (100 * εs)) :=
      le_trans (le_max_left Cl 1) (le_max_left _ _)
    rw [hCdef]; linarith
  have hCd : 1 / (100 * εs) ≤ C := by
    have hmax : 1 / (100 * εs) ≤ max (max Cl 1) (1 / (100 * εs)) := le_max_right _ _
    rw [hCdef]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro ε h X Y hb hne H hcX hcY hA hB s hs1 hs2
  have hτ7 : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by
    norm_num [Work.OddVolterra.tau]
  have hs0 : 0 < s := by
    have h : (7 / 10 : ℝ) ≤ s := by rw [← hτ7]; exact hs1
    linarith
  by_cases hεle : ε ≤ εs
  · -- the small-`ε` regime: the rigidity identifies the anchor with the Step-2 state
    have hεpos : 0 < ε := Work.OddVolterra.Existence.bump_eps_pos hb hne
    have hh : ContDiff ℝ (⊤ : ℕ∞) h := hb.1
    have h0 : h 0 = 0 := by
      by_contra hc
      have hx := hb.2.1 (Function.mem_support.mpr hc)
      rw [Set.mem_Ioo] at hx
      have h1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
        norm_num [Work.OddVolterra.tau]
      rw [h1] at hx
      norm_num at hx
    have hsuppI : Function.support h ⊆
        Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
      fun x hx => ⟨(hb.2.1 hx).1.le, (hb.2.1 hx).2.le⟩
    have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
      fun k hk s => le_trans (hb.2.2.1 k (by omega) s) (le_trans hεle hεs100)
    -- the window solution of Step 2 at level `ε`
    obtain ⟨Z, hZsm, hZsys, hZtail, hZclose, hZder, _hZsign⟩ :=
      H₃ h (hb.mono (le_trans hεle hεs3)) h0 hne
    have hZdiffAt : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ Z t := fun t ht =>
      (hZsm.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds ht)
    have hZnorm : ∀ t : ℝ, 1 / 4 ≤ t →
        ‖Z t - Work.OddVolterra.baseState t‖ ≤ 1 / 1000 ∧
        ‖deriv Z t - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t‖
          ≤ 1 / 1000 := by
      intro t ht
      have ht0 : 0 < t := by linarith
      obtain ⟨a0, a2, a22, a1, a3, a33⟩ := hZclose t ht
      have hst : ∀ i : Fin 4, |Z t i - Work.OddVolterra.baseState t i| ≤ 1 / 1000 := by
        intro i
        fin_cases i
        · simpa [Work.OddVolterra.baseState] using a0
        · simpa [Work.OddVolterra.baseState] using a1
        · simpa [Work.OddVolterra.baseState] using a2
        · simpa [Work.OddVolterra.baseState] using a3
      have hder : ∀ i : Fin 4,
          |deriv Z t i - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t i|
            ≤ 1 / 1000 := by
        intro i
        fin_cases i
        · have key : |deriv Z t 0
              - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 0| ≤ 1 / 1000 := by
            have h1 : deriv Z t 0 = deriv (fun u : ℝ => Z u 0) t :=
              Work.OddCurve.LowSlope.act_deriv_apply_coord_local (hZdiffAt t ht0) 0
            have h2 : deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 0
                = deriv Commons.Geometry.Ulam.profileX t := by
              rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
                (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 0]
              rfl
            rw [h1, h2, (hZder t ht).1]
            exact a2
          exact key
        · have key : |deriv Z t 1
              - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 1| ≤ 1 / 1000 := by
            have h1 : deriv Z t 1 = deriv (fun u : ℝ => Z u 1) t :=
              Work.OddCurve.LowSlope.act_deriv_apply_coord_local (hZdiffAt t ht0) 1
            have h2 : deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 1
                = deriv Commons.Geometry.Ulam.profileX t := by
              rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
                (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 1]
              rfl
            rw [h1, h2, (hZder t ht).2]
            exact a3
          exact key
        · have key : |deriv Z t 2
              - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 2| ≤ 1 / 1000 := by
            have h1 : deriv Z t 2 = deriv (fun u : ℝ => Z u 2) t :=
              Work.OddCurve.LowSlope.act_deriv_apply_coord_local (hZdiffAt t ht0) 2
            have h2 : deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 2
                = deriv (deriv Commons.Geometry.Ulam.profileX) t := by
              rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
                (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 2]
              rfl
            rw [h1, h2]
            exact a22
          exact key
        · have key : |deriv Z t 3
              - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 3| ≤ 1 / 1000 := by
            have h1 : deriv Z t 3 = deriv (fun u : ℝ => Z u 3) t :=
              Work.OddCurve.LowSlope.act_deriv_apply_coord_local (hZdiffAt t ht0) 3
            have h2 : deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 3
                = deriv (deriv Commons.Geometry.Ulam.profileX) t := by
              rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
                (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 3]
              rfl
            rw [h1, h2]
            exact a33
          exact key
      refine ⟨?_, ?_⟩
      · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
        intro i
        rw [Pi.sub_apply, Real.norm_eq_abs]
        exact hst i
      · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
        intro i
        rw [Pi.sub_apply, Real.norm_eq_abs]
        exact hder i
    have hlinZ := hLin hb h0 hne hZsm hZsys hZtail hZnorm
    -- uniqueness of the Volterra system on the window
    obtain ⟨L, hL, Cc, hCc, hLipC, hBdC, hContC⟩ :=
      Work.OddVolterra.Existence.theta_lipschitz_state_ball n hn hh hsuppI hsmall2
        (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
    obtain ⟨c, hc, hInj⟩ :=
      Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsuppI hsmall2
        (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
    have hvol := Work.OddCurve.LowSlope.act_anchor_volterra n hn hb H hcX hcY hA hB
    have hZc : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) :=
      hZsm.continuousOn.mono (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
    have hWc : ContinuousOn (Work.OddVolterra.stateOf X Y) (Set.Icc (7 / 10 : ℝ) 1) :=
      Work.OddCurve.LowSlope.stateOf_continuousOn_Icc H (by norm_num)
    have hZb : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        ‖Z t - Work.OddVolterra.baseState t‖ ≤ 1 / 2 :=
      fun t ht => le_trans (hZnorm t (by linarith [ht.1])).1 (by norm_num)
    have hWb : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        ‖Work.OddVolterra.stateOf X Y t - Work.OddVolterra.baseState t‖ ≤ 1 / 2 :=
      Work.OddCurve.LowSlope.stateOf_close_baseState hcX hcY (by norm_num)
    have heq : ∀ t ∈ Set.Ioo (7 / 10 : ℝ) 1, Z t = Work.OddVolterra.stateOf X Y t :=
      Work.OddVolterra.Window.eqOn_of_solves_win (n := n) (h := h) (b := (7 / 10 : ℝ))
        hL hc (by norm_num) (by norm_num) hLipC hBdC hContC hInj hZc hWc
        (fun t ht => hZsys t ⟨by linarith [ht.1], ht.2⟩)
        (fun t ht => hvol t (by rw [hτ7]; exact ht))
        hZb hWb
    -- the six bounds on the open interval
    have hkey : ∀ t ∈ Set.Ioo (7 / 10 : ℝ) 1,
        |X t - Work.OddEnvelope.profileX t| ≤ Cl * ε ∧
        |deriv X t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε ∧
        |deriv (deriv X) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε ∧
        |Y t - Work.OddEnvelope.profileX t| ≤ Cl * ε ∧
        |deriv Y t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε ∧
        |deriv (deriv Y) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε := by
      intro t ht
      obtain ⟨hn1, hn2⟩ := hlinZ t ⟨by linarith [ht.1], ht.2.le⟩
      have ht0 : 0 < t := by linarith [ht.1]
      have hZs : Z t = Work.OddVolterra.stateOf X Y t := heq t ht
      have hZdt : DifferentiableAt ℝ Z t := hZdiffAt t ht0
      have e2 : deriv (deriv Work.OddEnvelope.profileX) t
          = deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 2 := by
        rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
          (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 2]
        rfl
      have e3 : deriv (deriv Work.OddEnvelope.profileX) t
          = deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t 3 := by
        rw [Work.OddCurve.LowSlope.act_deriv_apply_coord_local
          (Work.OddCurve.LowSlope.act_differentiableAt_baseState t) 3]
        rfl
      have c0 : |X t - Work.OddEnvelope.profileX t| ≤ Cl * ε := by
        have h := anchor_free_abs_le_norm (Z t) (Work.OddVolterra.baseState t) 0
        have h' : |(Z t) 0 - (Work.OddVolterra.baseState t) 0| ≤ Cl * ε := le_trans h hn1
        rw [hZs] at h'
        simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState,
          Work.OddCurve.LowSlope.profileX_ulam_eq_envelope] using h'
      have c1 : |Y t - Work.OddEnvelope.profileX t| ≤ Cl * ε := by
        have h := anchor_free_abs_le_norm (Z t) (Work.OddVolterra.baseState t) 1
        have h' : |(Z t) 1 - (Work.OddVolterra.baseState t) 1| ≤ Cl * ε := le_trans h hn1
        rw [hZs] at h'
        simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState,
          Work.OddCurve.LowSlope.profileX_ulam_eq_envelope] using h'
      have c2 : |deriv X t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε := by
        have h := anchor_free_abs_le_norm (Z t) (Work.OddVolterra.baseState t) 2
        have h' : |(Z t) 2 - (Work.OddVolterra.baseState t) 2| ≤ Cl * ε := le_trans h hn1
        rw [hZs] at h'
        simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState,
          Work.OddCurve.LowSlope.profileX_ulam_eq_envelope] using h'
      have c3 : |deriv Y t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε := by
        have h := anchor_free_abs_le_norm (Z t) (Work.OddVolterra.baseState t) 3
        have h' : |(Z t) 3 - (Work.OddVolterra.baseState t) 3| ≤ Cl * ε := le_trans h hn1
        rw [hZs] at h'
        simpa [Work.OddVolterra.stateOf, Work.OddVolterra.baseState,
          Work.OddCurve.LowSlope.profileX_ulam_eq_envelope] using h'
      have c22 : |deriv (deriv X) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε := by
        have hevDX : deriv X =ᶠ[𝓝 t] (fun u : ℝ => Z u 2) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
          have hu14 : (1 / 4 : ℝ) ≤ u := by linarith [hu.1]
          have hXu : X =ᶠ[𝓝 u] (fun v : ℝ => Z v 0) := by
            filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
            rw [heq v hv]
            rfl
          rw [hXu.deriv_eq, (hZder u hu14).1]
        have e1 : deriv (deriv X) t = deriv Z t 2 := by
          rw [hevDX.deriv_eq,
            (Work.OddCurve.LowSlope.act_deriv_apply_coord_local hZdt 2).symm]
        rw [e1, e2]
        exact le_trans (anchor_free_abs_le_norm (deriv Z t)
          (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t) 2) hn2
      have c33 : |deriv (deriv Y) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε := by
        have hevDY : deriv Y =ᶠ[𝓝 t] (fun u : ℝ => Z u 3) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
          have hu14 : (1 / 4 : ℝ) ≤ u := by linarith [hu.1]
          have hYu : Y =ᶠ[𝓝 u] (fun v : ℝ => Z v 1) := by
            filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
            rw [heq v hv]
            rfl
          rw [hYu.deriv_eq, (hZder u hu14).2]
        have e1 : deriv (deriv Y) t = deriv Z t 3 := by
          rw [hevDY.deriv_eq,
            (Work.OddCurve.LowSlope.act_deriv_apply_coord_local hZdt 3).symm]
        rw [e1, e3]
        exact le_trans (anchor_free_abs_le_norm (deriv Z t)
          (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) t) 3) hn2
      exact ⟨c0, c2, c22, c1, c3, c33⟩
    -- extend to the closed interval by continuity
    have hprofCont : ContinuousOn Work.OddEnvelope.profileX (Set.Icc (7 / 10 : ℝ) 1) :=
      (Work.OddCurveB.Est.contDiff_profileX_est.continuous).continuousOn
    have hdprofCont : ContinuousOn (deriv Work.OddEnvelope.profileX) (Set.Icc (7 / 10 : ℝ) 1) :=
      (Work.OddCurveB.Est.contDiff_profileX_est.continuous_deriv (by simp)).continuousOn
    have hd2profCont :
        ContinuousOn (deriv (deriv Work.OddEnvelope.profileX)) (Set.Icc (7 / 10 : ℝ) 1) :=
      (((contDiff_infty_iff_deriv.mp Work.OddCurveB.Est.contDiff_profileX_est).2).continuous_deriv
        (by simp)).continuousOn
    have hm : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi (0 : ℝ)) →
        ContinuousOn g (Set.Icc (7 / 10 : ℝ) 1) :=
      fun hg => hg.continuousOn.mono (fun x hx => by rw [Set.mem_Ioi]; linarith [hx.1])
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
    have hb1 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |X t - Work.OddEnvelope.profileX t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo (f := fun t => |X t - Work.OddEnvelope.profileX t|)
        (c := Cl * ε) (hXcont.sub hprofCont).abs (fun t ht => (hkey t ht).1)
    have hb2 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |deriv X t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo
        (f := fun t => |deriv X t - deriv Work.OddEnvelope.profileX t|)
        (c := Cl * ε) (hderXcont.sub hdprofCont).abs (fun t ht => (hkey t ht).2.1)
    have hb3 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |deriv (deriv X) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo
        (f := fun t => |deriv (deriv X) t - deriv (deriv Work.OddEnvelope.profileX) t|)
        (c := Cl * ε) (hddXcont.sub hd2profCont).abs (fun t ht => (hkey t ht).2.2.1)
    have hb4 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |Y t - Work.OddEnvelope.profileX t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo (f := fun t => |Y t - Work.OddEnvelope.profileX t|)
        (c := Cl * ε) (hYcont.sub hprofCont).abs (fun t ht => (hkey t ht).2.2.2.1)
    have hb5 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |deriv Y t - deriv Work.OddEnvelope.profileX t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo
        (f := fun t => |deriv Y t - deriv Work.OddEnvelope.profileX t|)
        (c := Cl * ε) (hderYcont.sub hdprofCont).abs (fun t ht => (hkey t ht).2.2.2.2.1)
    have hb6 : ∀ t ∈ Set.Icc (7 / 10 : ℝ) 1,
        |deriv (deriv Y) t - deriv (deriv Work.OddEnvelope.profileX) t| ≤ Cl * ε :=
      anchor_free_le_on_Icc_of_le_on_Ioo
        (f := fun t => |deriv (deriv Y) t - deriv (deriv Work.OddEnvelope.profileX) t|)
        (c := Cl * ε) (hddYcont.sub hd2profCont).abs (fun t ht => (hkey t ht).2.2.2.2.2)
    have hs1' : (7 / 10 : ℝ) ≤ s := by rw [← hτ7]; exact hs1
    have hClC : Cl * ε ≤ C * ε := mul_le_mul_of_nonneg_right hCgeCl hεpos.le
    exact ⟨le_trans (hb1 s ⟨hs1', hs2⟩) hClC, le_trans (hb2 s ⟨hs1', hs2⟩) hClC,
      le_trans (hb3 s ⟨hs1', hs2⟩) hClC, le_trans (hb4 s ⟨hs1', hs2⟩) hClC,
      le_trans (hb5 s ⟨hs1', hs2⟩) hClC, le_trans (hb6 s ⟨hs1', hs2⟩) hClC⟩
  · -- the large-`ε` regime: the absolute `1/100`-closeness already dominates `C * ε`
    push_neg at hεle
    have hden : (0 : ℝ) < 100 * εs := by linarith [hεspos]
    have hpos : (0 : ℝ) < 1 / (100 * εs) := one_div_pos.mpr hden
    have h4 : (1 : ℝ) / (100 * εs) * εs = 1 / 100 := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff hden.ne' (by norm_num)]
      ring
    have hCε : (1 : ℝ) / 100 ≤ C * ε := by
      have h2 : (1 : ℝ) / (100 * εs) * εs ≤ (1 : ℝ) / (100 * εs) * ε :=
        mul_le_mul_of_nonneg_left hεle.le (le_of_lt hpos)
      have h3 : (1 : ℝ) / (100 * εs) * ε ≤ C * ε :=
        mul_le_mul_of_nonneg_right hCd (by linarith [hεspos, hεle])
      linarith [h4, h2, h3]
    exact ⟨le_trans (hcX s hs0).1 hCε, le_trans (hcX s hs0).2.1 hCε,
      le_trans (hcX s hs0).2.2 hCε, le_trans (hcY s hs0).1 hCε,
      le_trans (hcY s hs0).2.1 hCε, le_trans (hcY s hs0).2.2 hCε⟩

end

end Work.OddVolterra.Free
