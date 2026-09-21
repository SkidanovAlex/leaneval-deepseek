import Mathlib
import Submission.Work.OddCurveB.Step2.DerivWide
import Submission.Work.OddCurveB.Step2.Extension
import Submission.Work.OddVolterra.WinData.window_state_continuous
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.Existence.curve_data_three_defs

/-!
# Step 2: the state-level window solution, via the wide derivative-closeness core

This file proves `Work.OddVolterra.Existence.WindowSolutionThree n` — the state-level output of
Ryabogin's Step 2 (the Volterra construction on the transition window) — **unconditionally**, by
combining

* the engine's state solution `Work.OddVolterra.WinData.window_state_continuous` (which supplies a
  state solving the paper's system on `(1/4,1)`, `1/2000`-close to the ball state, with the right
  tail and row identities),
* this chapter's wide derivative-closeness core `Work.OddCurveB.Step2.w_window_deriv_close_core`
  (the `C¹`-closeness of an arbitrary solution, on the wide window `(1/4, 9/10)`),
* the globally smooth Seeley/Borel extension `Work.OddCurveB.Step2.w_extension` (global smoothness
  is what makes the endpoint `s = 1/4` accessible by a right-hand limit).

The structure follows `Work.OddVolterra.Existence.window_C1_state` / `window_solution_three`
(the sibling chapter's assembly), with the two changes above: the smoothness of the state is
recorded globally, and the derivative-closeness is taken from the wide core.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Elementary facts about the ball profile -/

lemma baseState_zero (s : ℝ) : baseState s 0 = Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_one (s : ℝ) : baseState s 1 = Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_two (s : ℝ) : baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := rfl
lemma baseState_three (s : ℝ) : baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := rfl

/-- The ball profile stays above `7/10` on the slope interval `[1/4, 9/10]`. -/
lemma profileX_ge_seven_tenths {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (9 / 10)) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have hsq : s ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by nlinarith [hs.1, hs.2]
  rw [show Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) from rfl,
    le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  have h1 : Real.sqrt (1 + s ^ 2) ≤ 10 / 7 := by
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((10 / 7 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 10 / 7 := Real.sqrt_sq (by norm_num)
  nlinarith [h1]

/-- The profile's slope is at most `-1/10` on `[1/4, 9/10]`. -/
lemma deriv_profileX_le_neg_tenth {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (9 / 10)) :
    deriv Commons.Geometry.Ulam.profileX s ≤ -(1 / 10 : ℝ) := by
  have hp := profileX_ge_seven_tenths hs
  rw [Commons.Geometry.Ulam.deriv_profileX_eq]
  have hspos : (0 : ℝ) < s / (1 + s ^ 2) := by
    apply div_pos (by linarith [hs.1]); positivity
  have hle : (4 / 17 : ℝ) ≤ s / (1 + s ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.1] : (0 : ℝ) ≤ s - 1 / 4)
      (by linarith [hs.2] : s - 4 ≤ 0)]
  have h1 : (4 / 17 : ℝ) * (7 / 10) ≤ s / (1 + s ^ 2) * Commons.Geometry.Ulam.profileX s :=
    mul_le_mul hle hp (by norm_num) (le_of_lt hspos)
  have h2 : (4 / 17 : ℝ) * (7 / 10) = 14 / 85 := by norm_num
  linarith [h1, h2]

/-- The profile's slope is negative on the positive half-line. -/
lemma deriv_profileX_neg {s : ℝ} (hs : 0 < s) : deriv Commons.Geometry.Ulam.profileX s < 0 := by
  rw [Commons.Geometry.Ulam.deriv_profileX_eq]
  have h1 : 0 < s / (1 + s ^ 2) := div_pos hs (by positivity)
  have h2 : 0 < Commons.Geometry.Ulam.profileX s := by
    rw [show Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) from rfl]
    exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))
  nlinarith

lemma contDiff_baseState :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX.iterate_deriv 1
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX.iterate_deriv 1


/-! ## The `1/2000`-close state with the right tail -/

/-- **The state-level window solution.**  There is `ε > 0` such that every `C^{n+3}` bump of size
`ε` supported in the transition window, flat near the left edge of the window and non-zero, admits
a *globally* `C^∞` state `Z` which solves the paper's system on `(1/4,1)`, agrees with the ball
state beyond `9/10`, is `1/2000`-close to the ball state together with its derivative, satisfies the
two row identities and has the sign pattern. -/

theorem w_window_C1_state (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ, Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
      h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContDiff ℝ (⊤ : ℕ∞) Z ∧
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) + Xi n h s) ∧
        (∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Z s = baseState s) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          dist (Z s) (baseState s) ≤ 1 / 2000 ∧
          dist (deriv Z s) (deriv (baseState : ℝ → St) s) ≤ 1 / 2000) ∧
        (∀ s : ℝ, 1 / 4 ≤ s →
          deriv (fun u : ℝ => Z u 0) s = Z s 2 ∧ deriv (fun u : ℝ => Z u 1) s = Z s 3) ∧
        (∀ s : ℝ, 1 / 4 ≤ s → 0 < Z s 0 ∧ 0 < Z s 1 ∧ Z s 2 < 0 ∧ Z s 3 < 0) := by
  have hL1 : WinData.ThetaMCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ) :=
    WinData.thetaM_close_box n hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hL4 : WinData.FderivGoddCloseBox n (1 / 4 : ℝ) (19 / 20 : ℝ) (1 / 2 : ℝ) :=
    WinData.fderiv_godd_close_box n hn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  obtain ⟨K, ε₁, hKpos, hε₁pos, hε₁100, hC1⟩ := w_window_deriv_close_core n hn
  set r : ℝ := min (min (1 / 2000) (1 / (2000 * (K + 1)))) ε₁ with hrdef
  have hrpos : 0 < r := lt_min (lt_min (by norm_num) (by positivity)) hε₁pos
  have hr2000 : r ≤ 1 / 2000 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hrK : r ≤ 1 / (2000 * (K + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hrε₁ : r ≤ ε₁ := min_le_right _ _
  have hr100 : r ≤ 1 / 100 := le_trans hrε₁ hε₁100
  have hKr : K * r ≤ 1 / 2000 := by
    have h1 : K * r ≤ K * (1 / (2000 * (K + 1))) := mul_le_mul_of_nonneg_left hrK hKpos.le
    have h2 : K * (1 / (2000 * (K + 1))) ≤ 1 / 2000 := by
      have h4 : (0 : ℝ) < 2000 * (K + 1) := by positivity
      have he : K * (1 / (2000 * (K + 1))) = K / (2000 * (K + 1)) := by ring
      rw [he, div_le_iff₀ h4]
      linarith
    linarith
  obtain ⟨εc, hεcpos, Hc⟩ := WinData.window_state_continuous n hn hL1 hL4 r hrpos
  set ε : ℝ := min εc r with hεdef
  have hεpos : 0 < ε := lt_min hεcpos hrpos
  have hεεc : ε ≤ εc := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro h hbump h0 hne
  obtain ⟨hh, hsupp, hjet, hflat⟩ := hbump
  have hsuppI : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
    fun x hx => ⟨(hsupp hx).1.le, (hsupp hx).2.le⟩
  have hε100 : ε ≤ 1 / 100 := le_trans hεr hr100
  have hsmallC : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ εc :=
    fun k hk s => le_trans (hjet k (by omega) s) hεεc
  have hsmall100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hε100
  obtain ⟨Z, hZc, hZeq, hZtail, hZd, hZder⟩ := Hc h hh hsuppI hflat hsmallC h0 hne
  have hZc' : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    hZc.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  have hZd' : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ),
      dist (Z s) (baseState s) ≤ 1 / 2 := fun s hs =>
    le_trans (hZd s ⟨hs.1, le_trans hs.2 (by norm_num)⟩) (le_trans hr2000 (by norm_num))
  have hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :=
    WinData.smooth_upgrade n hn h hh hsuppI hflat hsmall100 Z hZc' hZeq hZtail hZd'
  have hZtail910 : ∀ s : ℝ, 9 / 10 ≤ s → Z s = baseState s := by
    have h : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
    intro s hs
    exact hZtail s (by linarith)
  have h914 : (9 / 10 : ℝ) ≤ 1 - Work.OddVolterra.tau := by
    have h : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
    linarith
  obtain ⟨Zf, hZfc, hZfeq, hZfder⟩ :=
    w_extension hZsm hZtail910
      (fun s hs => (hZder s hs.le).1) (fun s hs => (hZder s hs.le).2)
  have hZfsm : ContDiffOn ℝ (⊤ : ℕ∞) Zf (Set.Ioi (0 : ℝ)) := hZfc.contDiffOn
  have hsys : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Godd n h s (Zf s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zf σ)) + Xi n h s := by
    intro s hs
    have hs14 : (1 / 4 : ℝ) ≤ s := le_of_lt hs.1
    rw [hZfeq s hs14, hZeq s hs]
    congr 1
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hs.2.le] at hσ
    rw [hZfeq σ (le_trans hs14 hσ.1)]
  have htail' : ∀ s : ℝ, 1 - Work.OddVolterra.tau ≤ s → Zf s = baseState s := by
    intro s hs
    rw [hZfeq s (by linarith [h914, hs]), hZtail s hs]
  have hbump' : Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h := ⟨hh, hsupp, hjet, hflat⟩
  have htail9 : ∀ s : ℝ, 9 / 10 ≤ s → Zf s = baseState s := by
    have h : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
    intro s hs
    exact htail' s (by linarith)
  -- the ball hypothesis on the whole window `[1/4, 1]`, as the wide core asks
  have hZb : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1, dist (Zf s) (baseState s) ≤ 1 / 2 := by
    intro s hs
    rcases le_or_gt s (19 / 20 : ℝ) with hle | hgt
    · rw [hZfeq s hs.1]
      exact hZd' s ⟨hs.1, hle⟩
    · have h910 : (9 / 10 : ℝ) ≤ s := by linarith
      rw [hZfeq s hs.1, hZtail910 s h910, dist_self]
      norm_num
  have hZfcont : ContinuousOn Zf (Set.Icc (1 / 4 : ℝ) 1) := hZfc.continuous.continuousOn
  have hKr' : K * ε ≤ 1 / 2000 := by
    have h3 : K * ε ≤ K * r := mul_le_mul_of_nonneg_left hεr hKpos.le
    linarith
  have hDcore : ∀ u ∈ Set.Ioo (1 / 4 : ℝ) (9 / 10 : ℝ),
      dist (deriv Zf u) (deriv (baseState : ℝ → St) u) ≤ K * ε :=
    fun u hu => hC1 h Zf ε hεpos (le_trans hεr hrε₁) hbump'
      (hZfsm.mono (Set.Ioi_subset_Ioi (by norm_num))) hZfcont hsys htail9 hZb u hu
  -- continuity of the two functions of which we take the right-hand limit at `1/4`
  have hcdZ : Continuous (deriv Zf) := by
    have h1 : Continuous (fun x : ℝ => fderiv ℝ Zf x) := hZfc.continuous_fderiv (by simp)
    have h2 : Continuous (fun x : ℝ => (fderiv ℝ Zf x) (1 : ℝ)) := h1.clm_apply continuous_const
    have hfun : deriv Zf = fun x : ℝ => (fderiv ℝ Zf x) (1 : ℝ) := rfl
    rw [hfun]; exact h2
  have hcb : ContDiff ℝ (⊤ : ℕ∞) (baseState : ℝ → St) := contDiff_baseState
  have hcdB : Continuous (deriv (baseState : ℝ → St)) := hcb.continuous_deriv (by simp)
  refine ⟨Zf, hZfc, hsys, htail', ?_, hZfder, ?_⟩
  · -- the two closeness bounds
    intro s hs
    refine ⟨?_, ?_⟩
    · -- the state
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · rw [hZfeq s hs]
        exact le_trans (hZd s ⟨hs, by linarith⟩) hr2000
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), dist_self]
        norm_num
    · -- the derivative
      rcases eq_or_lt_of_le hs with h0s | hpos
      · -- `s = 1/4`: right-hand limit along the open window `(1/4, 9/10)`
        subst h0s
        haveI : (𝓝[Set.Ioo (1 / 4 : ℝ) (9 / 10)] (1 / 4)).NeBot :=
          left_nhdsWithin_Ioo_neBot (by norm_num)
        have hF : Tendsto (fun u : ℝ => dist (deriv Zf u) (deriv (baseState : ℝ → St) u))
            (𝓝[Set.Ioo (1 / 4 : ℝ) (9 / 10)] (1 / 4))
            (𝓝 (dist (deriv Zf (1 / 4)) (deriv (baseState : ℝ → St) (1 / 4)))) :=
          ((hcdZ.continuousAt).tendsto.dist (hcdB.continuousAt).tendsto).mono_left
            nhdsWithin_le_nhds
        refine le_of_tendsto hF ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact le_trans (hDcore u hu) hKr'
      · rcases lt_trichotomy s (9 / 10 : ℝ) with hlt9 | h9 | hgt9
        · exact le_trans (hDcore s ⟨hpos, hlt9⟩) hKr'
        · -- `s = 9/10`: left-hand limit, using the global continuity of `deriv Zf`
          subst h9
          haveI : (𝓝[Set.Ioo (1 / 4 : ℝ) (9 / 10)] (9 / 10)).NeBot :=
            right_nhdsWithin_Ioo_neBot (by norm_num)
          have hF : Tendsto (fun u : ℝ => dist (deriv Zf u) (deriv (baseState : ℝ → St) u))
              (𝓝[Set.Ioo (1 / 4 : ℝ) (9 / 10)] (9 / 10))
              (𝓝 (dist (deriv Zf (9 / 10)) (deriv (baseState : ℝ → St) (9 / 10)))) :=
            ((hcdZ.continuousAt).tendsto.dist (hcdB.continuousAt).tendsto).mono_left
              nhdsWithin_le_nhds
          refine le_of_tendsto hF ?_
          filter_upwards [self_mem_nhdsWithin] with u hu
          exact le_trans (hDcore u hu) hKr'
        · -- `s > 9/10`: `Zf` agrees with `baseState` on a neighbourhood of `s`
          have hev : Zf =ᶠ[𝓝 s] (baseState : ℝ → St) := by
            filter_upwards [isOpen_Ioi.mem_nhds hgt9] with u hu
            have hu' : (9 / 10 : ℝ) < u := hu
            rw [hZfeq u (by linarith), hZtail910 u (le_of_lt hu')]
          rw [Filter.EventuallyEq.deriv_eq hev, dist_self]
          norm_num
  · -- the sign pattern
    intro s hs
    have hcomp : ∀ i : Fin 4, dist (Zf s i) (baseState s i) ≤ 1 / 2000 := by
      intro i
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := le_trans (hZd s ⟨hs, by linarith⟩) hr2000
        rw [dist_eq_norm] at h
        have hb := norm_le_pi_norm (Z s - baseState s) i
        rw [Pi.sub_apply] at hb
        have h1 : Zf s i - baseState s i = (Z s - baseState s) i := by
          rw [hZfeq s hs]; rfl
        rw [Real.dist_eq, h1, ← Real.norm_eq_abs]
        exact le_trans hb h
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), dist_self]
        norm_num
    have hget : ∀ i : Fin 4, |Zf s i - baseState s i| ≤ 1 / 2000 := by
      intro i
      have h := hcomp i
      rwa [Real.dist_eq] at h
    have h0pos : (0 : ℝ) < Zf s 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 0)).1
        have hp := profileX_ge_seven_tenths ⟨hs, hle⟩
        rw [baseState_zero s] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_zero s]
        exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))
    have h1pos : (0 : ℝ) < Zf s 1 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 1)).1
        have hp := profileX_ge_seven_tenths ⟨hs, hle⟩
        rw [baseState_one s] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_one s]
        exact div_pos one_pos (Real.sqrt_pos.mpr (by positivity))
    have h2neg : Zf s 2 < 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 2)).2
        have hd := deriv_profileX_le_neg_tenth ⟨hs, hle⟩
        rw [baseState_two s] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_two s]
        exact deriv_profileX_neg (by linarith)
    have h3neg : Zf s 3 < 0 := by
      rcases le_or_gt s (9 / 10 : ℝ) with hle | hgt
      · have h := (abs_le.mp (hget 3)).2
        have hd := deriv_profileX_le_neg_tenth ⟨hs, hle⟩
        rw [baseState_three s] at h
        linarith
      · rw [hZfeq s hs, hZtail910 s (le_of_lt hgt), baseState_three s]
        exact deriv_profileX_neg (by linarith)
    exact ⟨h0pos, h1pos, h2neg, h3neg⟩

/-- The `i`-th coordinate of `deriv Z s` is the derivative of the `i`-th coordinate function. -/
lemma deriv_apply_coord {Z : ℝ → Work.OddVolterra.St} {s : ℝ} (hZ : DifferentiableAt ℝ Z s)
    (i : Fin 4) : deriv Z s i = deriv (fun u : ℝ => Z u i) s := by
  have h := fderiv_apply (𝕜 := ℝ) hZ i
  simp only [deriv]
  rw [h]
  rfl

lemma differentiableAt_baseState (s : ℝ) :
    DifferentiableAt ℝ (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s :=
  (contDiff_baseState.differentiable (by simp)).differentiableAt

lemma deriv_baseState_two (s : ℝ) :
    deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 2 =
      deriv (deriv Commons.Geometry.Ulam.profileX) s := by
  rw [deriv_apply_coord (differentiableAt_baseState s) 2]
  rfl

lemma deriv_baseState_three (s : ℝ) :
    deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 3 =
      deriv (deriv Commons.Geometry.Ulam.profileX) s := by
  rw [deriv_apply_coord (differentiableAt_baseState s) 3]
  rfl

/-- **The transition-window half of the odd construction (Ryabogin's Step 2).**  This is the
project's `Prop` `Work.OddVolterra.Existence.WindowSolutionThree`, proved here from
`w_window_C1_state` by converting the two `dist`-bounds into the six componentwise `1/1000`
bounds (using that the components `2, 3` of the state are the derivatives of the components
`0, 1`). -/
theorem w_windowSolutionThree (n : ℕ) (hn : 1 ≤ n) :
    Work.OddVolterra.Existence.WindowSolutionThree n := by
  obtain ⟨ε, hε, H⟩ := w_window_C1_state n hn
  refine ⟨ε, hε, ?_⟩
  intro h hb h0 hne
  obtain ⟨Z, hZfc, hsys, htail, hclose, hder, hsign⟩ := H h hb h0 hne
  refine ⟨Z, hZfc.contDiffOn, hsys, htail, ?_, hder, hsign⟩
  intro s hs
  obtain ⟨hcd, hdd⟩ := hclose s hs
  have hZs : DifferentiableAt ℝ Z s := (hZfc.differentiable (by simp)).differentiableAt
  have hbd : ∀ i : Fin 4, |Z s i - Work.OddVolterra.baseState s i| ≤ 1 / 1000 := by
    intro i
    have h1 : ‖(Z s - Work.OddVolterra.baseState s) i‖ ≤
        ‖Z s - Work.OddVolterra.baseState s‖ := norm_le_pi_norm _ i
    have h3 : (Z s - Work.OddVolterra.baseState s) i =
        Z s i - Work.OddVolterra.baseState s i := rfl
    rw [h3, Real.norm_eq_abs] at h1
    have h2 : ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2000 := by
      simpa [dist_eq_norm] using hcd
    linarith
  have hbd2 : ∀ i : Fin 4,
      |deriv Z s i - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s i|
        ≤ 1 / 1000 := by
    intro i
    have h1 : ‖(deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) i‖
        ≤ ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖ :=
      norm_le_pi_norm _ i
    have h3 : (deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) i =
        deriv Z s i - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s i := rfl
    rw [h3, Real.norm_eq_abs] at h1
    have h2 : ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖
        ≤ 1 / 2000 := by simpa [dist_eq_norm] using hdd
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hbd 0
    rw [baseState_zero s] at h
    linarith
  · have h := hbd 2
    rw [baseState_two s] at h
    linarith
  · rw [← deriv_apply_coord hZs 2, ← deriv_baseState_two s]
    exact hbd2 2
  · have h := hbd 1
    rw [baseState_one s] at h
    linarith
  · have h := hbd 3
    rw [baseState_three s] at h
    linarith
  · rw [← deriv_apply_coord hZs 3, ← deriv_baseState_three s]
    exact hbd2 3


end

end Work.OddCurveB.Step2
