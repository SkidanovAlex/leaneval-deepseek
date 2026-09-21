import Mathlib
import Submission.Work.Anchor.anchor_data
import Submission.Work.Anchor.anchor_final
import Submission.Work.OddVolterra.Window.window_tail_glue
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.glue_local_solutions
import Submission.Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Existence.base_volterra

/-!
# Transferring the windowed solution to the paper's system

`Work.Anchor.engine_solution` produces a curve `Z` on the anchor window `[wl, wr] = [1/2, 19/20]`
solving the *modified* system `Gf n h s (Z s) = ∫ σ in s..wr, Thf n h s σ (Z σ) + Xif n h s`, with
data cut off in the slope and in the state, and with the source corrected by a *frozen tail*.  The
present file converts this information into the paper's data:

* on the window the cut-offs are `1` along `Z` (`‖Z σ - baseState σ‖ ≤ 1/100`), so the manifest
  `Θ` and the paper's `Θ` agree and `Gf`, `Thf` are `Godd`, `Theta`;
* `Xif` is exactly `Xi` plus the frozen tail `∫ σ in wr..1, Θ n h s σ (baseState σ)`
  (`Xif_eq_Xi_add_tail`), which turns the truncated equation into the paper's system with the
  integral running up to `1` and the curve frozen at `baseState` past `wr`;
* uniqueness of the (right-to-left) Volterra equation on `[9/10, 1]`, applied to the curve `Ẑ`
  obtained from `Z` by continuing it with `baseState` past `wr`, forces `Z = baseState` on
  `(9/10, wr]`; the endpoint value `Z wr = baseState wr` -- needed to glue `Ẑ` -- follows from the
  injectivity modulus of `Godd` at `wr` together with the base identity `base_volterra_right`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.Anchor

open Work.OddVolterra

noncomputable section

/-! ## Elementary facts -/

/-- The two coordinates of the ball's state are at least `1/5` in absolute value. -/
lemma one_fifth_le_abs_baseState {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    1 / 5 ≤ |baseState σ 0| ∧ 1 / 5 ≤ |baseState σ 1| := by
  have hpx := seven_tenths_le_profileX hσ0 hσ1
  have hpos : (0 : ℝ) < Commons.Geometry.Ulam.profileX σ := by
    rw [show Commons.Geometry.Ulam.profileX σ = 1 / Real.sqrt (1 + σ ^ 2) from rfl]
    positivity
  constructor
  · have h : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [h, abs_of_pos hpos]; linarith
  · have h : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    rw [h, abs_of_pos hpos]; linarith

/-! ## The manifest data at the states of a curve that is `1/100`-close to the base state -/

lemma ThetaM_eq_Theta_of_close_state (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Icc wl wr) (hsσ : s < σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {z : St} (hz : ‖z - baseState σ‖ ≤ 1 / 100) :
    KernelExt.ThetaM n h s σ z = Theta n h s σ z := by
  have hs0 : 0 < s := by linarith [hs.1, wl_pos]
  have hδpos : (0 : ℝ) < s / 2 := by linarith
  obtain ⟨hz0, hz1⟩ := abs_coord_ge_of_close hσ0 hσ1 hz
  refine Window.ThetaM_eq_Theta n hn hh hsσ hδpos z ?_ ?_ <;> intro a ha
  · have h1 : s / 2 ≤ a := by linarith [ha.1]
    exact Existence.krad_pos_state_region hsupp hsm1 (b := s / 2) (a := a) (σ := σ) (t := -(z 0))
      hδpos h1 ha.2 hσ1 (by rw [abs_neg]; exact hz0)
  · have h1 : s / 2 ≤ a := by linarith [ha.1]
    exact Existence.krad_pos_state_region hsupp hsm1 (b := s / 2) (a := a) (σ := σ) (t := z 1)
      hδpos h1 ha.2 hσ1 hz1

/-! ## Interval integrability of the `𝚯`-integrand -/

/-- **Interval integrability of the `𝚯`-integrand with a free row parameter.**  The row `s` of
`𝚯` is at most the left end `r` of the integration interval, so that the integrand stays in the
region of continuity of `𝚯(s,·,·)`. -/
lemma intervalIntegrable_Theta_row {n : ℕ} {h : ℝ → ℝ} {C : ℝ}
    (hBd : ∀ s' ∈ Set.Icc wl (1 : ℝ), ∀ σ ∈ Set.Ioo s' 1,
      ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2), ‖Theta n h s' σ z‖ ≤ C)
    (hCont : ∀ s' ∈ Set.Icc wl (1 : ℝ),
      ContinuousOn (fun p : ℝ × St => Theta n h s' p.1 p.2)
        {p : ℝ × St | p.1 ∈ Set.Ioo s' 1 ∧
          p.2 ∈ Metric.closedBall (baseState p.1) (1 / 2)})
    {s r r' : ℝ} (hs : s ∈ Set.Icc wl (1 : ℝ)) (hsr : s ≤ r)
    (hrr' : r ≤ r') (hr' : r' ≤ 1)
    {Z : ℝ → St} (hZc : ContinuousOn Z (Set.Icc r r'))
    (hZb : ∀ σ ∈ Set.Icc r r', ‖Z σ - baseState σ‖ ≤ 1 / 2) :
    IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume r r' := by
  have hopen : ContinuousOn (fun σ => Theta n h s σ (Z σ)) (Set.Ioo r r') := by
    refine ContinuousOn.comp (g := fun p : ℝ × St => Theta n h s p.1 p.2)
      (f := fun σ : ℝ => (σ, Z σ)) (hCont s hs) ?_ ?_
    · intro σ hσ
      refine ContinuousWithinAt.prodMk continuousWithinAt_id ?_
      exact (hZc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).continuousWithinAt hσ
    · intro σ hσ
      exact ⟨⟨lt_of_le_of_lt hsr hσ.1, hσ.2.trans_le hr'⟩, hZb σ ⟨hσ.1.le, hσ.2.le⟩⟩
  have hmeas_open : AEStronglyMeasurable (fun σ => Theta n h s σ (Z σ))
      (volume.restrict (Set.Ioo r r')) :=
    hopen.aestronglyMeasurable isOpen_Ioo.measurableSet
  have hset : Set.Ioo r r' =ᵐ[(volume : Measure ℝ)] Set.Ioc r r' := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hempty : Set.Ioo r r' \ Set.Ioc r r' = ∅ := by
        rw [Set.sdiff_eq_empty.mpr]
        intro x hx
        exact ⟨hx.1, hx.2.le⟩
      rw [hempty]
      exact measure_empty
    · refine measure_mono_null (t := ({r'} : Set ℝ)) ?_ (Real.volume_singleton (a := r'))
      intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx1
      exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hx1⟩
  have hmeas : AEStronglyMeasurable (fun σ => Theta n h s σ (Z σ))
      (volume.restrict (Set.Ioc r r')) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact hmeas_open
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Ioc r r')),
      ‖Theta n h s σ (Z σ)‖ ≤ max C 0 := by
    have hbad : (volume : Measure ℝ)
        {σ : ℝ | σ ∈ Set.Ioc r r' ∧ ¬ (‖Theta n h s σ (Z σ)‖ ≤ max C 0)} = 0 := by
      refine measure_mono_null (t := ({r'} : Set ℝ)) ?_ (Real.volume_singleton (a := r'))
      intro σ hσ
      rw [Set.mem_singleton_iff]
      by_contra hσ1
      refine hσ.2 (le_trans (hBd s hs σ
        ⟨lt_of_le_of_lt hsr hσ.1.1, lt_of_lt_of_le (lt_of_le_of_ne hσ.1.2 hσ1) hr'⟩ (Z σ) ?_)
        (le_max_left _ _))
      rw [Metric.mem_closedBall]
      exact hZb σ ⟨hσ.1.1.le, hσ.1.2⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hbad
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact Classical.not_imp.mp hx
  refine intervalIntegrable_iff.mpr ?_
  rw [Set.uIoc_of_le hrr']
  exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas (max C 0) hbound

/-- Interval integrability of the `𝚯`-integrand, the row parameter `s` being at most the left end
of the integration interval. -/
lemma intervalIntegrable_Theta {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s r r' : ℝ} (hs : s ∈ Set.Icc wl (1 : ℝ)) (hsr : s ≤ r)
    (hrr' : r ≤ r') (hr' : r' ≤ 1)
    {Z : ℝ → St} (hZc : ContinuousOn Z (Set.Icc r r'))
    (hZb : ∀ σ ∈ Set.Icc r r', ‖Z σ - baseState σ‖ ≤ 1 / 2) :
    IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume r r' := by
  obtain ⟨L, hL, C, hC, hLip, hBd, hCont⟩ :=
    Existence.theta_lipschitz_state_ball n hn hh hsupp hsm2 (b := wl) wl_pos wl_le_one
  exact intervalIntegrable_Theta_row hBd hCont hs hsr hrr' hr' hZc hZb

/-- Interval integrability of the `𝚯`-integrand along the ball's state. -/
lemma intervalIntegrable_Theta_base {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {r r' : ℝ} (hr : r ∈ Set.Icc wl (1 : ℝ)) (hrr' : r ≤ r') (hr' : r' ≤ 1) :
    IntervalIntegrable (fun σ : ℝ => Theta n h r σ (baseState σ)) volume r r' :=
  intervalIntegrable_Theta hn hh hsupp hsm2 hr le_rfl hrr' hr'
    Window.continuous_baseState.continuousOn (fun σ _ => by rw [sub_self, norm_zero]; norm_num)

lemma intervalIntegrable_Theta_of_continuous {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → St} {r r' : ℝ} (hr : r ∈ Set.Icc wl (1 : ℝ)) (hrr' : r ≤ r') (hr' : r' ≤ 1)
    (hZc : ContinuousOn Z (Set.Icc r r'))
    (hZb : ∀ σ ∈ Set.Icc r r', ‖Z σ - baseState σ‖ ≤ 1 / 2) :
    IntervalIntegrable (fun σ : ℝ => Theta n h r σ (Z σ)) volume r r' :=
  intervalIntegrable_Theta hn hh hsupp hsm2 hr le_rfl hrr' hr' hZc hZb

/-! ## The cut-off factors along a `1/100`-close curve -/

lemma Gf_eq_Godd_of_close {n : ℕ} {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc wl wr) {z : St}
    (hz : ‖z - baseState s‖ ≤ 1 / 5) : Gf n h s z = Godd n h s z := by
  rw [Gf, chiG_eq_one_of_close hs hz, one_smul]

lemma Thf_integral_eq {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → St} (hZdist : ∀ s ∈ Set.Icc wl wr, dist (Z s) (baseState s) ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc wl wr) :
    (∫ σ in s..wr, Thf n h s σ (Z σ)) = ∫ σ in s..wr, Theta n h s σ (Z σ) := by
  refine intervalIntegral.integral_congr_Ioo_of_le hs.2 (fun σ hσ => ?_)
  exact Thf_eq_Theta_of_close (n := n) hn hh hsupp hsm1 hs hσ.1 hσ.2.le
    (by rw [← dist_eq_norm]; exact hZdist σ ⟨le_trans hs.1 hσ.1.le, hσ.2.le⟩)

/-! ## The frozen-tail identity for the modified source -/

/-- On the window the modified source is the paper's source plus the frozen tail. -/
theorem Xif_eq_Xi_add_tail (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Icc wl wr) :
    Xif n h s = Xi n h s + ∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ) := by
  have hcs : (cs : ℝ → ℝ) s = 1 := cs_eq_one_of_mem hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le wl_pos hs.1, lt_of_le_of_lt hs.2 wr_lt_one⟩
  have hwr1 : wr ≤ (1 : ℝ) := wr_lt_one.le
  have hzero_supp : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    simp [Function.support]
  have hzero_sm : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk x
    rw [iteratedDeriv_const_zero]
    norm_num
  -- the cut-off `1` at the base state, for the unperturbed datum
  have hThf0 : (∫ σ in s..wr, Thf n 0 s σ (baseState σ))
      = ∫ σ in s..wr, KernelExt.ThetaM n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hs.2 (fun σ hσ => ?_)
    rw [Thf, chiT_eq_one_of_close hs ⟨le_trans hs.1 hσ.1.le, hσ.2.le⟩
      (by rw [sub_self, norm_zero]; norm_num), one_smul]
  have hTM0 : (∫ σ in s..wr, KernelExt.ThetaM n 0 s σ (baseState σ))
      = ∫ σ in s..wr, Theta n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hs.2 (fun σ hσ => ?_)
    refine ThetaM_eq_Theta_of_close_state n hn (h := (0 : ℝ → ℝ)) contDiff_const hzero_supp
      (fun k hk x => hzero_sm k (le_trans hk (by norm_num)) x) hs hσ.1
      (by linarith [wl_pos, hs.1, hσ.1]) (by linarith [hσ.2, wr_lt_one]) (by simp)
  -- the base identity at `h = 0`, split at `wr`
  have hbase : Godd n 0 s (baseState s) - (∫ σ in s..wr, Theta n 0 s σ (baseState σ))
      = Xi n 0 s + ∫ σ in wr..(1 : ℝ), Theta n 0 s σ (baseState σ) := by
    have hG : Gf n 0 s (baseState s) = Godd n 0 s (baseState s) :=
      Gf_eq_Godd_of_close hs (by rw [sub_self, norm_zero]; norm_num)
    have hbv := Existence.base_volterra n hn s hs01
    have hbv' : Godd n 0 s (baseState s) =
        (∫ σ in s..(1 : ℝ), Theta n 0 s σ (baseState σ)) + Xi n 0 s := hbv
    have hI : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume s 1 :=
      intervalIntegrable_Theta_base (n := n) hn (h := (0 : ℝ → ℝ)) contDiff_const hzero_supp
        hzero_sm ⟨hs.1, le_trans hs.2 wr_lt_one.le⟩ (le_trans hs.2 wr_lt_one.le) le_rfl
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hI.mono_set (by
        rw [Set.uIcc_of_le hs.2, Set.uIcc_of_le (le_trans hs.2 wr_lt_one.le)]
        exact Set.Icc_subset_Icc le_rfl wr_lt_one.le))
      (hI.mono_set (by
        rw [Set.uIcc_of_le hwr1, Set.uIcc_of_le (le_trans hs.2 wr_lt_one.le)]
        exact Set.Icc_subset_Icc hs.2 le_rfl))
    rw [hbv', ← hsplit]
    abel
  -- the tail: the manifest datum agrees with the paper's datum
  have htail : (∫ σ in wr..(1 : ℝ),
        (KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)))
      = (∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ))
        - (∫ σ in wr..(1 : ℝ), Theta n 0 s σ (baseState σ)) := by
    have hIh : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (baseState σ)) volume wr 1 :=
      intervalIntegrable_Theta (n := n) hn hh hsupp hsm2 ⟨hs.1, le_trans hs.2 wr_lt_one.le⟩
        hs.2 hwr1 le_rfl Window.continuous_baseState.continuousOn
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    have hI0 : IntervalIntegrable (fun σ : ℝ => Theta n 0 s σ (baseState σ)) volume wr 1 :=
      intervalIntegrable_Theta (n := n) hn (h := (0 : ℝ → ℝ)) contDiff_const hzero_supp
        hzero_sm ⟨hs.1, le_trans hs.2 wr_lt_one.le⟩ hs.2 hwr1 le_rfl
        Window.continuous_baseState.continuousOn
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    rw [← intervalIntegral.integral_sub hIh hI0]
    refine intervalIntegral.integral_congr_Ioo_of_le hwr1 (fun σ hσ => ?_)
    have hsσ : s < σ := lt_of_le_of_lt hs.2 hσ.1
    have hσ0 : 0 ≤ σ := by linarith [wl_pos, hs.1, hsσ]
    have hσ1 : σ ≤ 1 := le_of_lt hσ.2
    rw [ThetaM_eq_Theta_of_close_state n hn hh hsupp hsm1 hs hsσ hσ0 hσ1 (by simp),
      ThetaM_eq_Theta_of_close_state n hn (h := (0 : ℝ → ℝ)) contDiff_const hzero_supp
        (fun k hk x => hzero_sm k (le_trans hk (by norm_num)) x) hs hsσ hσ0 hσ1 (by simp)]
  -- the manifest datum of the perturbation agrees with the paper's datum
  have hTMh : (∫ σ in wr..(1 : ℝ), KernelExt.ThetaM n h s σ (baseState σ))
      = ∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hwr1 (fun σ hσ => ?_)
    have hsσ : s < σ := lt_of_le_of_lt hs.2 hσ.1
    exact ThetaM_eq_Theta_of_close_state n hn hh hsupp hsm1 hs hsσ
      (by linarith [wl_pos, hs.1, hsσ]) (le_of_lt hσ.2) (by simp)
  rw [Xif, Xibase, hcs, Gf_eq_Godd_of_close hs (by rw [sub_self, norm_zero]; norm_num),
    hThf0, hTM0, hbase, htail]
  simp only [one_smul]
  abel

/-! ## The truncated equation is the paper's equation with the frozen tail -/

theorem sys_transfer (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → St}
    (hZeq : ∀ s ∈ Set.Icc wl wr, Gf n h s (Z s) =
      (∫ σ in s..wr, Thf n h s σ (Z σ)) + Xif n h s)
    (hZdist : ∀ s ∈ Set.Icc wl wr, dist (Z s) (baseState s) ≤ 1 / 100) :
    ∀ s ∈ Set.Icc wl wr, Godd n h s (Z s) =
      (∫ σ in s..wr, Theta n h s σ (Z σ)) +
        (Xi n h s + ∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ)) := by
  intro s hs
  have hc : ‖Z s - baseState s‖ ≤ 1 / 5 := by
    rw [← dist_eq_norm]; linarith [hZdist s hs]
  rw [← Gf_eq_Godd_of_close hs hc, hZeq s hs,
    Thf_integral_eq (n := n) hn hh hsupp hsm1 hZdist hs,
    Xif_eq_Xi_add_tail (n := n) hn hh hsupp hsm1 hsm2 hs]

/-! ## The frozen tail written as a single integral -/

theorem integral_ite_eq (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → St} (hZcont : ContinuousOn Z (Set.Icc wl wr))
    (hZdist : ∀ s ∈ Set.Icc wl wr, dist (Z s) (baseState s) ≤ 1 / 100)
    (hZbase : ∀ s ∈ Set.Icc wl wr, 9 / 10 ≤ s → Z s = baseState s)
    {s : ℝ} (hs : s ∈ Set.Icc wl wr) :
    (∫ σ in s..wr, Theta n h s σ (Z σ)) +
        (∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ))
      = ∫ σ in s..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ) := by
  have hs1 : s ≤ 1 := le_trans hs.2 wr_lt_one.le
  have h9w : (9 : ℝ) / 10 ≤ wr := by norm_num [wr]
  have h91 : (9 : ℝ) / 10 ≤ 1 := by norm_num
  have hwl9 : wl ≤ (9 : ℝ) / 10 := by norm_num [wl]
  rcases le_or_gt s (9 / 10) with h9s | h9s
  · -- the slope lies left of the tail
    have hZc1 : ContinuousOn Z (Set.Icc s (9 / 10)) :=
      hZcont.mono (Set.Icc_subset_Icc hs.1 h9w)
    have hball1 : ∀ σ ∈ Set.Icc s (9 / 10), dist (Z σ) (baseState σ) ≤ 1 / 2 := by
      intro σ hσ
      linarith [hZdist σ ⟨hs.1.trans hσ.1, hσ.2.trans h9w⟩]
    have hAc : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume s (9 / 10) :=
      intervalIntegrable_Theta_of_continuous (n := n) hn hh hsupp hsm2 ⟨hs.1, hs1⟩ h9s h91
        hZc1 (fun σ hσ => by
          rw [← dist_eq_norm]; linarith [hball1 σ hσ])
    have hBc : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (baseState σ)) volume (9 / 10) 1 :=
      intervalIntegrable_Theta (n := n) hn hh hsupp hsm2 ⟨hs.1, hs1⟩ h9s h91 le_rfl
        Window.continuous_baseState.continuousOn
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    have hDc : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume (9 / 10) wr :=
      intervalIntegrable_Theta (n := n) hn hh hsupp hsm2 ⟨hs.1, hs1⟩ h9s h9w wr_lt_one.le
        (hZcont.mono (Set.Icc_subset_Icc hwl9 le_rfl))
        (fun σ hσ => by
          rw [← dist_eq_norm]
          linarith [hZdist σ ⟨hwl9.trans hσ.1, hσ.2⟩])
    have hFc : IntervalIntegrable
        (fun σ : ℝ => Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        volume s (9 / 10) :=
      hAc.congr_uIoo (fun σ hσ => by
        have hσ' : σ ∈ Set.Ioo s (9 / 10) := by rwa [Set.uIoo_of_le h9s] at hσ
        rw [if_pos hσ'.2.le])
    have hFc' : IntervalIntegrable
        (fun σ : ℝ => Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        volume (9 / 10) 1 :=
      hBc.congr_uIoo (fun σ hσ => by
        have hσ' : σ ∈ Set.Ioo (9 / 10) 1 := by rwa [Set.uIoo_of_le h91] at hσ
        rw [if_neg (not_le.mpr hσ'.1)])
    have hsplit : (∫ σ in s..(9 / 10),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ)) +
        (∫ σ in (9 / 10)..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in s..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ) :=
      intervalIntegral.integral_add_adjacent_intervals hFc hFc'
    have hA' : (∫ σ in s..(9 / 10),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in s..(9 / 10), Theta n h s σ (Z σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le h9s] at hσ
      rw [if_pos hσ.2]
    have hB' : (∫ σ in (9 / 10)..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in (9 / 10)..(1 : ℝ), Theta n h s σ (baseState σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le h91] at hσ
      rcases eq_or_lt_of_le hσ.1 with h | h
      · rw [← h, if_pos le_rfl, hZbase (9 / 10) ⟨hwl9, h9w⟩ le_rfl]
      · rw [if_neg (not_le.mpr h)]
    have hsplitB : (∫ σ in (9 / 10)..wr, Theta n h s σ (baseState σ)) +
        (∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ))
        = ∫ σ in (9 / 10)..(1 : ℝ), Theta n h s σ (baseState σ) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hBc.mono_set (by
          rw [Set.uIcc_of_le h9w, Set.uIcc_of_le h91]
          exact Set.Icc_subset_Icc le_rfl wr_lt_one.le))
        (hBc.mono_set (by
          rw [Set.uIcc_of_le wr_lt_one.le, Set.uIcc_of_le h91]
          exact Set.Icc_subset_Icc h9w le_rfl))
    have hmid : (∫ σ in (9 / 10)..wr, Theta n h s σ (baseState σ))
        = ∫ σ in (9 / 10)..wr, Theta n h s σ (Z σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le h9w] at hσ
      rw [hZbase σ ⟨hwl9.trans hσ.1, hσ.2⟩ hσ.1]
    have hsplitZ : (∫ σ in s..(9 / 10), Theta n h s σ (Z σ)) +
        (∫ σ in (9 / 10)..wr, Theta n h s σ (Z σ))
        = ∫ σ in s..wr, Theta n h s σ (Z σ) :=
      intervalIntegral.integral_add_adjacent_intervals hAc hDc
    rw [← hsplit, hA', hB', ← hsplitB, hmid, ← hsplitZ]
    abel
  · -- the slope lies right of the tail
    have hZc1 : ContinuousOn Z (Set.Icc s wr) := hZcont.mono (Set.Icc_subset_Icc hs.1 le_rfl)
    have hAc : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Z σ)) volume s wr :=
      intervalIntegrable_Theta_of_continuous (n := n) hn hh hsupp hsm2 ⟨hs.1, hs1⟩ hs.2
        wr_lt_one.le hZc1 (fun σ hσ => by
          rw [← dist_eq_norm]
          linarith [hZdist σ ⟨hs.1.trans hσ.1, hσ.2⟩])
    have hBc : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (baseState σ)) volume wr 1 :=
      intervalIntegrable_Theta (n := n) hn hh hsupp hsm2 ⟨hs.1, hs1⟩ hs.2 wr_lt_one.le le_rfl
        Window.continuous_baseState.continuousOn
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    have hFc : IntervalIntegrable
        (fun σ : ℝ => Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        volume s wr :=
      hAc.congr_uIoo (fun σ hσ => by
        have hσ' : σ ∈ Set.Ioo s wr := by rwa [Set.uIoo_of_le hs.2] at hσ
        have hbase : Z σ = baseState σ :=
          hZbase σ ⟨hs.1.trans hσ'.1.le, hσ'.2.le⟩ (le_of_lt (lt_trans h9s hσ'.1))
        show Theta n h s σ (Z σ) = Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ)
        rw [if_neg (not_le.mpr (lt_of_lt_of_le h9s hσ'.1.le)), hbase])
    have hFc' : IntervalIntegrable
        (fun σ : ℝ => Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        volume wr 1 :=
      hBc.congr_uIoo (fun σ hσ => by
        have hσ' : σ ∈ Set.Ioo wr 1 := by rwa [Set.uIoo_of_le wr_lt_one.le] at hσ
        rw [if_neg (not_le.mpr (by linarith [h9s, h9w, hσ'.1]))])
    have hsplit : (∫ σ in s..wr,
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ)) +
        (∫ σ in wr..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in s..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ) :=
      intervalIntegral.integral_add_adjacent_intervals hFc hFc'
    have h1 : (∫ σ in s..wr,
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in s..wr, Theta n h s σ (baseState σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le hs.2] at hσ
      rw [if_neg (not_le.mpr (lt_of_lt_of_le h9s hσ.1))]
    have h2 : (∫ σ in wr..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ))
        = ∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le wr_lt_one.le] at hσ
      rw [if_neg (not_le.mpr (by linarith [h9s, hs.2, hσ.1]))]
    have h3 : (∫ σ in s..wr, Theta n h s σ (baseState σ))
        = ∫ σ in s..wr, Theta n h s σ (Z σ) := by
      refine intervalIntegral.integral_congr (fun σ hσ => ?_)
      rw [Set.uIcc_of_le hs.2] at hσ
      rw [hZbase σ ⟨hs.1.trans hσ.1, hσ.2⟩ (le_of_lt (lt_of_lt_of_le h9s hσ.1))]
    rw [← hsplit, h1, h2, h3]

/-! ## The transfer -/

theorem anchor_transfer (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St}
    (hZcont : ContinuousOn Z (Set.Icc Work.Anchor.wl Work.Anchor.wr))
    (hZeq : ∀ s ∈ Set.Icc Work.Anchor.wl Work.Anchor.wr,
      Work.Anchor.Gf n h s (Z s) =
        (∫ σ in s..Work.Anchor.wr, Work.Anchor.Thf n h s σ (Z σ)) + Work.Anchor.Xif n h s)
    (hZdist : ∀ s ∈ Set.Icc Work.Anchor.wl Work.Anchor.wr,
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 100) :
    Z Work.Anchor.wr = Work.OddVolterra.baseState Work.Anchor.wr ∧
    (∀ s ∈ Set.Ioo (9 / 10 : ℝ) Work.Anchor.wr, Z s = Work.OddVolterra.baseState s) ∧
    (∀ s ∈ Set.Icc Work.Anchor.wl Work.Anchor.wr,
      Work.OddVolterra.Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ),
          Work.OddVolterra.Theta n h s σ
            (if σ ≤ 9 / 10 then Z σ else Work.OddVolterra.baseState σ)) +
          Work.OddVolterra.Xi n h s) := by
  have hwr_mem : wr ∈ Set.Icc wl wr := ⟨wl_le_wr, le_rfl⟩
  have hZdist' : ∀ s ∈ Set.Icc wl wr, ‖Z s - baseState s‖ ≤ 1 / 100 := fun s hs => by
    rw [← dist_eq_norm]; exact hZdist s hs
  have htrunc := sys_transfer n hn hh hsupp hsm1 hsm2 hZeq hZdist
  -- the value at the right end of the window
  have hZend : Z wr = baseState wr := by
    obtain ⟨c, hc, hInj⟩ :=
      Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsm2 (b := wl)
        wl_pos wl_le_one
    have hwrI : wr ∈ Set.Icc wl (1 : ℝ) := ⟨wl_le_wr, wr_lt_one.le⟩
    have hZw : dist (Z wr) (baseState wr) ≤ 1 / 2 := by linarith [hZdist wr hwr_mem]
    have hz : Z wr ∈ Metric.closedBall (baseState wr) (1 / 2) := by
      rwa [Metric.mem_closedBall]
    have hz' : baseState wr ∈ Metric.closedBall (baseState wr) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_self]; norm_num
    have hEq : Godd n h wr (Z wr) = Godd n h wr (baseState wr) := by
      rw [htrunc wr hwr_mem, intervalIntegral.integral_same, zero_add,
        Window.base_volterra_right n hn hsupp one_sub_tau_lt_wr wr_lt_one]
      abel
    have hle := hInj wr hwrI (Z wr) hz (baseState wr) hz'
    rw [hEq, sub_self, norm_zero] at hle
    have h0 : ‖Z wr - baseState wr‖ ≤ 0 := by
      nlinarith [hle, hc, norm_nonneg (Z wr - baseState wr)]
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
  -- the extension of the solution by the ball's state
  let Zhat : ℝ → St := fun s => if s ≤ wr then Z s else baseState s
  have hZhat_le : ∀ s : ℝ, s ≤ wr → Zhat s = Z s := by
    intro s hs
    show (if s ≤ wr then Z s else baseState s) = Z s
    rw [if_pos hs]
  have hZhat_gt : ∀ s : ℝ, wr < s → Zhat s = baseState s := by
    intro s hs
    show (if s ≤ wr then Z s else baseState s) = baseState s
    rw [if_neg (not_le.mpr hs)]
  have hZhat_ge : ∀ s : ℝ, wr ≤ s → Zhat s = baseState s := by
    intro s hs
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, hZhat_le wr le_rfl, hZend]
    · exact hZhat_gt s h
  have hZhat_cont : ContinuousOn Zhat (Set.Icc (9 / 10 : ℝ) 1) := by
    have h1 : ContinuousOn Zhat (Set.Icc (9 / 10 : ℝ) wr) :=
      (hZcont.mono (Set.Icc_subset_Icc (by norm_num [wl]) le_rfl)).congr (fun s hs => by
        rcases lt_or_eq_of_le hs.2 with h | h
        · exact hZhat_le s h.le
        · rw [h]; exact hZhat_le wr le_rfl)
    have h2 : ContinuousOn Zhat (Set.Icc wr 1) :=
      (Window.continuous_baseState.continuousOn).congr (fun s hs => hZhat_ge s hs.1)
    have hunion := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by norm_num [wr]) (by norm_num [wr])] at hunion
  have hZhat_ball : ∀ s ∈ Set.Icc (9 / 10 : ℝ) 1, ‖Zhat s - baseState s‖ ≤ 1 / 2 := by
    intro s hs
    rcases le_or_gt s wr with h | h
    · rw [hZhat_le s h, ← dist_eq_norm]
      exact le_trans (hZdist s ⟨by linarith [hs.1, (by norm_num [wl] : wl ≤ 9 / 10)], h⟩)
        (by norm_num)
    · rw [hZhat_gt s h, sub_self, norm_zero]; norm_num
  -- the extension solves the paper's system on the right half-window
  have hZhat_solves : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) 1,
      Godd n h s (Zhat s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zhat σ)) + Xi n h s := by
    intro s hs
    have hsI : s ∈ Set.Icc wl (1 : ℝ) :=
      ⟨by linarith [hs.1, (by norm_num [wl] : wl ≤ 9 / 10)], hs.2.le⟩
    rcases le_or_gt s wr with hle | hlt
    · -- inside the window
      have hsIcc : s ∈ Set.Icc wl wr := ⟨hsI.1, hle⟩
      rw [hZhat_le s hle, htrunc s hsIcc]
      have hint : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zhat σ)) volume s 1 :=
        intervalIntegrable_Theta_of_continuous (n := n) hn hh hsupp hsm2 hsI hs.2.le le_rfl
          (hZhat_cont.mono (Set.Icc_subset_Icc hs.1.le le_rfl))
          (fun σ hσ => hZhat_ball σ ⟨le_trans hs.1.le hσ.1, hσ.2⟩)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hint.mono_set (by
          rw [Set.uIcc_of_le hle, Set.uIcc_of_le hs.2.le]
          exact Set.Icc_subset_Icc le_rfl wr_lt_one.le))
        (hint.mono_set (by
          rw [Set.uIcc_of_le wr_lt_one.le, Set.uIcc_of_le hs.2.le]
          exact Set.Icc_subset_Icc hle le_rfl))
      have h1 : (∫ σ in s..wr, Theta n h s σ (Zhat σ)) = ∫ σ in s..wr, Theta n h s σ (Z σ) :=
        intervalIntegral.integral_congr_Ioo_of_le hle (fun σ hσ => by rw [hZhat_le σ hσ.2.le])
      have h2 : (∫ σ in wr..(1 : ℝ), Theta n h s σ (Zhat σ))
          = ∫ σ in wr..(1 : ℝ), Theta n h s σ (baseState σ) :=
        intervalIntegral.integral_congr_Ioo_of_le wr_lt_one.le
          (fun σ hσ => by rw [hZhat_ge σ hσ.1.le])
      rw [← hsplit, h1, h2]
      abel
    · -- beyond the window: the unperturbed identity
      have hsτ : (1 : ℝ) - Work.OddVolterra.tau < s := by
        rw [Window.one_sub_tau_eq_window]; linarith [hs.1]
      rw [hZhat_gt s hlt, Window.base_volterra_right n hn hsupp hsτ hs.2]
      have h3 : (∫ σ in s..(1 : ℝ), Theta n h s σ (Zhat σ))
          = ∫ σ in s..(1 : ℝ), Theta n h s σ (baseState σ) :=
        intervalIntegral.integral_congr_Ioo_of_le hs.2.le
          (fun σ hσ => by rw [hZhat_ge σ (le_of_lt (lt_trans hlt hσ.1))])
      rw [h3]
  -- uniqueness on the right half-window
  obtain ⟨L, hL, C, hC, hLip, hBd, hCont⟩ :=
    Existence.theta_lipschitz_state_ball n hn hh hsupp hsm2 (b := (9 / 10 : ℝ))
      (by norm_num) (by norm_num)
  obtain ⟨c, hc, hInj9⟩ :=
    Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsm2 (b := (9 / 10 : ℝ))
      (by norm_num) (by norm_num)
  have heqOn : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) 1, Zhat s = baseState s :=
    Existence.eqOn_of_solves (n := n) (h := h) (b := (9 / 10 : ℝ)) (L := L) (C := C) (c := c)
      hL hc (by norm_num) (by norm_num) hLip hBd hCont hInj9
      hZhat_cont Window.continuous_baseState.continuousOn hZhat_solves
      (fun s hs => Window.base_volterra_right n hn hsupp
        (by rw [Window.one_sub_tau_eq_window]; exact hs.1) hs.2)
      hZhat_ball (fun s _ => by rw [sub_self, norm_zero]; norm_num)
  have hZeqOn : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) wr, Z s = baseState s := by
    intro s hs
    have h := heqOn s ⟨hs.1, lt_trans hs.2 wr_lt_one⟩
    rwa [hZhat_le s hs.2.le] at h
  -- the value at the left end of the tail, by continuity
  have hZ9 : Z (9 / 10 : ℝ) = baseState (9 / 10) := by
    have hclosed : IsClosed {x : ℝ | x ∈ Set.Icc (9 / 10 : ℝ) wr ∧ Z x = baseState x} :=
      IsClosed.isClosed_eq isClosed_Icc
        (hZcont.mono (Set.Icc_subset_Icc (by norm_num [wl]) le_rfl))
        Window.continuous_baseState.continuousOn
    have hsub : Set.Ioo (9 / 10 : ℝ) wr ⊆
        {x : ℝ | x ∈ Set.Icc (9 / 10 : ℝ) wr ∧ Z x = baseState x} :=
      fun x hx => ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hZeqOn x hx⟩
    have hmem : (9 / 10 : ℝ) ∈ closure (Set.Ioo (9 / 10 : ℝ) wr) := by
      rw [closure_Ioo (by norm_num [wr] : (9 / 10 : ℝ) ≠ wr)]
      exact ⟨le_rfl, by norm_num [wr]⟩
    exact (closure_minimal hsub hclosed hmem).2
  -- the curve is the ball's state on the whole tail
  have hZbase : ∀ s ∈ Set.Icc wl wr, 9 / 10 ≤ s → Z s = baseState s := by
    intro s hs h9
    rcases lt_or_eq_of_le h9 with h9' | h9'
    · rcases lt_trichotomy s wr with h | h | h
      · exact hZeqOn s ⟨h9', h⟩
      · rw [h]; exact hZend
      · exact absurd hs.2 (not_le.mpr h)
    · rw [← h9']; exact hZ9
  -- the paper's equation on the window
  have hfinal : ∀ s ∈ Set.Icc wl wr,
      Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ),
          Theta n h s σ (if σ ≤ 9 / 10 then Z σ else baseState σ)) + Xi n h s := by
    intro s hs
    rw [htrunc s hs]
    have hIT := integral_ite_eq n hn hh hsupp hsm2 hZcont hZdist hZbase hs
    rw [← hIT]
    abel
  exact ⟨hZend, hZeqOn, hfinal⟩

end

end Work.Anchor
