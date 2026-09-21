import Mathlib
import Submission.Work.OddVolterra.Existence.wdc_aux

/-!
# The clamped system on the wide window `[1/4, 19/20]`

`Work.OddVolterra.Existence.clamped_solves_of_paper` and
`intervalIntegrable_thetaM_window` (`wdc_aux.lean`) are stated on the narrow window
`[7/10, 19/20]`; this file restates them on the wide window `[1/4, 19/20]`, with the continuity
of the state on `Icc (1/4) 1` supplied as a hypothesis (rather than derived from the `C^∞`-ness on
`(1/4, ∞)`, which fails exactly at the left end `1/4`).  The proofs are the originals: the only
change is that the left end of the window is `1/4` instead of `7/10`, which is still compatible
with the radicand positivity (`krad_pos_of_add_pos'`: `σ + a > 1/10` and `|t| ≥ 1/5`) used in the
`Θ = ΘM` bridge.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open Work.OddVolterra
open Work.OddVolterra.Existence
open scoped Topology ContDiff Interval

noncomputable section

variable {n : ℕ} {h : ℝ → ℝ}

lemma w_window_mem {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :
    s ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi :=
  ⟨by rw [show Work.OddVolterra.WinData.wLo = 1 / 4 from rfl]; linarith [hs.1],
   by rw [show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]; exact hs.2⟩

/-- The chord endpoints of a state in the ball of radius `1/2` are at distance `> 1/5`. -/
lemma one_fifth_of_ball {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1) {z : Work.OddVolterra.St}
    (hz : ‖z - Work.OddVolterra.baseState σ‖ ≤ 1 / 2) : 1 / 5 < |z 0| ∧ 1 / 5 < |z 1| :=
  ⟨Work.OddVolterra.WinData.one_fifth_lt_abs_coord hσ.1 hσ.2 hz 0 (Or.inl rfl),
   Work.OddVolterra.WinData.one_fifth_lt_abs_coord hσ.1 hσ.2 hz 1 (Or.inr rfl)⟩

lemma continuous_baseState : Continuous (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
  have h1 : Continuous (Commons.Geometry.Ulam.profileX : ℝ → ℝ) :=
    (Work.OddVolterra.Existence.contDiff_profileX).continuous
  have h2 : Continuous (deriv (Commons.Geometry.Ulam.profileX : ℝ → ℝ)) :=
    (Work.OddVolterra.Existence.contDiff_profileX).continuous_deriv (by simp)
  unfold Work.OddVolterra.baseState
  fun_prop

lemma w_window_mem_tcl {σ s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ))
    (hσ : σ ∈ Set.Icc s (19 / 20 : ℝ)) :
    σ ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi := by
  constructor
  · rw [show Work.OddVolterra.WinData.wLo = 1 / 4 from rfl]; linarith [hs.1, hσ.1]
  · rw [show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]; exact hσ.2

/-- The manifest integrand is interval integrable on `[s,19/20]` and on `[19/20,1]`. -/
lemma w_intervalIntegrable_thetaM_window (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St} (hZc : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1))
    (hball : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20 : ℝ)) :
    IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume s (19 / 20 : ℝ) ∧
    IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume (19 / 20 : ℝ) 1 := by
  have hs8 : (1 / 8 : ℝ) < s := by linarith [hs.1]
  have hs9 : s < 99 / 100 := by linarith [hs.2]
  have hmain : ∀ {a b : ℝ} (hab : a ≤ b), (1 / 4 : ℝ) ≤ a → b ≤ 1 →
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume a b := by
    intro a b hab ha hb
    refine Work.OddVolterra.WinData.intervalIntegrable_thetaM_of_curve n hh hsupp h1
      hs8 hs9 hab (hZc.mono ?_) ?_
    · intro x hx
      exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    · intro σ hσ
      have h7 : (1 / 4 : ℝ) ≤ σ := le_trans ha hσ.1
      have hσ1 : σ ≤ 1 := le_trans hσ.2 hb
      have hzσ : ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := hball σ ⟨h7, hσ1⟩
      obtain ⟨h5, h5'⟩ := one_fifth_of_ball ⟨by linarith, hσ1⟩ hzσ
      exact ⟨by linarith [hσ.1], by linarith [hσ.2], h5, h5'⟩
  exact ⟨hmain hs.2 hs.1 (by norm_num), hmain (by norm_num) (by norm_num) le_rfl⟩

/-- **The clamped system for the given solution.** -/
lemma w_clamped_solves_of_paper (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St}
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)))
    (hZc : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1))
    (heq : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
          Work.OddVolterra.Xi n h s)
    (htail : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s)
    (hball : ∀ s ∈ Set.Icc (1 / 4 : ℝ) 1,
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ Set.Ioc (1 / 4 : ℝ) (19 / 20 : ℝ)) :
    Work.OddVolterra.WinData.Gcl n h s (Z s) =
      (∫ σ in s..Work.OddVolterra.WinData.wHi,
        Work.OddVolterra.WinData.Tcl n h s σ (Z σ)) + Work.OddVolterra.WinData.Xcl n h s := by
  have hsW : s ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi :=
    ⟨le_of_lt hs.1, hs.2⟩
  have hball' : ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := by
    intro σ hσ; rw [← dist_eq_norm]; exact hball σ hσ
  have hzs : ‖Z s - Work.OddVolterra.baseState s‖ ≤ Work.OddVolterra.WinData.wRho := by
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]
    exact hball' s ⟨le_of_lt hs.1, by linarith [hs.2]⟩
  have hmo : s ∈ Set.Ioo (1 / 4 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- `Θ = ΘM` on `(s,1)`
  have hTheta : ∀ σ ∈ Set.Ioo s 1,
      Work.OddVolterra.Theta n h s σ (Z σ) =
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) := by
    intro σ hσ
    have hσ4 : (1 / 4 : ℝ) ≤ σ := by linarith [hs.1, hσ.1]
    have hσ1 : σ ≤ 1 := le_of_lt hσ.2
    have hzσ : ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 :=
      hball' σ ⟨by linarith [hs.1, hσ.1], hσ1⟩
    obtain ⟨h5, h5'⟩ := one_fifth_of_ball ⟨hσ4, hσ1⟩ hzσ
    exact (Work.OddVolterra.Window.ThetaM_eq_Theta n hn hh hσ.1 (δ := 1 / 8)
      (by norm_num) (Z σ)
      (fun a ha => Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp h1
        (by linarith [ha.1, hs.1]) (by rw [abs_neg]; exact le_of_lt h5))
      (fun a ha => Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp h1
        (by linarith [ha.1, hs.1]) (le_of_lt h5'))).symm
  have hman : (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ))
      = ∫ σ in s..(1 : ℝ), Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) :=
    intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hmo.2) hTheta
  obtain ⟨hI1, hI2⟩ := w_intervalIntegrable_thetaM_window hn hh hsupp h1 hZc hball' ⟨le_of_lt hs.1, hs.2⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  -- the frozen tail: on `[19/20,1]` the state is `baseState`
  have htail' : (∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ))
      = ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1)] at hσ
    rw [htail σ (by linarith [hσ.1])]
  -- `Tcl = ΘM` on `[s, wHi]`
  have hTcl : (∫ σ in s..Work.OddVolterra.WinData.wHi,
      Work.OddVolterra.WinData.Tcl n h s σ (Z σ))
      = ∫ σ in s..Work.OddVolterra.WinData.wHi,
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl,
      Set.uIcc_of_le hs.2] at hσ
    refine Work.OddVolterra.WinData.Tcl_eq_ThetaM hsW (w_window_mem_tcl ⟨le_of_lt hs.1, hs.2⟩ hσ) ?_
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]
    exact hball' σ ⟨le_trans (le_of_lt hs.1) hσ.1, by linarith [hσ.2]⟩
  rw [Work.OddVolterra.WinData.Gcl_eq_Godd hsW hzs, heq s hmo, hman, hTcl,
    Work.OddVolterra.WinData.Xcl_eq hsW, ← hsplit, htail',
    show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]
  abel

end

end Work.OddCurveB.Step2
