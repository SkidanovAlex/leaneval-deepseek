import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.Window.Kvec_deriv2_close
import Submission.Work.OddVolterra.Window.KvecJet_data2
import Submission.Work.OddVolterra.Window.krad_deriv2_data
import Submission.Work.OddVolterra.Window.hquot_deriv2_bound
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.Anchor.deriv_close
import Submission.Work.OddVolterra.WinData.smooth_upgrade
import Submission.Work.OddVolterra.Window.TW2_kvecM_state_unif
import Submission.Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec
import Submission.Work.OddVolterra.Existence.odd_linearization
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.VolterraLong.volterra_long_exists_C1_r

/-!
# The clamped window data and its slope derivatives (auxiliary snapshot)

This module collects the `s`-derivative data of the clamped window data `Gcl/Tcl/Xcl`
(`GsCl`, `TsCl`, `XsCl`), their chain rules, the identity identifying them with the derivatives of
`Godd`/`ThetaM`/`Xi + frozen tail`, and the clamped Volterra equation for a solution of the paper's
system on `[7/10, 19/20]`.  It is consumed by `window_deriv_close_core.lean`.

The route is:

* the clamped data `WinData.Gcl / Tcl / Xcl` of `win_data.lean` are globally `C^∞`
  (`gcl_contDiffOn`, `tcl_contDiffOn`, `contDiffOn_Xcl`) and agree with the paper's data on the
  box `[1/4, 19/20] × ball(baseState s, 1/2)` (`Gcl_eq_Godd`, `Tcl_eq_ThetaM`, `Xcl_eq`);
* `WinData.clamped_base_identity` gives the clamped base solution *and* its `s`-derivative, i.e.
  `A s (deriv baseState s) = RHS₀ s` for the base linearisation `A s` of `odd_linearization`;
* `Work.VolterraLong.deriv_from_solution_linearized` applied to the clamped system for the given
  `Z` (with `V` produced by the perturbed-inverse step `VolterraLong.C1.solve_near_equiv`) gives
  `deriv Z s = V s` and the quantitative bound `‖V s - deriv baseState s‖ ≤ 2 B (κ ‖Z₀'‖ + δ)`;
* the two estimates `κ ≤ C ε` (fderiv-closeness, `Anchor.deriv_close`) and `δ ≤ C ε` (the four
  terms of `RHS_h - RHS₀`) close the proof.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The `s`-derivative data of the clamped data -/

/-- The `s`-derivative of the clamped state datum, as a function of the slope and the state. -/
def GsCl (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  (fderiv ℝ (fun p : ℝ × Work.OddVolterra.St => Work.OddVolterra.WinData.Gcl n h p.1 p.2)
    (s, z)) ((1, 0) : ℝ × Work.OddVolterra.St)

/-- The `s`-derivative of the clamped `Θ` datum. -/
def TsCl (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : Work.OddVolterra.St) : Work.OddVolterra.St :=
  (fderiv ℝ (fun p : ℝ × (ℝ × Work.OddVolterra.St) =>
      Work.OddVolterra.WinData.Tcl n h p.1 p.2.1 p.2.2) (s, (σ, z)))
    ((1, 0, 0) : ℝ × (ℝ × Work.OddVolterra.St))

/-- The derivative of the clamped source. -/
def XsCl (n : ℕ) (h : ℝ → ℝ) (s : ℝ) : Work.OddVolterra.St :=
  deriv (fun u : ℝ => Work.OddVolterra.WinData.Xcl n h u) s

variable {n : ℕ} {h : ℝ → ℝ}

/-- The `C^{n+3}` bump hypothesis gives the `1/100`-bounds used by the clamped-data lemmas. -/
lemma bump_small {n : ℕ} {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBumpThree n ε h)
    (hε : ε ≤ 1 / 100) {k : ℕ} (hk : k ≤ n + 3) : ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
  fun s => le_trans (hb.deriv_bound hk s) hε

lemma bump_small2 {n : ℕ} {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBumpThree n ε h)
    (hε : ε ≤ 1 / 100) {k : ℕ} (hk : k ≤ 2) : ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
  bump_small hb hε (le_trans hk (by omega))
    -- needs 2 ≤ n + 3, i.e. n ≥ -1: given by `hn`

lemma bump_supp {n : ℕ} {ε : ℝ} {h : ℝ → ℝ} (hb : IsSmallFlatBumpThree n ε h) :
    Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
  fun x hx => ⟨le_of_lt (hb.support_subset hx).1, le_of_lt (hb.support_subset hx).2⟩

lemma gcl_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.WinData.Gcl n h p.1 p.2) :=
  contDiffOn_univ.mp (Work.OddVolterra.WinData.gcl_contDiffOn n hh hsupp h2)

lemma tcl_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (ℝ × Work.OddVolterra.St) =>
      Work.OddVolterra.WinData.Tcl n h q.1 q.2.1 q.2.2) :=
  contDiffOn_univ.mp (Work.OddVolterra.WinData.tcl_contDiffOn n hh hsupp h2)

lemma xcl_contDiff {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Work.OddVolterra.WinData.Xcl n h s) :=
  contDiffOn_univ.mp (Work.OddVolterra.WinData.contDiffOn_Xcl n hn hh hsupp h1)

lemma gcl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun p : ℝ × Work.OddVolterra.St => Work.OddVolterra.WinData.Gcl n h p.1 p.2) :=
  (gcl_contDiff (n := n) hh hsupp h2).continuous

lemma tcl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun q : ℝ × (ℝ × Work.OddVolterra.St) =>
      Work.OddVolterra.WinData.Tcl n h q.1 q.2.1 q.2.2) :=
  (tcl_contDiff (n := n) hh hsupp h2).continuous

lemma xcl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun s : ℝ => Work.OddVolterra.WinData.Xcl n h s) :=
  (xcl_contDiff (n := n) hn hh hsupp h1).continuous

lemma gsCl_hasDerivAt {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (s : ℝ)
    (z : Work.OddVolterra.St) :
    HasDerivAt (fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z) (GsCl n h s z) s := by
  have hcd := gcl_contDiff (n := n) hh hsupp h2
  have h1 : HasFDerivAt (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.WinData.Gcl n h p.1 p.2)
      (fderiv ℝ (fun p : ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.WinData.Gcl n h p.1 p.2) (s, z)) (s, z) :=
    (hcd.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2' : HasDerivAt (fun u : ℝ => (u, z)) ((1, 0) : ℝ × Work.OddVolterra.St) s := by
    simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  have h3 := h1.comp_hasDerivAt s h2'
  have hfun : ((fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.WinData.Gcl n h p.1 p.2) ∘ (fun u : ℝ => (u, z)))
      = fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z := rfl
  rw [hfun] at h3
  exact h3

lemma tsCl_hasDerivAt {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (s σ : ℝ) (z : Work.OddVolterra.St) :
    HasDerivAt (fun u : ℝ => Work.OddVolterra.WinData.Tcl n h u σ z) (TsCl n h s σ z) s := by
  have hcd := tcl_contDiff (n := n) hh hsupp h2
  have h1 : HasFDerivAt (fun p : ℝ × (ℝ × Work.OddVolterra.St) =>
      Work.OddVolterra.WinData.Tcl n h p.1 p.2.1 p.2.2)
      (fderiv ℝ (fun p : ℝ × (ℝ × Work.OddVolterra.St) =>
        Work.OddVolterra.WinData.Tcl n h p.1 p.2.1 p.2.2) (s, (σ, z))) (s, (σ, z)) :=
    (hcd.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2' : HasDerivAt (fun u : ℝ => (u, (σ, z)))
      ((1 : ℝ), ((0 : ℝ), (0 : Work.OddVolterra.St))) s := by
    have h := (hasDerivAt_id s).prodMk (hasDerivAt_const s (σ, z))
    convert h using 2
    all_goals first
      | (simp)
      | (simp)
      | rfl
  have h3 := h1.comp_hasDerivAt s h2'
  have hfun : ((fun p : ℝ × (ℝ × Work.OddVolterra.St) =>
      Work.OddVolterra.WinData.Tcl n h p.1 p.2.1 p.2.2) ∘ (fun u : ℝ => (u, (σ, z))))
      = fun u : ℝ => Work.OddVolterra.WinData.Tcl n h u σ z := rfl
  rw [hfun] at h3
  exact h3

lemma xsCl_hasDerivAt {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (s : ℝ) :
    HasDerivAt (fun u : ℝ => Work.OddVolterra.WinData.Xcl n h u) (XsCl n h s) s :=
  ((xcl_contDiff (n := n) hn hh hsupp h1).differentiable (by simp)).differentiableAt.hasDerivAt

lemma gsCl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun p : ℝ × Work.OddVolterra.St => GsCl n h p.1 p.2) := by
  have h := (gcl_contDiff (n := n) hh hsupp h2).continuous_fderiv_apply (by simp)
  have hcomp : Continuous (fun p : ℝ × Work.OddVolterra.St =>
      ((p.1, p.2), ((1, 0) : ℝ × Work.OddVolterra.St))) := by fun_prop
  have h' := h.comp hcomp
  simpa [GsCl, Function.comp_def] using h'

lemma tsCl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (fun p : ℝ × (ℝ × Work.OddVolterra.St) => TsCl n h p.1 p.2.1 p.2.2) := by
  have h := (tcl_contDiff (n := n) hh hsupp h2).continuous_fderiv_apply (by simp)
  have hcomp : Continuous (fun p : ℝ × (ℝ × Work.OddVolterra.St) =>
      ((p.1, (p.2.1, p.2.2)), ((1, 0, 0) : ℝ × (ℝ × Work.OddVolterra.St)))) := by fun_prop
  have h' := h.comp hcomp
  simpa [TsCl, Function.comp_def] using h'

lemma xsCl_continuous {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (XsCl n h) :=
  (xcl_contDiff (n := n) hn hh hsupp h1).continuous_deriv (by simp)

lemma gcl_differentiableAt {h : ℝ → ℝ} (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (s : ℝ)
    (z : Work.OddVolterra.St) :
    DifferentiableAt ℝ (fun w : Work.OddVolterra.St => Work.OddVolterra.WinData.Gcl n h s w) z := by
  have hcd := gcl_contDiff (n := n) hh hsupp h2
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Work.OddVolterra.St => (s, w)) z := by fun_prop
  have hcomp := hcd.contDiffAt.comp z h1
  have hfun : (fun p : ℝ × Work.OddVolterra.St =>
      Work.OddVolterra.WinData.Gcl n h p.1 p.2) ∘ (fun w : Work.OddVolterra.St => (s, w))
      = fun w : Work.OddVolterra.St => Work.OddVolterra.WinData.Gcl n h s w := rfl
  rw [hfun] at hcomp
  exact hcomp.differentiableAt (by simp)

/-! ## The clamps are the model data on the window -/

lemma window_mem {s : ℝ} (hs : s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) :
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

lemma window_mem_tcl {σ s : ℝ} (hs : s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ))
    (hσ : σ ∈ Set.Icc s (19 / 20 : ℝ)) :
    σ ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi := by
  constructor
  · rw [show Work.OddVolterra.WinData.wLo = 1 / 4 from rfl]; linarith [hs.1, hσ.1]
  · rw [show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]; exact hσ.2

/-- The manifest integrand is interval integrable on `[s,19/20]` and on `[19/20,1]`. -/
lemma intervalIntegrable_thetaM_window (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St} (hZc : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1))
    (hball : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) :
    IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume s (19 / 20 : ℝ) ∧
    IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume (19 / 20 : ℝ) 1 := by
  have hs8 : (1 / 8 : ℝ) < s := by linarith [hs.1]
  have hs9 : s < 99 / 100 := by linarith [hs.2]
  have hmain : ∀ {a b : ℝ} (hab : a ≤ b), (7 / 10 : ℝ) ≤ a → b ≤ 1 →
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n h s σ (Z σ)) volume a b := by
    intro a b hab ha hb
    refine Work.OddVolterra.WinData.intervalIntegrable_thetaM_of_curve n hh hsupp h1
      hs8 hs9 hab (hZc.mono ?_) ?_
    · intro x hx
      exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    · intro σ hσ
      have h7 : (7 / 10 : ℝ) ≤ σ := le_trans ha hσ.1
      have hσ1 : σ ≤ 1 := le_trans hσ.2 hb
      have hzσ : ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := hball σ ⟨h7, hσ1⟩
      obtain ⟨h5, h5'⟩ := one_fifth_of_ball ⟨by linarith, hσ1⟩ hzσ
      exact ⟨by linarith [hσ.1], by linarith [hσ.2], h5, h5'⟩
  exact ⟨hmain hs.2 hs.1 (by norm_num), hmain (by norm_num) (by norm_num) le_rfl⟩

/-- **The clamped system for the given solution.** -/
lemma clamped_solves_of_paper (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {Z : ℝ → Work.OddVolterra.St}
    (hZsm : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)))
    (heq : ∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
      Work.OddVolterra.Godd n h s (Z s) =
        (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
          Work.OddVolterra.Xi n h s)
    (htail : ∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s)
    (hball : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
      dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) :
    Work.OddVolterra.WinData.Gcl n h s (Z s) =
      (∫ σ in s..Work.OddVolterra.WinData.wHi,
        Work.OddVolterra.WinData.Tcl n h s σ (Z σ)) + Work.OddVolterra.WinData.Xcl n h s := by
  have hsW := window_mem hs
  have hball' : ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1,
      ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := by
    intro σ hσ; rw [← dist_eq_norm]; exact hball σ hσ
  have hZc : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) := by
    refine (hZsm.continuousOn).mono ?_
    intro x hx
    show (1 / 4 : ℝ) < x
    linarith [hx.1]
  have hzs : ‖Z s - Work.OddVolterra.baseState s‖ ≤ Work.OddVolterra.WinData.wRho := by
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]
    exact hball' s ⟨hs.1, by linarith [hs.2]⟩
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
  obtain ⟨hI1, hI2⟩ := intervalIntegrable_thetaM_window hn hh hsupp h1 hZc hball' hs
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
    refine Work.OddVolterra.WinData.Tcl_eq_ThetaM hsW (window_mem_tcl hs hσ) ?_
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]
    exact hball' σ ⟨le_trans hs.1 hσ.1, by linarith [hσ.2]⟩
  rw [Work.OddVolterra.WinData.Gcl_eq_Godd hsW hzs, heq s hmo, hman, hTcl,
    Work.OddVolterra.WinData.Xcl_eq hsW, ← hsplit, htail',
    show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]
  abel

/-- **The clamped system for the base** (`h = 0`). -/
lemma clamped_solves_base (hn : 1 ≤ n) {s : ℝ}
    (hs : s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) :
    Work.OddVolterra.WinData.Gcl n 0 s (Work.OddVolterra.baseState s) =
      (∫ σ in s..Work.OddVolterra.WinData.wHi,
        Work.OddVolterra.WinData.Tcl n 0 s σ (Work.OddVolterra.baseState σ)) +
        Work.OddVolterra.WinData.Xcl n 0 s := by
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau) := by
    intro x hx; rw [Function.mem_support] at hx; exact absurd rfl hx
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> norm_num
  have hsW := window_mem hs
  have hzs : ‖Work.OddVolterra.baseState s - Work.OddVolterra.baseState s‖
      ≤ Work.OddVolterra.WinData.wRho := by
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]; simp
  have hmo : s ∈ Set.Ioo (1 / 4 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbc : ContinuousOn (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St)
      (Set.Icc (7 / 10 : ℝ) 1) := continuous_baseState.continuousOn
  have hTheta : ∀ σ ∈ Set.Ioo s 1,
      Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.baseState σ) =
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ) := by
    intro σ hσ
    have hσ4 : (1 / 4 : ℝ) ≤ σ := by linarith [hs.1, hσ.1]
    have hσ1 : σ ≤ 1 := le_of_lt hσ.2
    obtain ⟨h5, h5'⟩ := one_fifth_of_ball (z := Work.OddVolterra.baseState σ)
      ⟨hσ4, hσ1⟩ (by simp)
    exact (Work.OddVolterra.Window.ThetaM_eq_Theta n hn contDiff_const hσ.1 (δ := 1 / 8)
      (by norm_num) (Work.OddVolterra.baseState σ)
      (fun a ha => Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp0 hsmall0
        (by linarith [ha.1, hs.1]) (by rw [abs_neg]; exact le_of_lt h5))
      (fun a ha => Work.OddVolterra.WinData.krad_pos_of_add_pos' hsupp0 hsmall0
        (by linarith [ha.1, hs.1]) (le_of_lt h5'))).symm
  have hman : (∫ σ in s..(1 : ℝ),
        Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.baseState σ))
      = ∫ σ in s..(1 : ℝ),
          Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ) :=
    intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hmo.2) hTheta
  have hint : ∀ {a b : ℝ} (hab : a ≤ b), (7 / 10 : ℝ) ≤ a → b ≤ 1 →
      IntervalIntegrable (fun σ : ℝ =>
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ)) volume a b := by
    intro a b hab ha hb
    refine Work.OddVolterra.WinData.intervalIntegrable_thetaM_of_curve n contDiff_const
      hsupp0 hsmall0 (by linarith [hs.1]) (by linarith [hs.2]) hab (hbc.mono ?_) ?_
    · intro x hx; exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
    · intro σ hσ
      obtain ⟨h5, h5'⟩ := one_fifth_of_ball (z := Work.OddVolterra.baseState σ)
        ⟨by linarith [le_trans ha hσ.1], le_trans hσ.2 hb⟩ (by simp)
      exact ⟨by linarith [hσ.1], by linarith [hσ.2], h5, h5'⟩
  have hI1 := hint (a := s) (b := 19 / 20) hs.2 hs.1 (by norm_num)
  have hI2 := hint (a := 19 / 20) (b := 1) (by norm_num) (by norm_num) le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hTcl : (∫ σ in s..Work.OddVolterra.WinData.wHi,
      Work.OddVolterra.WinData.Tcl n 0 s σ (Work.OddVolterra.baseState σ))
      = ∫ σ in s..Work.OddVolterra.WinData.wHi,
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl,
      Set.uIcc_of_le hs.2] at hσ
    refine Work.OddVolterra.WinData.Tcl_eq_ThetaM hsW (window_mem_tcl hs hσ) ?_
    rw [show Work.OddVolterra.WinData.wRho = 1 / 2 from rfl]; simp
  have hmo0 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbase := base_volterra n hn s hmo0
  have hbase' : Work.OddVolterra.Godd n 0 s (Work.OddVolterra.baseState s)
      = (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.baseState σ))
        + Work.OddVolterra.Xi n 0 s := by
    have h2 : (∫ σ in s..(1 : ℝ),
          Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.baseState σ))
        = (∫ σ in s..(1 : ℝ),
          Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.stateOf Commons.Geometry.Ulam.profileX
            Commons.Geometry.Ulam.profileX σ)) :=
      intervalIntegral.integral_congr fun σ _ => by
        rw [show Work.OddVolterra.stateOf Commons.Geometry.Ulam.profileX
          Commons.Geometry.Ulam.profileX σ = Work.OddVolterra.baseState σ from rfl]
    rw [h2]
    exact hbase
  rw [Work.OddVolterra.WinData.Gcl_eq_Godd hsW hzs, hbase', hman, hTcl,
    Work.OddVolterra.WinData.Xcl_eq hsW, ← hsplit,
    show Work.OddVolterra.WinData.wHi = 19 / 20 from rfl]
  abel

/-! ## The `s`-derivative data are the model derivatives

On the window the clamps equal `1`, so the derivatives of `Gcl`, `Tcl`, `Xcl` are the derivatives of
the model data. -/

lemma gsCl_eq (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Ioo Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState s‖
      < Work.OddVolterra.WinData.wRho) :
    GsCl n h s z = deriv (fun u : ℝ => Work.OddVolterra.Godd n h u z) s := by
  have hderiv : GsCl n h s z
      = deriv (fun u : ℝ => Work.OddVolterra.WinData.Gcl n h u z) s :=
    (gsCl_hasDerivAt hn hh hsupp h2 s z).deriv.symm
  rw [hderiv]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcont : ContinuousAt (fun u : ℝ => ‖z - Work.OddVolterra.baseState u‖) s :=
    ((continuous_const.sub continuous_baseState).norm).continuousAt
  have hmem : ∀ᶠ u in 𝓝 s, u ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
  filter_upwards [hmem, hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hz)] with u hu hzu
  exact Work.OddVolterra.WinData.Gcl_eq_Godd hu (le_of_lt hzu)

lemma tsCl_eq (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Ioo Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi)
    (hσ : σ ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi)
    {z : Work.OddVolterra.St} (hz : ‖z - Work.OddVolterra.baseState σ‖
      < Work.OddVolterra.WinData.wRho) :
    TsCl n h s σ z = deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s := by
  have hderiv : TsCl n h s σ z
      = deriv (fun u : ℝ => Work.OddVolterra.WinData.Tcl n h u σ z) s :=
    (tsCl_hasDerivAt hn hh hsupp h2 s σ z).deriv.symm
  rw [hderiv]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hmem : ∀ᶠ u in 𝓝 s, u ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
  filter_upwards [hmem] with u hu
  exact Work.OddVolterra.WinData.Tcl_eq_ThetaM hu hσ (le_of_lt hz)

lemma xsCl_eq (hn : 1 ≤ n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (h1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : s ∈ Set.Ioo Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi) :
    XsCl n h s = deriv (fun u : ℝ =>
      Work.OddVolterra.Xi n h u + ∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
        Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ)) s := by
  rw [XsCl]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hmem : ∀ᶠ u in 𝓝 s, u ∈ Set.Icc Work.OddVolterra.WinData.wLo Work.OddVolterra.WinData.wHi :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) (fun u hu => ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
  filter_upwards [hmem] with u hu
  exact Work.OddVolterra.WinData.Xcl_eq hu

end

end Work.OddVolterra.Existence
