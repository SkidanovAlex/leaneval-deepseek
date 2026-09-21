import Mathlib
import Submission.Work.OddVolterra.Existence.window_deriv_close_core
import Submission.Work.OddCurveB.Step2.StateWide
import Submission.Work.OddCurveB.Step2.RhsWide
import Submission.Work.OddCurveB.Step2.XsclWide
import Submission.Work.OddCurveB.Step2.ClampedWide

/-!
# `C¹`-closeness of the odd transition-window solution on the wide window `[1/4, 9/10]`

This is `Work.OddVolterra.Existence.window_deriv_close_core` (`window_deriv_close_core.lean`)
with the slope window widened from `[7/10, 19/20]` to `[1/4, 19/20]`: the conclusion is on the
*open* window `Ioo (1/4) (9/10)` (the endpoint `s = 1/4` is handled by the caller, where the state
is known to be smooth at `1/4`), and the state-closeness input is this chapter's wide state core
`Work.OddCurveB.Step2.w_window_state_close_wide`, which needs the extra hypothesis
`ContinuousOn Z (Icc (1/4) 1)` (true whenever `Z` is `C^∞` on `(0,∞)`, which is the case in the
application).  All the other ingredients (`w_gscl_data`, `w_rhs_diff`, `w_xscl_close`, the
`WinData` clamped-data estimates, `Estimates.linearization`, `fderiv_godd_close_box`,
`deriv_from_solution_linearized`) are already stated on the wide window.
-/

namespace Work.OddCurveB.Step2

open MeasureTheory Set Filter
open Work.OddVolterra
open Work.OddVolterra.Existence
open Work.OddVolterra.Existence.WDC
open scoped Topology ContDiff Interval

noncomputable section

def winRHS (n : ℕ) (g : ℝ → ℝ) (c : ℝ → St) (s : ℝ) : St :=
  - GsCl n g s (c s) - WinData.Tcl n g s s (c s) +
    (∫ σ in s..(19 / 20 : ℝ), TsCl n g s σ (c σ)) + XsCl n g s

/-- **The differentiated clamped base identity, separated.**  For the base state `baseState` and
the linearisation `A` of the unperturbed state datum, the left-hand side of the differentiated
clamped identity is the right-hand side `winRHS` of the linearised equation. -/
theorem w_winRHS_base (n : ℕ) (hn : 1 ≤ n) (A : ℝ → St ≃L[ℝ] St)
    (hA : ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      (A s : St →L[ℝ] St) = fderiv ℝ (fun z => Godd n 0 s z) (baseState s)) :
    ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), (A s) (deriv baseState s) = winRHS n 0 baseState s := by
  intro s hs
  have hsW : s ∈ Set.Icc WinData.wLo WinData.wHi := by
    rw [WinData.wLo, WinData.wHi]
    exact ⟨by linarith [hs.1], hs.2⟩
  have hb := (WinData.clamped_base_identity n hn).2 s ⟨by linarith [hs.1], hs.2⟩
  have hjet0 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x| ≤ 1 / 100 :=
    WDC.hjet_zero_wdc (by norm_num)
  have e1 : deriv (fun u : ℝ => WinData.Gcl n 0 u (baseState s)) s
      = GsCl n 0 s (baseState s) :=
    (gsCl_hasDerivAt (n := n) (h := 0) hn contDiff_const WDC.support_zero_wdc hjet0 s
      (baseState s)).deriv
  have e4 : fderiv ℝ (fun z : St => WinData.Gcl n 0 s z) (baseState s) = (A s : St →L[ℝ] St) := by
    have hev : (fun z : St => WinData.Gcl n 0 s z) =ᶠ[𝓝 (baseState s)]
        (fun z : St => Godd n 0 s z) := by
      filter_upwards [Metric.ball_mem_nhds (baseState s) (show (0 : ℝ) < 1 / 2 by norm_num)]
        with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact WinData.Gcl_eq_Godd hsW (le_of_lt hz)
    rw [hev.fderiv_eq, ← hA s hs]
  have e5 : (∫ σ in s..(19 / 20 : ℝ),
        deriv (fun u : ℝ => WinData.Tcl n 0 u σ (baseState σ)) s)
      = ∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ) := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    exact (tsCl_hasDerivAt (n := n) (h := 0) hn contDiff_const WDC.support_zero_wdc hjet0 s σ
      (baseState σ)).deriv
  have e3 : deriv (fun u : ℝ => WinData.Xcl n 0 u) s = XsCl n 0 s := rfl
  rw [e1, e4, e5, e3] at hb
  have h1 : (A s) (deriv baseState s) =
      (-WinData.Tcl n 0 s s (baseState s) +
        (∫ σ in s..(19 / 20 : ℝ), TsCl n 0 s σ (baseState σ))) + XsCl n 0 s
        - GsCl n 0 s (baseState s) := by
    rw [← hb]; abel
  rw [winRHS, h1]; abel

/-- **L-2 core lemma.**  The `C¹`-closeness (NRZ Lemma 8) of the odd transition-window solution:
every smooth solution `Z` of the paper's system in the `C^{n+3}` bump class which agrees with the
ball's state beyond `9/10` has `deriv Z` within `C ε` of `deriv baseState` on `[7/10, 9/10]`.

The proof is the linearised comparison: on the window `[7/10, 19/20]` the given `Z` solves the
*clamped* system (`clamped_solves_of_paper`), whose linearisation about the base state is
`A s = D_z 𝐆 n 0 s (baseState s)`.  The difference of the two right-hand sides is `O(ε)` by
`rhs_diff`, the defect `‖D_z 𝐆 n h s (Z s) - A s‖` is `O(ε)` by `fderiv_godd_close_box` and the
`C⁰`-closeness `window_state_close_core`, and the perturbed inverse `solve_near_equiv` then bounds
the solution of the linearised equation; `deriv_from_solution_linearized` identifies it with
`deriv Z`. -/
theorem w_window_deriv_close_core (n : ℕ) (hn : 1 ≤ n) :
    ∃ C ε₁ : ℝ, 0 < C ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (Z : ℝ → Work.OddVolterra.St) (ε : ℝ), 0 < ε → ε ≤ ε₁ →
        Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) →
        ContinuousOn Z (Set.Icc (1 / 4 : ℝ) 1) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (1 / 4 : ℝ) 1,
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2) →
        ∀ s ∈ Set.Ioo (1 / 4 : ℝ) (9 / 10 : ℝ),
          dist (deriv Z s) (deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s)
            ≤ C * ε
:= by
  -- the `C⁰`-closeness of an arbitrary solution
  obtain ⟨Kc, εc, hKcpos, hεcpos, hεc100, hclose⟩ := w_window_state_close_core n hn
  -- the closeness of the derivative of the clamped source
  obtain ⟨CX, hCXnn, hXscl⟩ := w_xscl_close n hn
  -- the `O(ε)` bound on the difference of the right-hand sides
  obtain ⟨Mrhs, hMrhsnn, hRdiff⟩ := w_rhs_diff n hn Kc hKcpos.le CX hCXnn hXscl
  -- the linearisation of the unperturbed datum about the base solution
  obtain ⟨A, B, hBpos, hAeq, _hAcont, hAinv⟩ :=
    Work.OddExistence.Estimates.linearization n hn (a := (1 / 4 : ℝ)) (b := (19 / 20 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  -- the closeness of the differential of the datum
  obtain ⟨Cg, hCgpos, hCgclose⟩ :=
    WinData.fderiv_godd_close_box n hn (a := (1 / 4 : ℝ)) (b := (19 / 20 : ℝ))
      (ρ := (9 / 20 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- the base state is smooth, and its derivative is bounded on the window
  have hcb : ContDiff ℝ (⊤ : ℕ∞) (baseState : ℝ → St) :=
    contDiff_baseState_comp.comp
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : St))))
  have hcd : Continuous (deriv (baseState : ℝ → St)) := hcb.continuous_deriv (by simp)
  obtain ⟨S, hSpos, hSbd⟩ : ∃ S : ℝ, 0 < S ∧
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ‖deriv (baseState : ℝ → St) s‖ ≤ S := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcd.continuousOn
      (f := deriv (baseState : ℝ → St))
    exact ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
      fun s hs => le_trans (hC s hs) (le_max_left _ _)⟩
  obtain ⟨KK, hKKdef⟩ : ∃ K : ℝ, K = 2 * B * (Cg * (Kc + 1) * S + Mrhs) := ⟨_, rfl⟩
  have hKKpos : 0 < KK := by
    rw [hKKdef]
    have h1 : 0 < Cg * (Kc + 1) * S := mul_pos (mul_pos hCgpos (by linarith)) hSpos
    have h2 : 0 < Cg * (Kc + 1) * S + Mrhs := by linarith [h1, hMrhsnn]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hBpos) h2
  have hε₁pos : 0 < min (1 / 100) (min εc (min (9 / (20 * Kc)) (1 / (2 * B * Cg * (Kc + 1))))) := by
    refine lt_min (by norm_num) (lt_min hεcpos (lt_min ?_ ?_))
    · positivity
    · positivity
  refine ⟨KK, _, hKKpos, hε₁pos, min_le_left _ _, ?_⟩
  intro h Z ε hεpos hεε₁ hbump hZsm hZcont0 heq htail hball s hs
  -- ## unpacking the hypotheses
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hbump.1
  have hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) :=
    fun x hx => ⟨le_of_lt (hbump.2.1 hx).1, le_of_lt (hbump.2.1 hx).2⟩
  have hjet : ∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ ε :=
    fun k hk x => hbump.2.2.1 k hk x
  have hε100 : ε ≤ 1 / 100 := le_trans hεε₁ (min_le_left _ _)
  have hεεc : ε ≤ εc := le_trans hεε₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε9 : ε ≤ 9 / (20 * Kc) :=
    le_trans hεε₁ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεB : ε ≤ 1 / (2 * B * Cg * (Kc + 1)) :=
    le_trans hεε₁ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (by omega) x) hε100
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (by omega) x) hε100
  have hjetn2 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ ε :=
    fun k hk x => hjet k (by omega) x
  -- ## the smallness conditions on `ε`
  have hKc9 : Kc * ε ≤ 9 / 20 := by
    have h1 : Kc * ε ≤ Kc * (9 / (20 * Kc)) := mul_le_mul_of_nonneg_left hε9 hKcpos.le
    have h2 : Kc * (9 / (20 * Kc)) = 9 / 20 := by field_simp
    linarith [h1, h2]
  have hκB : B * (Cg * (Kc + 1) * ε) ≤ 1 / 2 := by
    have h1 : Cg * (Kc + 1) * ε ≤ Cg * (Kc + 1) * (1 / (2 * B * Cg * (Kc + 1))) :=
      mul_le_mul_of_nonneg_left hεB (by positivity)
    have h2 : Cg * (Kc + 1) * (1 / (2 * B * Cg * (Kc + 1))) = 1 / (2 * B) := by field_simp
    have h3 : B * (Cg * (Kc + 1) * ε) ≤ B * (1 / (2 * B)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hBpos.le
    have h4 : B * (1 / (2 * B)) = 1 / 2 := by field_simp
    linarith [h3, h4]
  -- ## the state closeness on the whole window
  have hZdist : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), dist (Z u) (baseState u) ≤ Kc * ε := by
    intro u hu
    by_cases h9 : u ≤ 9 / 10
    · exact hclose h Z ε hεpos hεεc hbump hZsm hZcont0 heq htail hball u ⟨hu.1, h9⟩
    · push_neg at h9
      rw [htail u (le_of_lt h9), dist_self]
      exact mul_nonneg hKcpos.le hεpos.le
  have hZcont : ContinuousOn Z (Set.Icc (1 / 4 : ℝ) (19 / 20)) :=
    hZcont0.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  have hsol : ∀ u ∈ Set.Ioc (1 / 4 : ℝ) (19 / 20), WinData.Gcl n h u (Z u) =
      (∫ σ in u..WinData.wHi, WinData.Tcl n h u σ (Z σ)) + WinData.Xcl n h u :=
    fun u hu => w_clamped_solves_of_paper (n := n) (Z := Z) hn hh hsupp hsmall1 hZsm hZcont0
      heq htail hball hu
  have hZm9 : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      Z u ∈ Metric.closedBall (baseState u) (9 / 20) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hZdist u hu
    rw [dist_eq_norm] at h1
    linarith [h1, hKc9]
  -- ## the defect of the differential
  have hJκ : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ‖fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u) - (A u : St →L[ℝ] St)‖
        ≤ Cg * (Kc + 1) * ε := by
    intro u hu
    have huW : u ∈ Set.Icc WinData.wLo WinData.wHi := by
      rw [WinData.wLo, WinData.wHi]
      exact ⟨by linarith [hu.1], hu.2⟩
    have hAcl : fderiv ℝ (fun w : St => Godd n h u w) (Z u) =
        fderiv ℝ (fun w : St => WinData.Gcl n h u w) (Z u) := by
      have hev : (fun w : St => WinData.Gcl n h u w) =ᶠ[𝓝 (Z u)]
          (fun w : St => Godd n h u w) := by
        filter_upwards [Metric.ball_mem_nhds (Z u) (show (0 : ℝ) < 1 / 20 by norm_num)]
          with w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have h2 := hZm9 u hu
        rw [Metric.mem_closedBall, dist_eq_norm] at h2
        refine WinData.Gcl_eq_Godd huW ?_
        rw [WinData.wRho]
        have h3 : ‖w - baseState u‖ ≤ ‖w - Z u‖ + ‖Z u - baseState u‖ := by
          have ht := dist_triangle w (Z u) (baseState u)
          rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
        linarith [h3, hw, h2]
      exact hev.fderiv_eq.symm
    have hmain := hCgclose h hh hsupp ε hεpos hε100 hjetn2 u hu (Z u) (hZm9 u hu)
    rw [← hAeq u hu, hAcl] at hmain
    have h2 : ‖Z u - baseState u‖ ≤ Kc * ε := by
      have h1 := hZdist u hu; rwa [dist_eq_norm] at h1
    have h3 : Cg * ‖Z u - baseState u‖ ≤ Cg * (Kc * ε) :=
      mul_le_mul_of_nonneg_left h2 hCgpos.le
    have h4 : Cg * (Kc * ε) + Cg * ε = Cg * (Kc + 1) * ε := by ring
    linarith [hmain, h3, h4]
  -- ## the base identity in the separated form
  have hv0 : ∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      (A u) (deriv baseState u) = winRHS n 0 baseState u :=
    w_winRHS_base n hn A hAeq
  -- ## the pointwise solution of the linearised equation with its bound
  have hVex : ∀ u, u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) → ∃ v : St,
      (fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u)) v = winRHS n h Z u ∧
      ‖v - deriv baseState u‖ ≤ KK * ε := by
    intro u hu
    have hδs : ‖winRHS n h Z u - winRHS n 0 baseState u‖ ≤ Mrhs * ε :=
      hRdiff h ε hh hεpos hε100 hjet hsupp hKc9 Z hZcont hZdist u hu
    obtain ⟨v, hv1, hv2⟩ := Work.VolterraLong.C1.solve_near_equiv (E := St)
      (A := A u) (J := fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u))
      (B := B) (κ := Cg * (Kc + 1) * ε) (δ := Mrhs * ε)
      hBpos (hAinv u hu) (hJκ u hu) hκB (R := winRHS n h Z u) (R₀ := winRHS n 0 baseState u)
      (v₀ := deriv baseState u) (hv0 u hu) hδs
    refine ⟨v, hv1, ?_⟩
    have hS' := hSbd u hu
    have hκnn : 0 ≤ Cg * (Kc + 1) * ε := by positivity
    have hb1 : Cg * (Kc + 1) * ε * ‖deriv baseState u‖ ≤ Cg * (Kc + 1) * ε * S :=
      mul_le_mul_of_nonneg_left hS' hκnn
    have hb2 : Cg * (Kc + 1) * ε * ‖deriv baseState u‖ + Mrhs * ε ≤
        (Cg * (Kc + 1) * S + Mrhs) * ε := by
      have hb3 : Cg * (Kc + 1) * ε * S + Mrhs * ε = (Cg * (Kc + 1) * S + Mrhs) * ε := by ring
      linarith [hb1, hb3]
    have hb4 := mul_le_mul_of_nonneg_left hb2 (by linarith [hBpos] : (0 : ℝ) ≤ 2 * B)
    have hb5 : 2 * B * ((Cg * (Kc + 1) * S + Mrhs) * ε) = KK * ε := by rw [hKKdef]; ring
    linarith [hv2, hb4, hb5]
  obtain ⟨V, hV1, hV2⟩ : ∃ V : ℝ → St,
      (∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        (fderiv ℝ (fun w => WinData.Gcl n h u w) (Z u)) (V u) = winRHS n h Z u) ∧
      (∀ u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ‖V u - deriv baseState u‖ ≤ KK * ε) := by
    refine ⟨fun u => if hu : u ∈ Set.Icc (1 / 4 : ℝ) (19 / 20)
        then Classical.choose (hVex u hu) else 0, ?_, ?_⟩
    · intro u hu
      simp only [dif_pos hu]
      exact (Classical.choose_spec (hVex u hu)).1
    · intro u hu
      simp only [dif_pos hu]
      exact (Classical.choose_spec (hVex u hu)).2
  -- ## `deriv Z` solves the linearised equation on every window `[a', 19/20]`, `a' > 1/4`
  have hderiv : ∀ a' : ℝ, (1 / 4 : ℝ) < a' → a' ≤ 19 / 20 →
      ∀ u ∈ Set.Icc a' (19 / 20 : ℝ),
        HasDerivWithinAt Z (V u) (Set.Icc a' (19 / 20 : ℝ)) u := by
    intro a' ha' ha'b
    exact Work.VolterraLong.deriv_from_solution_linearized (E := St)
      (a := a') (b := (19 / 20 : ℝ)) (hab := by linarith)
      (G := fun u (z : St) => WinData.Gcl n h u z)
      (Θ := fun u (σ : ℝ) (z : St) => WinData.Tcl n h u σ z)
      (Ξ := fun u : ℝ => WinData.Xcl n h u)
      (Gs := fun u (z : St) => GsCl n h u z)
      (Θs := fun u (σ : ℝ) (z : St) => TsCl n h u σ z)
      (Ξs := fun u : ℝ => XsCl n h u)
      (Z := Z) (V := V) (A := A) (B := B) (κ := Cg * (Kc + 1) * ε)
      hBpos
      (fun s hs => hAinv s ⟨le_trans ha'.le hs.1, hs.2⟩)
      (hZcont.mono (Set.Icc_subset_Icc ha'.le le_rfl))
      hκB
      (fun s hs => hsol s ⟨lt_of_lt_of_le ha' hs.1, hs.2⟩)
      (gcl_continuous (n := n) hn hh hsupp hsmall2)
      (tcl_continuous (n := n) hn hh hsupp hsmall2)
      (xcl_continuous (n := n) hn hh hsupp hsmall1)
      (fun u _ z => gsCl_hasDerivAt (n := n) hn hh hsupp hsmall2 u z)
      (gsCl_continuous (n := n) hn hh hsupp hsmall2)
      (fun u _ σ z => tsCl_hasDerivAt (n := n) hn hh hsupp hsmall2 u σ z)
      (tsCl_continuous (n := n) hn hh hsupp hsmall2)
      (fun u => xsCl_hasDerivAt (n := n) hn hh hsupp hsmall1 u)
      (xsCl_continuous (n := n) hn hh hsupp hsmall1)
      (fun u _ => ((gcl_contDiff (n := n) hh hsupp hsmall2).comp
          (contDiff_prodMk_right (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (e₀ := u))).differentiable
          (by simp) |>.differentiableAt)
      (fun s hs => hJκ s ⟨le_trans ha'.le hs.1, hs.2⟩)
      (fun s hs => hV1 s ⟨le_trans ha'.le hs.1, hs.2⟩)
  -- ## conclusion
  have hmain : ∀ u ∈ Set.Ioo (1 / 4 : ℝ) (19 / 20),
      dist (deriv Z u) (deriv (baseState : ℝ → St) u) ≤ KK * ε := by
    intro u hu
    set a' : ℝ := ((1 / 4 : ℝ) + u) / 2 with ha'def
    have ha' : (1 / 4 : ℝ) < a' := by rw [ha'def]; linarith [hu.1]
    have hau : a' ≤ u := by rw [ha'def]; linarith [hu.1]
    have ha'b : a' ≤ 19 / 20 := le_trans hau hu.2.le
    have huI : u ∈ Set.Icc a' (19 / 20 : ℝ) := ⟨hau, hu.2.le⟩
    have hau' : a' < u := by rw [ha'def]; linarith [hu.1]
    have hd : HasDerivAt Z (V u) u :=
      (hderiv a' ha' ha'b u huI).hasDerivAt (Icc_mem_nhds hau' hu.2)
    rw [hd.deriv, dist_eq_norm]
    exact hV2 u ⟨le_trans ha'.le huI.1, huI.2⟩
  exact hmain s ⟨hs.1, by linarith [hs.2]⟩



end

end Work.OddCurveB.Step2
