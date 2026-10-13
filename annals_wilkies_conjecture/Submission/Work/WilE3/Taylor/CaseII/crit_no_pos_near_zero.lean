import Mathlib
import Submission.Work.WilE3.Taylor.criticalValueSeparation

set_option autoImplicit false

namespace Work.WilE3.Taylor.CaseII

open scoped Topology

/-- **No positive critical values near a zero of an analytic function.**

Let `Φ : ℝᵏ → ℝ` be real analytic everywhere and let `z` be a zero of `Φ`.  Then near `z` every
critical point `w` of `Φ` (that is, `fderiv ℝ Φ w = 0`) satisfies `Φ w ≤ 0`.

This is the "no non-zero critical value accumulates at a zero" phenomenon for analytic functions.
Suppose the conclusion failed: then there are critical points `aₙ → z` with `Φ aₙ > 0`, i.e. `z`
is a cluster point of the basic semianalytic set `{∇Φ = 0} ∩ {Φ > 0}`.  By Łojasiewicz analytic
curve selection there is then a real analytic arc `γ` through `z` with `∇Φ (γ s) = 0` and
`Φ (γ s) > 0` for all small `s > 0`.  But the one-variable function `s ↦ Φ (γ s)` is analytic at
`0`, vanishes at `0` (since `γ 0 = z` is a zero of `Φ`), and — by the chain rule, because `γ` runs
in the critical set of `Φ` — has vanishing derivative on `(0, ε)`; hence it is constant there and
equals its value at `0`, namely `0`, contradicting `Φ (γ s) > 0`.

This is exactly the argument of `Work.WilE3.Taylor.criticalValueSeparation`, with the
nonnegativity hypothesis replaced by the *conclusion* `Φ aₙ > 0` that is forced by the failure of
the present claim. -/
theorem crit_no_pos_near_zero {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {z : Fin k → ℝ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hz : Φ z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : Fin k → ℝ, dist w z < ρ → fderiv ℝ Φ w = 0 → Φ w ≤ 0 := by
  classical
  by_contra hcon
  -- counterexample points: critical for `Φ`, with `Φ > 0`, accumulating at `z`
  have hbad : ∀ n : ℕ, ∃ w : Fin k → ℝ,
      dist w z < 1 / (n + 1) ∧ fderiv ℝ Φ w = 0 ∧ 0 < Φ w := by
    intro n
    by_contra h
    exact hcon ⟨1 / (n + 1), by positivity, fun w hw hwf => by
      by_contra hle
      exact h ⟨w, hw, hwf, not_le.mp hle⟩⟩
  choose a had haw haΦ using hbad
  have ha_tendsto : Filter.Tendsto a Filter.atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (had n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- `z` is a cluster point of the semianalytic set `{∇Φ = 0, Φ > 0}`
  have hzcl : z ∈ closure (WilkiesDesign.CG.C4a.BasicSA (critSqFun Φ) (fun _ : Fin 1 => Φ)) := by
    refine mem_closure_of_tendsto ha_tendsto ?_
    filter_upwards with n
    exact ⟨critSqFun_eq_zero_iff.mpr (haw n), fun _ => haΦ n⟩
  -- analytic curve selection
  obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
    Work.WilE3.Loj.curveSel_full k 1 (critSqFun Φ) (fun _ : Fin 1 => Φ) z
      (analyticAt_critSqFun hΦ z) (fun _ => hΦ z) hzcl
  have hcrit : ∀ s ∈ Set.Ioo (0:ℝ) ε, critSqFun Φ (γ s) = 0 := fun s hs => (hγε s hs).1
  have hpos : ∀ s ∈ Set.Ioo (0:ℝ) ε, 0 < Φ (γ s) := fun s hs => (hγε s hs).2 0
  -- `γ` is differentiable near `0`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ → DifferentiableAt ℝ γ s := by
    have hev : ∀ᶠ s in 𝓝 (0:ℝ), DifferentiableAt ℝ γ s :=
      hγan.eventually_analyticAt.mono fun s hs => hs.differentiableAt
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ, hδpos, fun s hs => hδ (by simpa [Real.dist_eq] using hs)⟩
  set s₁ : ℝ := min ε δ / 2 with hs₁def
  have hs₁pos : 0 < s₁ := by rw [hs₁def]; have := lt_min hεpos hδpos; linarith
  have hs₁ε : s₁ < ε := by rw [hs₁def]; linarith [min_le_left ε δ]
  have hs₁δ : s₁ < δ := by rw [hs₁def]; linarith [min_le_right ε δ]
  -- the one-variable function `s ↦ Φ (γ s)`
  set hh : ℝ → ℝ := fun s => Φ (γ s) with hhdef
  have hgan : AnalyticAt ℝ hh 0 := by
    have h1 : AnalyticAt ℝ Φ (γ 0) := by rw [hγ0]; exact hΦ z
    have h2 : AnalyticAt ℝ (Φ ∘ γ) 0 := h1.comp hγan
    rw [hhdef]
    exact h2
  have hdiffAt : ∀ c ∈ Set.Icc (0:ℝ) s₁, DifferentiableAt ℝ hh c := by
    intro c hc
    rcases eq_or_lt_of_le hc.1 with hc0 | hc0
    · rw [← hc0]; exact hgan.differentiableAt
    · have hcδ : |c| < δ := by
        rw [abs_of_pos hc0]; exact lt_of_le_of_lt hc.2 hs₁δ
      have hγc : DifferentiableAt ℝ γ c := hδ c hcδ
      have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
      have h3 : DifferentiableAt ℝ (Φ ∘ γ) c := hΦc.comp c hγc
      rw [hhdef]
      exact h3
  have hdiffOnIcc : DifferentiableOn ℝ hh (Set.Icc 0 s₁) := fun c hc =>
    (hdiffAt c hc).differentiableWithinAt
  have hcont : ContinuousOn hh (Set.Icc 0 s₁) := hdiffOnIcc.continuousOn
  have hdiffOn : DifferentiableOn ℝ hh (Set.Ioo (0:ℝ) s₁) := fun c hc =>
    (hdiffAt c ⟨hc.1.le, hc.2.le⟩).differentiableWithinAt
  -- the chain rule: `deriv hh` vanishes on `(0, s₁)`, because `γ` runs in the critical set
  have hderiv0 : ∀ c ∈ Set.Ioo (0:ℝ) s₁, deriv hh c = 0 := by
    intro c hc
    have hcε : c ∈ Set.Ioo (0:ℝ) ε := ⟨hc.1, lt_trans hc.2 hs₁ε⟩
    have hcδ : |c| < δ := by
      rw [abs_of_pos hc.1]; exact lt_of_lt_of_le hc.2 (le_of_lt hs₁δ)
    have hγc : DifferentiableAt ℝ γ c := hδ c hcδ
    have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
    have hfc : fderiv ℝ Φ (γ c) = 0 := critSqFun_eq_zero_iff.mp (hcrit c hcε)
    have h1 : HasFDerivAt Φ (fderiv ℝ Φ (γ c)) (γ c) := hΦc.hasFDerivAt
    have h2 : HasDerivAt γ (deriv γ c) c := hγc.hasDerivAt
    have h3 : HasDerivAt (Φ ∘ γ) ((fderiv ℝ Φ (γ c)) (deriv γ c)) c :=
      h1.comp_hasDerivAt c h2
    have h4 : HasDerivAt hh ((fderiv ℝ Φ (γ c)) (deriv γ c)) c := by
      rw [hhdef]; exact h3
    rw [hfc] at h4
    simpa using h4.deriv
  -- mean value theorem on `[0, s₁]`: `hh s₁ = hh 0`
  obtain ⟨c, hcmem, hceq⟩ := exists_deriv_eq_slope hh hs₁pos hcont hdiffOn
  have hzero : (hh s₁ - hh 0) / (s₁ - 0) = 0 := by rw [← hceq, hderiv0 c hcmem]
  have hval : hh s₁ = hh 0 := by
    rw [div_eq_zero_iff] at hzero
    rcases hzero with h | h
    · linarith
    · exact absurd h (by linarith)
  have hh0 : hh 0 = 0 := by simp [hhdef, hγ0, hz]
  have hpos₁ : 0 < hh s₁ := by
    have := hpos s₁ ⟨hs₁pos, hs₁ε⟩
    simpa [hhdef] using this
  -- contradiction: `hh s₁ = 0` but `hh s₁ > 0`
  rw [hval, hh0] at hpos₁
  exact lt_irrefl 0 hpos₁

end Work.WilE3.Taylor.CaseII
