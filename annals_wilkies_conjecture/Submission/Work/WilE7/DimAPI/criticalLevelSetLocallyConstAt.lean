import Mathlib
import Submission.Work.WilE7.AuxLC.criticalLevelSetLocallyConst
import Submission.Work.WilE9G.Sard.analyticLevelSetChartLocal

namespace Work.WilE7.DimAPI

open Filter
open scoped Topology

/-- **Local constancy along a regular level set, local-analytic version.**

If `g` and `F` are analytic *at `p`* (not globally), the differential of `g` at `p` is
surjective, and `dF` vanishes on `ker dg` along the zero set of `g` near `p`, then `F` is constant
on the zero set of `g` near `p`.  Uses the local analytic chart of the level set
(`Work.WilE9G.Sard.analyticLevelSetChartLocal`): the fibre `{g = g p}` is, near `p`, the analytic
image of a neighbourhood of `0` in `ker (fderiv ℝ g p)`, and `F` restricted to this image has
vanishing derivative, hence is constant. -/
theorem criticalLevelSetLocallyConstAt {n k : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (F : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ)
    (hg : AnalyticAt ℝ g p) (hF : AnalyticAt ℝ F p)
    (hsurj : (fderiv ℝ g p).range = ⊤)
    (hcrit : ∀ᶠ y in nhds p, g y = 0 → ∀ v, (fderiv ℝ g y) v = 0 → (fderiv ℝ F y) v = 0) :
    ∀ᶠ y in nhds p, g y = 0 → F y = F p := by
  by_cases hgp : g p = 0
  · -- main case: `p` lies on the zero set
    obtain ⟨C, γ, V, U, _hCid, hVopen, hUopen, h0V, hpU, hγ0, hγan, _hγU, hglevel, _hCγ, hγC⟩ :=
      Work.WilE9G.Sard.analyticLevelSetChartLocal g p hg hsurj
    -- `F ∘ γ` is analytic at `0`
    have hHan : AnalyticAt ℝ (fun v => F (γ v)) 0 := by
      have h := AnalyticAt.comp
        (g := fun y => F y) (f := γ) (x := (0 : (fderiv ℝ g p).ker))
        (show AnalyticAt ℝ (fun y => F y) (γ 0) from by rw [hγ0]; exact hF) hγan
      simpa only [Function.comp_def] using h
    -- `γ` is differentiable near `0`
    have hγdiff : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), DifferentiableAt ℝ γ v :=
      hγan.eventually_analyticAt.mono fun v hv => hv.differentiableAt
    -- `γ` tends to `p` at `0`
    have hγtend : Tendsto γ (𝓝 (0 : (fderiv ℝ g p).ker)) (𝓝 p) := by
      have h : Tendsto γ (𝓝 (0 : (fderiv ℝ g p).ker)) (𝓝 (γ 0)) := hγan.continuousAt
      rw [hγ0] at h
      exact h
    -- the hypothesis holds at `γ v` for `v` near `0`
    have hγS : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        g (γ v) = 0 → ∀ w, (fderiv ℝ g (γ v)) w = 0 → (fderiv ℝ F (γ v)) w = 0 :=
      hγtend.eventually hcrit
    -- `g` and `F` are differentiable at `γ v` for `v` near `0` (analyticity at `p` is local)
    have hgd : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), DifferentiableAt ℝ g (γ v) :=
      (hγtend.eventually hg.eventually_analyticAt).mono fun _ hv => hv.differentiableAt
    have hFd : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), DifferentiableAt ℝ F (γ v) :=
      (hγtend.eventually hF.eventually_analyticAt).mono fun _ hv => hv.differentiableAt
    -- `g ∘ γ` has zero derivative on `V`
    have hgc : ∀ v ∈ V, fderiv ℝ (fun w => g (γ w)) v = 0 := by
      intro v hv
      have hev : (fun w => g (γ w)) =ᶠ[𝓝 v] (fun _ => g p) :=
        Filter.eventually_of_mem (hVopen.mem_nhds hv) fun w hw => hglevel w hw
      rw [hev.fderiv_eq]
      exact (hasFDerivAt_const (g p) v).fderiv
    -- derivative of `F ∘ γ` vanishes near `0`
    have hzero : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        fderiv ℝ (fun w => F (γ w)) v = 0 := by
      filter_upwards [hγS, hVopen.mem_nhds h0V, hγdiff, hgd, hFd] with v hvS hvV hvdiff hgdv hFdv
      have hvd : fderiv ℝ (fun w => g (γ w)) v = 0 := hgc v hvV
      have h1 : fderiv ℝ (fun w => g (γ w)) v
          = (fderiv ℝ g (γ v)).comp (fderiv ℝ γ v) := by
        simpa only [Function.comp_def] using
          fderiv_comp (𝕜 := ℝ) v (f := γ) (g := fun y => g y) hgdv hvdiff
      rw [h1] at hvd
      have h2 : fderiv ℝ (fun w => F (γ w)) v
          = (fderiv ℝ F (γ v)).comp (fderiv ℝ γ v) := by
        simpa only [Function.comp_def] using
          fderiv_comp (𝕜 := ℝ) v (f := γ) (g := fun y => F y) hFdv hvdiff
      rw [h2]
      refine ContinuousLinearMap.ext fun e => ?_
      have h3 : (fderiv ℝ g (γ v)) ((fderiv ℝ γ v) e) = 0 := by
        have h := congrArg (fun (M : (fderiv ℝ g p).ker →L[ℝ] (Fin k → ℝ)) => M e) hvd
        simpa [ContinuousLinearMap.comp_apply] using h
      have h4 := hvS (by rw [hglevel v hvV, hgp]) ((fderiv ℝ γ v) e) h3
      simpa [ContinuousLinearMap.comp_apply] using h4
    -- `F ∘ γ` is differentiable near `0`
    have hdiffH : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker),
        DifferentiableAt ℝ (fun w => F (γ w)) v :=
      hHan.eventually_analyticAt.mono fun _ hv => hv.differentiableAt
    -- `F ∘ γ` is constant near `0`
    have hconst : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ g p).ker), F (γ v) = F p := by
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hdiffH.and hzero)
      filter_upwards [Metric.ball_mem_nhds (0 : (fderiv ℝ g p).ker) hr] with v hv
      have hc := IsOpen.is_const_of_fderiv_eq_zero (Metric.isOpen_ball)
        (convex_ball (0 : (fderiv ℝ g p).ker) r).isPreconnected
        (fun z hz => (hsub hz).1.differentiableWithinAt)
        (fun z hz => (hsub hz).2) (Metric.mem_ball_self hr) hv
      simpa [hγ0] using hc.symm
    -- transport back to `p` along the projection `C`
    let σ : (Fin n → ℝ) → (fderiv ℝ g p).ker := fun y => C (y - p)
    have hσcont : Continuous σ :=
      C.continuous.comp (continuous_id.sub continuous_const)
    have hσp : σ p = 0 := by
      show C (p - p) = 0
      simp
    have hσev : ∀ᶠ y in 𝓝 p, F (γ (σ y)) = F p := by
      have hpre : σ ⁻¹' {v : (fderiv ℝ g p).ker | F (γ v) = F p} ∈ 𝓝 p := by
        apply hσcont.continuousAt.preimage_mem_nhds
        rw [hσp]
        exact hconst
      filter_upwards [hpre] with y hy
      exact hy
    filter_upwards [hσev, hUopen.mem_nhds hpU] with y hy hUy
    intro hgy
    have hgyp : g y = g p := by rw [hgy, hgp]
    have hγσy : γ (σ y) = y := by
      simpa only [σ] using hγC y hUy hgyp
    rw [hγσy] at hy
    exact hy
  · -- `p` is not on the zero set: the statement is vacuous near `p`
    have hne : ∀ᶠ y in 𝓝 p, g y ≠ 0 :=
      hg.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hgp)
    filter_upwards [hne] with y hy hgy
    exact absurd hgy hy

end Work.WilE7.DimAPI
