import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Set Filter Metric
open scoped Topology

/-- **Hurwitz's non-vanishing theorem.** Let `U ⊆ ℂ` be open and preconnected, let `v n` be a
sequence of holomorphic functions on `U` none of which has a zero on `U`, and suppose `v n`
converges to `g` locally uniformly on `U`. Then `g` either vanishes nowhere on `U` or vanishes
identically on `U`.

The proof does not use the argument principle.  If `g` is not locally identically zero and had a
zero at `z₀ ∈ U`, then on a small circle around `z₀` the functions `v n` would be bounded below by
`m/2` (where `m > 0` is the minimum of `|g|` on that circle), so the mean value property
`Real.circleAverage (log ‖v n ·‖) z₀ r = log ‖v n z₀‖` (valid because `v n` is zero-free there)
would give `log ‖v n z₀‖ ≥ log (m/2)` for all large `n`, contradicting `v n z₀ → g z₀ = 0`. -/
theorem hurwitz_nonvanishing {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (v : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (hv : ∀ n, DifferentiableOn ℂ (v n) U)
    (hvn : ∀ n, ∀ z ∈ U, v n z ≠ 0)
    (h : TendstoLocallyUniformlyOn v g Filter.atTop U) :
    (∀ z ∈ U, g z ≠ 0) ∨ ∀ z ∈ U, g z = 0 := by
  have hg_diff : DifferentiableOn ℂ g U :=
    h.differentiableOn (Eventually.of_forall hv) hU
  have hg_an : AnalyticOnNhd ℂ g U := hg_diff.analyticOnNhd hU
  by_cases hzero : ∀ z ∈ U, g z = 0
  · exact Or.inr hzero
  · refine Or.inl fun z₀ hz₀ hgz₀ => ?_
    rcases (hg_an z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with hloc | hloc
    · exact hzero fun z hz =>
        (hg_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hloc) hz
    · -- `hloc : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0`
      obtain ⟨ρ, hρpos, hρU⟩ : ∃ ρ > 0, ball z₀ ρ ⊆ U := by
        obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
        exact ⟨ρ, hρ, hsub⟩
      obtain ⟨ε, hεpos, hεU⟩ : ∃ ε > 0, ∀ z, z ≠ z₀ → dist z z₀ < ε → g z ≠ 0 := by
        rw [eventually_nhdsWithin_iff] at hloc
        obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp hloc
        exact ⟨ε, hε, fun z hzne hzd => hall hzd hzne⟩
      obtain ⟨r, hrpos, hrρ, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < ρ ∧ r < ε :=
        ⟨min ρ ε / 2, div_pos (lt_min hρpos hεpos) two_pos,
          by have := min_le_left ρ ε; linarith,
          by have := min_le_right ρ ε; linarith⟩
      have hsub : closedBall z₀ r ⊆ U := by
        intro z hz
        apply hρU
        rw [mem_ball]
        rw [mem_closedBall] at hz
        linarith
      have hsphere : ∀ z ∈ sphere z₀ r, g z ≠ 0 := by
        intro z hz
        rw [mem_sphere] at hz
        exact hεU z (by rintro rfl; rw [dist_self] at hz; exact absurd hz.symm (ne_of_gt hrpos))
          (by rw [hz]; exact hrε)
      have hunif : TendstoUniformlyOn v g atTop (sphere z₀ r) :=
        (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp h (sphere z₀ r)
          (fun z hz => hsub (sphere_subset_closedBall hz)) (isCompact_sphere z₀ r)
      have hgc : ContinuousOn g (sphere z₀ r) :=
        hg_diff.continuousOn.mono (fun z hz => hsub (sphere_subset_closedBall hz))
      obtain ⟨z₁, hz₁, hz₁min⟩ := (isCompact_sphere z₀ r).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr hrpos.le) (continuous_norm.comp_continuousOn hgc)
      have hmpos : 0 < ‖g z₁‖ := norm_pos_iff.mpr (hsphere z₁ hz₁)
      have hm : ∀ z ∈ sphere z₀ r, ‖g z₁‖ ≤ ‖g z‖ := fun z hz => hz₁min hz
      have hA : ∀ n, Real.circleAverage (fun z => Real.log ‖v n z‖) z₀ r = Real.log ‖v n z₀‖ := by
        intro n
        refine AnalyticOnNhd.circleAverage_log_norm_of_ne_zero ?_ ?_
        · rw [abs_of_pos hrpos]
          exact ((hv n).analyticOnNhd hU).mono hsub
        · rw [abs_of_pos hrpos]
          exact fun u hu => hvn n u (hsub hu)
      have hlow : ∀ᶠ n in atTop,
          Real.log (‖g z₁‖ / 2) ≤ Real.circleAverage (fun z => Real.log ‖v n z‖) z₀ r := by
        have hm2 : 0 < ‖g z₁‖ / 2 := by linarith
        filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (‖g z₁‖ / 2) hm2] with n hn
        have hbound : ∀ z ∈ sphere z₀ r, ‖g z₁‖ / 2 ≤ ‖v n z‖ := by
          intro z hz
          have h1 : ‖g z‖ - ‖v n z‖ ≤ dist (g z) (v n z) := by
            rw [dist_eq_norm]; exact norm_sub_norm_le _ _
          have h2 : dist (g z) (v n z) < ‖g z₁‖ / 2 := hn z hz
          have h3 : ‖g z₁‖ ≤ ‖g z‖ := hm z hz
          linarith
        have hCI1 : CircleIntegrable (fun _ : ℂ => Real.log (‖g z₁‖ / 2)) z₀ r :=
          circleIntegrable_const _ _ _
        have hCI2 : CircleIntegrable (fun z => Real.log ‖v n z‖) z₀ r := by
          apply ContinuousOn.circleIntegrable'
          rw [abs_of_pos hrpos]
          refine ContinuousOn.log (continuous_norm.comp_continuousOn ?_) ?_
          · exact (hv n).continuousOn.mono (fun z hz => hsub (sphere_subset_closedBall hz))
          · intro z hz
            have := hbound z hz
            linarith
        refine le_trans (le_of_eq ?_) (Real.circleAverage_mono hCI1 hCI2 ?_)
        · exact (Real.circleAverage_const _ z₀ r).symm
        · intro x hx
          rw [abs_of_pos hrpos] at hx
          exact Real.log_le_log hm2 (hbound x hx)
      have hup : ∀ᶠ n in atTop, Real.log ‖v n z₀‖ < Real.log (‖g z₁‖ / 2) := by
        have hv0 : Tendsto (fun n => ‖v n z₀‖) atTop (𝓝 0) := by
          have h1 : Tendsto (fun n => v n z₀) atTop (𝓝 (0 : ℂ)) := by
            simpa [hgz₀] using h.tendsto_at hz₀
          simpa only [Function.comp_def, norm_zero] using
            (continuous_norm.tendsto (0 : ℂ)).comp h1
        filter_upwards [hv0.eventually_lt_const (show (0:ℝ) < ‖g z₁‖ / 2 by linarith)] with n hn
        exact Real.log_lt_log (norm_pos_iff.mpr (hvn n z₀ hz₀)) hn
      obtain ⟨n, hn1, hn2⟩ := (hlow.and hup).exists
      rw [hA n] at hn1
      linarith

end Work.Normal
