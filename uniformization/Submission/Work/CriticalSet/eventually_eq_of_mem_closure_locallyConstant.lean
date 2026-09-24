import Mathlib
import Submission.Work.Potential.Defs
import Submission.Work.CriticalSet.Fundamentals
import Submission.Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero

/-!
# A harmonic function is locally constant at a point of the closure of its locally constant locus

Let `E : X → ℝ` be harmonic at `y` on a Riemann surface `X` and let `S` be the set of points at
which `E` is locally constant.  Then `S` is open, and it is closed at every point of harmonicity of
`E`: if `y ∈ closure S` and `E` is harmonic at `y`, then `E` is locally already constant at `y`.

The proof reads `E` near `y` as the real part `Re F₀` of a function `F₀` analytic in the chart at
`y`.  A point `z ∈ S` near `y` makes `Re F₀` locally constant near `c z`, hence `F₀` locally
constant near `c z` (two real-analytic functions with the same real part agree:
`Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero`), so `deriv F₀` vanishes at `c z`.
If `c z ≠ c y`, this contradicts the isolated vanishing of `deriv F₀`
(`Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq`); if `c z = c y` then `z = y`
belongs to `S` already.  Either way a point of `S` arbitrarily close to `y` forces `y ∈ S`.
-/

open scoped Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

theorem eventually_eq_of_mem_closure_locallyConstant {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {E : X → ℝ} {y : X} (hE : Submission.HarmonicOnXAt E y)
    (hcl : y ∈ closure {z : X | ∀ᶠ w in nhds z, E w = E z}) :
    ∀ᶠ w in nhds y, E w = E y := by
  by_contra hcon
  -- work in the preferred chart at `y`
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let ζ : ℂ := c y
  have hy_src : y ∈ c.source := mem_chart_source ℂ y
  have hharm : InnerProductSpace.HarmonicAt (E ∘ c.symm) ζ := hE
  -- a local holomorphic companion of `E` in the chart
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    ((InnerProductSpace.isOpen_setOfPred_harmonicAt (E ∘ c.symm)).mem_nhds hharm)
  obtain ⟨F₀, hF₀ana, hF₀re⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hRsub
  have hF₀ζ : AnalyticAt ℂ F₀ ζ := hF₀ana ζ (Metric.mem_ball_self hR)
  -- `(F₀ ·).re` is not constant near `ζ`, else `E` would be locally constant at `y`
  have hnotre : ¬ ∀ᶠ w in 𝓝 ζ, (F₀ w).re = (F₀ ζ).re := by
    intro hh
    apply hcon
    have hct : Filter.Tendsto c (𝓝 y) (𝓝 ζ) := c.continuousAt hy_src
    have hpull : ∀ᶠ w in 𝓝 y, (F₀ (c w)).re = (F₀ ζ).re := hct.eventually hh
    have hEy : (F₀ ζ).re = E y := by
      have h1 := hF₀re (Metric.mem_ball_self hR)
      simp only [Function.comp_apply] at h1
      rw [h1]
      exact congrArg E (c.left_inv hy_src)
    have hV : Submission.chartBall c ζ R ∈ 𝓝 y :=
      (Submission.chartBall_isOpen c ζ R).mem_nhds ⟨hy_src, Metric.mem_ball_self hR⟩
    filter_upwards [hpull, hV] with w hw1 hw2
    obtain ⟨hw2src, hw2ball⟩ := Submission.mem_chartBall.mp hw2
    have hwe : (F₀ (c w)).re = E w := by
      have h2 := hF₀re hw2ball
      simp only [Function.comp_apply] at h2
      rw [h2]
      exact congrArg E (c.left_inv hw2src)
    rw [← hwe, hw1, hEy]
  -- hence the derivative of `F₀` does not vanish on a punctured neighbourhood of `ζ`
  have hpunct : ∀ᶠ w in 𝓝[≠] ζ, deriv F₀ w ≠ 0 :=
    Work.CriticalSet.eventually_deriv_ne_zero_of_not_eventually_re_eq hF₀ζ hnotre
  have hpunct' : ∀ᶠ w in 𝓝 ζ, w ≠ ζ → deriv F₀ w ≠ 0 := eventually_nhdsWithin_iff.mp hpunct
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hpunct'
  -- a chart neighbourhood of `y` on which all the above is under control
  have hVne : Submission.chartBall c ζ (min ε R) ∈ 𝓝 y :=
    (Submission.chartBall_isOpen c ζ (min ε R)).mem_nhds
      ⟨hy_src, Metric.mem_ball_self (lt_min hεpos hR)⟩
  obtain ⟨z, hzVS⟩ := mem_closure_iff_nhds.mp hcl _ hVne
  obtain ⟨hzV, hzS⟩ := hzVS
  obtain ⟨hzsrc, hzball⟩ := Submission.mem_chartBall.mp hzV
  have hzballε : c z ∈ Metric.ball ζ ε := Metric.ball_subset_ball (min_le_left _ _) hzball
  have hzballR : c z ∈ Metric.ball ζ R := Metric.ball_subset_ball (min_le_right _ _) hzball
  have hzS' : ∀ᶠ w in 𝓝 z, E w = E z := hzS
  -- `E` locally constant at `z` forces `deriv F₀ (c z) = 0`
  have hz0 : deriv F₀ (c z) = 0 := by
    have hb : Submission.chartBall c ζ R ∈ 𝓝 z :=
      (Submission.chartBall_isOpen c ζ R).mem_nhds ⟨hzsrc, hzballR⟩
    have hzre : (F₀ (c z)).re = E z := by
      have h1 := hF₀re hzballR
      simp only [Function.comp_apply] at h1
      rw [h1]
      exact congrArg E (c.left_inv hzsrc)
    have hq : ∀ᶠ w in 𝓝 z, (F₀ (c w)).re = (F₀ (c z)).re := by
      filter_upwards [hzS', hb] with w hwS hwV
      obtain ⟨hwsrc, hwball⟩ := Submission.mem_chartBall.mp hwV
      have hwe : (F₀ (c w)).re = E w := by
        have h2 := hF₀re hwball
        simp only [Function.comp_apply] at h2
        rw [h2]
        exact congrArg E (c.left_inv hwsrc)
      rw [hwe, hwS, hzre]
    have hcs : Filter.Tendsto c.symm (𝓝 (c z)) (𝓝 z) := by
      have h : ContinuousAt c.symm (c z) := c.continuousAt_symm (c.map_source hzsrc)
      simpa only [c.left_inv hzsrc] using h.tendsto
    have hq' : ∀ᶠ ξ in 𝓝 (c z), (F₀ ξ).re = (F₀ (c z)).re := by
      filter_upwards [hcs.eventually hq, c.open_target.mem_nhds (c.map_source hzsrc)]
        with ξ hξ hξtgt
      rwa [c.right_inv hξtgt] at hξ
    have hana : AnalyticAt ℂ F₀ (c z) := hF₀ana (c z) hzballR
    have hsub : ∀ᶠ ξ in 𝓝 (c z), ((fun w : ℂ => F₀ w - F₀ (c z)) ξ).re = 0 := by
      filter_upwards [hq'] with ξ hξ
      simp [hξ]
    have hconst := Commons.Analysis.Complex.Analytic.eventually_eq_of_re_eq_zero
      (hana.sub analyticAt_const) hsub
    have hEq : F₀ =ᶠ[𝓝 (c z)] (fun _ : ℂ => F₀ (c z)) := by
      filter_upwards [hconst] with ξ hξ
      exact sub_eq_zero.mp (by simpa using hξ)
    rw [hEq.deriv_eq]
    simp
  by_cases hcz : c z = ζ
  · have hzy : z = y := c.injOn hzsrc hy_src hcz
    exact hcon (hzy ▸ hzS')
  · exact (hεball hzballε hcz) hz0

end Work.CriticalSet
