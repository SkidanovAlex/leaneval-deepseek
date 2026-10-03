import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst
import Submission.Lib.Unif2.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness

open Filter Metric Set
open scoped Topology

noncomputable section

namespace Commons.Analysis.Complex.ChartedSpace

/-- **Chart balls of analyticity.**  Let `X` be a `ℂ`-charted space, locally compact and second
countable, and `F : ℕ → X → ℂ` a family which in the preferred chart at each point is analytic at the
image of that point.  Then for every `x` there is a ball `Metric.ball ((chartAt ℂ x) x) ρ` inside the
target of `chartAt ℂ x` on which **every** `F n` is analytic (in that chart).

Proof sketch.  Let `e := chartAt ℂ x`, `c := e x`.
* If every `F n` is locally constant at `x`: by
  `Commons.Analysis.Complex.ChartedSpace.isClopen_setOf_eventuallyConst` the set where `F n` is
  locally constant is clopen, so `F n` is locally constant on the connected component of `x`, hence
  (being continuous — it is analytic in charts) `F n` is constant on that component; as
  `e.symm '' ball c ρ` is connected, `F n ∘ e.symm` is constant near `c`, in particular analytic on
  the whole ball.
* Otherwise some `F n₀` is not locally constant at `x`; then `h := F n₀ ∘ e.symm` is analytic at `c`
  with some radius `ρ > 0` and is non-constant on the ball.  By
  `Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness`, every
  `F m ∘ e.symm` is analytic at every point `u` of the ball with `deriv h u ≠ 0`, i.e. on the ball
  minus the (discrete) zero set of `deriv h`.  Each `F m ∘ e.symm` is continuous on the ball and
  bounded, so by Riemann's removable singularity theorem
  (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) the isolated points of
  that zero set are removable, and every `F m ∘ e.symm` is analytic on the whole ball. -/
theorem exists_chartBall_analyticAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {F : ℕ → X → ℂ}
    (hF : ∀ n x, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) (x : X) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let c : ℂ := e x
  have hc_tgt : c ∈ e.target := e.map_source (mem_chart_source ℂ x)
  have hx_src : x ∈ e.source := mem_chart_source ℂ x
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.mp e.open_target c hc_tgt
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    rw [continuous_iff_continuousAt]
    intro q
    have hq : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
    have hcomp : ContinuousAt ((F n ∘ (chartAt ℂ q).symm) ∘ (chartAt ℂ q)) q :=
      (hF n q).continuousAt.comp ((chartAt ℂ q).continuousAt hq)
    refine hcomp.congr ?_
    filter_upwards [(chartAt ℂ q).open_source.mem_nhds hq] with y hy
    simp only [Function.comp_apply]
    rw [(chartAt ℂ q).left_inv hy]
  by_cases hA : ∀ n, ∀ᶠ y in 𝓝 x, F n y = F n x
  · have hcont_symm : ContinuousOn e.symm (Metric.ball c ρ₁) := e.continuousOn_symm.mono hball₁
    have hPconn : IsPreconnected (e.symm '' Metric.ball c ρ₁) :=
      isPreconnected_ball.image e.symm hcont_symm
    have hxP : x ∈ e.symm '' Metric.ball c ρ₁ :=
      ⟨c, mem_ball_self hρ₁, e.left_inv hx_src⟩
    have hconst : ∀ n y, y ∈ e.symm '' Metric.ball c ρ₁ → F n y = F n x := by
      intro n y hy
      have hS : IsClopen {z : X | ∀ᶠ w in 𝓝 z, F n w = F n z} :=
        isClopen_setOf_eventuallyConst (f := F n) (fun z => hF n z)
      have hxS : x ∈ {z : X | ∀ᶠ w in 𝓝 z, F n w = F n z} := hA n
      have hPS : e.symm '' Metric.ball c ρ₁ ⊆ {z : X | ∀ᶠ w in 𝓝 z, F n w = F n z} :=
        hPconn.subset_left_of_subset_union hS.isOpen hS.isClosed.isOpen_compl
          disjoint_compl_right (by rw [union_compl_self]; exact subset_univ _) ⟨x, hxP, hxS⟩
      let P : Set X := e.symm '' Metric.ball c ρ₁
      have hPconnI : PreconnectedSpace P := Subtype.preconnectedSpace hPconn
      have hφ : IsLocallyConstant (fun z : P => F n (z : X)) := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro z
        have hzS := hPS z.2
        exact continuous_subtype_val.continuousAt.eventually hzS
      exact hφ.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, hxP⟩
    refine ⟨ρ₁, hρ₁, hball₁, ?_⟩
    intro n z hz
    have hev : (fun _ => F n x) =ᶠ[𝓝 z] (F n ∘ e.symm) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      simp only [Function.comp_apply]
      exact (hconst n (e.symm w) ⟨w, hw, rfl⟩).symm
    exact analyticAt_const.congr hev
  · obtain ⟨n₀, hB⟩ := not_forall.mp hA
    let h : ℂ → ℂ := F n₀ ∘ e.symm
    have hh_ana : AnalyticAt ℂ h c := hF n₀ x
    obtain ⟨r₁, hr₁, hana₁⟩ := hh_ana.exists_ball_analyticOnNhd
    let ρ : ℝ := min ρ₁ r₁
    have hρ : 0 < ρ := lt_min hρ₁ hr₁
    have hρ_le₁ : ρ ≤ ρ₁ := min_le_left _ _
    have hρ_le₂ : ρ ≤ r₁ := min_le_right _ _
    have hball : Metric.ball c ρ ⊆ e.target :=
      (Metric.ball_subset_ball hρ_le₁).trans hball₁
    have hana : AnalyticOnNhd ℂ h (Metric.ball c ρ) :=
      hana₁.mono (Metric.ball_subset_ball hρ_le₂)
    have hc_val : h c = F n₀ x := by
      simp only [h, Function.comp_apply]
      rw [show c = e x from rfl, e.left_inv hx_src]
    have hnc : ¬ (∀ᶠ w in 𝓝 c, h w = h c) := by
      intro hh
      apply hB
      have h1 : F n₀ =ᶠ[𝓝 x] (h ∘ e) := by
        filter_upwards [e.open_source.mem_nhds hx_src] with y hy
        simp only [Function.comp_apply, h]
        rw [e.left_inv hy]
      have h2 : (h ∘ e) =ᶠ[𝓝 x] (fun _ => F n₀ x) := by
        have htend : Tendsto e (𝓝 x) (𝓝 c) := by
          rw [show c = e x from rfl]
          exact e.continuousAt hx_src
        filter_upwards [htend.eventually hh] with y hy
        simp only [Function.comp_apply]
        rw [hy, hc_val]
      exact h1.trans h2
    have hnotconst : ¬ ∃ a, ∀ z ∈ Metric.ball c ρ, h z = a := by
      rintro ⟨a, ha⟩
      apply hnc
      filter_upwards [Metric.ball_mem_nhds c hρ] with w hw
      rw [ha w hw, ha c (mem_ball_self hρ)]
    have hderiv_ana : AnalyticOnNhd ℂ (deriv h) (Metric.ball c ρ) := hana.deriv
    have hcrit : ∀ z ∈ Metric.ball c ρ, deriv h z = 0 →
        ∀ᶠ w in 𝓝[≠] z, deriv h w ≠ 0 := by
      intro z hz hdz
      rcases (hderiv_ana z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exfalso
        have heq : EqOn (deriv h) 0 (Metric.ball c ρ) :=
          hderiv_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hz h0
        have hcst : ∀ a ∈ Metric.ball c ρ, ∀ b ∈ Metric.ball c ρ, h a = h b :=
          fun a ha b hb => Metric.isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball
            hana.differentiableOn (fun w hw => heq hw) ha hb
        exact hnotconst ⟨h c, fun w hw => hcst w hw c (mem_ball_self hρ)⟩
      · exact hne
    refine ⟨ρ, hρ, hball, ?_⟩
    intro m z hz
    by_cases hdz : deriv h z = 0
    · have hball_z := hcrit z hz hdz
      rw [eventually_nhdsWithin_iff] at hball_z
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hball_z
      obtain ⟨ε₀, hε₀, hε₀p⟩ := Metric.eventually_nhds_iff.mp hball_z
      have hdist : dist z c < ρ := hz
      let δ : ℝ := min ε₀ (ρ - dist z c)
      have hδpos : 0 < δ := lt_min hε₀ (by linarith)
      have hδsub : Metric.ball z δ ⊆ Metric.ball c ρ := by
        intro w hw
        rw [mem_ball] at hw ⊢
        calc dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
          _ < δ + dist z c := by linarith
          _ ≤ (ρ - dist z c) + dist z c := by linarith [min_le_right ε₀ (ρ - dist z c)]
          _ = ρ := by ring
      have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (F m ∘ e.symm) w := by
        rw [eventually_nhdsWithin_iff]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        filter_upwards [Metric.ball_mem_nhds z hδpos] with w hw hwne
        have hwball : w ∈ Metric.ball c ρ := hδsub hw
        have hwne' : deriv h w ≠ 0 :=
          hε₀p (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)) hwne
        exact (analyticAt_comp_chart_symm_of_witness hF (hball hwball) (hana w hwball) hwne' m).differentiableAt
      have hcont : ContinuousAt (F m ∘ e.symm) z :=
        (hFcont m).continuousAt.comp (e.continuousAt_symm (hball hz))
      exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
    · exact analyticAt_comp_chart_symm_of_witness hF (hball hz) (hana z hz) hdz m


end Commons.Analysis.Complex.ChartedSpace
