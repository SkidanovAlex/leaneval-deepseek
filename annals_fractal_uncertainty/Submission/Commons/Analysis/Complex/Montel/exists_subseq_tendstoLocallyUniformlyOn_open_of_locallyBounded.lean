import Mathlib
import Submission.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness
import Submission.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness_of_isOpen
import Submission.Commons.Analysis.Complex.ChartedSpace.eqOn_const_of_isPreconnected_of_isLocallyConst
import Submission.Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn_of_isOpen
import Submission.Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_bounded

noncomputable section
open Filter Metric Set
open scoped Topology

namespace Commons.Analysis.Complex.Montel

/-!
## Montel's theorem on an open subset of a `ℂ`-charted space

This file proves
`Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_open_of_locallyBounded`:
a locally bounded sequence of functions on an open subset `U` of a locally compact, second countable
space charted over `ℂ`, each of which is analytic in the preferred chart at every point of `U`,
admits a subsequence converging locally uniformly on `U` to a function which is again analytic in
the preferred chart at every point of `U`.

The proof has three parts.

* Every point of `U` has a chart ball on which *all* the functions of the family are analytic and
  on which the family is bounded: the bound is immediate from local boundedness, while the
  uniformity of the radius is the content of the helper `exists_chartBall_analyticAt_of_isOpen`
  below (the open-set version of
  `Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt`, proved by the same
  dichotomy: either every member is locally constant near the point — in which case the
  locally-constant set is relatively clopen and, on a connected chart ball, every member is constant
  — or some member has a non-vanishing derivative somewhere, in which case the rigidity lemma
  `Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness_of_isOpen` forces
  every member to be analytic, with the isolated critical points removed by Riemann's removable
  singularity theorem).
* `Commons.Analysis.Complex.Montel.exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_bounded`
  then performs the diagonal extraction over a countable cover of `U` by such chart balls, using
  Montel's theorem on a disc after rescaling on each chart ball.
* Finally
  `Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn_of_isOpen`
  shows that the limit is analytic in the preferred chart at every point of `U`.
-/

/-- A function which is analytic in the preferred chart at every point of `U` is continuous at
every point of `U`. -/
private lemma continuousAt_of_analyticAt_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {f : X → ℂ}
    (hf : ∀ x ∈ U, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) {x : X}
    (hx : x ∈ U) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) x :=
    (hf x hx).continuousAt.comp ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))
  have h2 : ((f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) =ᶠ[𝓝 x] f := by
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x).left_inv hy]
  exact h1.congr h2

/-- **Chart balls of analyticity, relative to an open set.**  Let `X` be a `ℂ`-charted space,
`U ⊆ X` open, and `F : ℕ → X → ℂ` a family which in the preferred chart at every point of `U` is
analytic at the image of that point.  Then for every `x ∈ U` and every `V ∈ 𝓝 x` there is a ball
`Metric.ball ((chartAt ℂ x) x) ρ` inside the target of `chartAt ℂ x`, whose `(chartAt ℂ x).symm`-image
is contained in `V` (hence in `U` if `V ⊆ U`), and on which **every** `F n` is analytic.

This is the open-set version of `Commons.Analysis.Complex.ChartedSpace.exists_chartBall_analyticAt`,
and the same proof applies, with two modifications: the continuity of the members of the family is
only used at points of `U` (where it follows from the hypothesis by `continuousAt_of_analyticAt_chart`),
and the rigidity lemma is used in its relative form `analyticAt_comp_chart_symm_of_witness_of_isOpen`
(whose only point of use is the preimage of the point under consideration, which lies in `U`). -/
theorem exists_chartBall_analyticAt_of_isOpen {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {U : Set X} (hU : IsOpen U) {F : ℕ → X → ℂ}
    (hF : ∀ n, ∀ x ∈ U, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    {x : X} (hx : x ∈ U) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ ⊆ V ∧
      ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (F n ∘ (chartAt ℂ x).symm) z := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let c : ℂ := e x
  have hx_src : x ∈ e.source := mem_chart_source ℂ x
  have hc_tgt : c ∈ e.target := e.map_source hx_src
  -- ## A ball around `c` whose `e.symm`-image lies in `V ∩ U`
  have hVU : V ∩ U ∈ 𝓝 x := Filter.inter_mem hV (hU.mem_nhds hx)
  have hsymm_c : e.symm c = x := e.left_inv hx_src
  have hev : ∀ᶠ z in 𝓝 c, e.symm z ∈ V ∩ U := by
    have ht : Tendsto e.symm (𝓝 c) (𝓝 x) := by
      rw [← hsymm_c]
      exact e.continuousAt_symm hc_tgt
    exact ht.eventually hVU
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
  have hεsub : e.symm '' Metric.ball c ε ⊆ V ∩ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hεp hz
  obtain ⟨ρ₁, hρ₁, hρ₁tgt⟩ := Metric.isOpen_iff.mp e.open_target c hc_tgt
  set ρ₀ : ℝ := min ρ₁ ε with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min hρ₁ hε
  have hρ₀tgt : Metric.ball c ρ₀ ⊆ e.target :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hρ₁tgt
  have hρ₀sub : e.symm '' Metric.ball c ρ₀ ⊆ V ∩ U :=
    (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _))).trans hεsub
  by_cases hA : ∀ n, ∀ᶠ y in 𝓝 x, F n y = F n x
  · -- ## Case 1: every member is locally constant at `x`
    have hPopen : IsOpen (e.symm '' Metric.ball c ρ₀) :=
      OpenPartialHomeomorph.isOpen_image_symm_of_subset_target e isOpen_ball hρ₀tgt
    have hPconn : IsPreconnected (e.symm '' Metric.ball c ρ₀) :=
      isPreconnected_ball.image e.symm (e.continuousOn_symm.mono hρ₀tgt)
    have hxP : x ∈ e.symm '' Metric.ball c ρ₀ := ⟨c, mem_ball_self hρ₀, e.left_inv hx_src⟩
    have hPU : e.symm '' Metric.ball c ρ₀ ⊆ U := fun y hy => (hρ₀sub hy).2
    refine ⟨ρ₀, hρ₀, hρ₀tgt, fun y hy => (hρ₀sub hy).1, ?_⟩
    intro n z hz
    have hconst : ∀ y ∈ e.symm '' Metric.ball c ρ₀, F n y = F n x :=
      Commons.Analysis.Complex.ChartedSpace.eqOn_const_of_isPreconnected_of_isLocallyConst
        (U := U) (fun y hy => hF n y hy)
        hPopen hPconn hPU hxP (hA n)
    have hev' : (fun _ => F n x) =ᶠ[𝓝 z] (F n ∘ e.symm) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      simp only [Function.comp_apply]
      exact (hconst (e.symm w) ⟨w, hw, rfl⟩).symm
    exact analyticAt_const.congr hev'
  · -- ## Case 2: some member is not locally constant at `x`
    obtain ⟨n₀, hB⟩ := not_forall.mp hA
    let h : ℂ → ℂ := F n₀ ∘ e.symm
    have hh_ana : AnalyticAt ℂ h c := hF n₀ x hx
    obtain ⟨r₁, hr₁, hana₁⟩ := hh_ana.exists_ball_analyticOnNhd
    set ρ : ℝ := min ρ₀ r₁ with hρdef
    have hρ : 0 < ρ := lt_min hρ₀ hr₁
    have hρ_le₀ : ρ ≤ ρ₀ := min_le_left _ _
    have hρ_le₁ : ρ ≤ r₁ := min_le_right _ _
    have hball : Metric.ball c ρ ⊆ e.target := (Metric.ball_subset_ball hρ_le₀).trans hρ₀tgt
    have hana : AnalyticOnNhd ℂ h (Metric.ball c ρ) := hana₁.mono (Metric.ball_subset_ball hρ_le₁)
    have hc_val : h c = F n₀ x := by
      simp only [h, Function.comp_apply]
      rw [show c = e x from rfl, e.left_inv hx_src]
    have hnc : ¬(∀ᶠ w in 𝓝 c, h w = h c) := by
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
    have hnotconst : ¬∃ a, ∀ z ∈ Metric.ball c ρ, h z = a := by
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
    refine ⟨ρ, hρ, hball, ?_, ?_⟩
    · intro y hy
      exact (hρ₀sub (Set.image_mono (Metric.ball_subset_ball hρ_le₀) hy)).1
    · intro m z hz
      by_cases hdz : deriv h z = 0
      · -- ## Removable singularities
        have hball_z := hcrit z hz hdz
        rw [eventually_nhdsWithin_iff] at hball_z
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hball_z
        obtain ⟨ε₀, hε₀, hε₀p⟩ := Metric.eventually_nhds_iff.mp hball_z
        have hdist : dist z c < ρ := hz
        set δ : ℝ := min ε₀ (ρ - dist z c) with hδdef
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
          have hwU : e.symm w ∈ U :=
            (hρ₀sub ⟨w, Metric.ball_subset_ball hρ_le₀ hwball, rfl⟩).2
          exact (Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness_of_isOpen
            hF (hball hwball) hwU (hana w hwball) hwne' m).differentiableAt
        have hcont : ContinuousAt (F m ∘ e.symm) z :=
          (continuousAt_of_analyticAt_chart (U := U) (fun y hy => hF m y hy)
            ((hρ₀sub ⟨z, Metric.ball_subset_ball hρ_le₀ hz, rfl⟩).2)).comp
            (e.continuousAt_symm (hball hz))
        exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont
      · exact Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_witness_of_isOpen
          hF (hball hz) ((hρ₀sub ⟨z, Metric.ball_subset_ball hρ_le₀ hz, rfl⟩).2)
          (hana z hz) hdz m

/-- **Montel's theorem on an open subset of a `ℂ`-charted space.**  Let `X` be a locally compact,
second countable space charted over `ℂ`, `U ⊆ X` open, and `f : ℕ → X → ℂ` a sequence of functions,
each analytic in the preferred chart at every point of `U`, which is locally bounded on `U` (every
point of `U` has a neighbourhood on which the whole family is bounded).  Then there is a strictly
monotone `φ` and a function `g` such that `f (φ n)` converges to `g` locally uniformly on `U`, and
`g` is again analytic in the preferred chart at every point of `U`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_open_of_locallyBounded {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [LocallyCompactSpace X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) {f : ℕ → X → ℂ}
    (hf : ∀ n, ∀ x ∈ U, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hb : ∀ x ∈ U, ∃ V : Set X, V ∈ 𝓝 x ∧ V ⊆ U ∧ ∃ M : ℝ, ∀ n, ∀ y ∈ V, ‖f n y‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g : X → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g Filter.atTop U ∧
      (∀ x ∈ U, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) := by
  classical
  -- ## Chart balls on which the whole family is analytic and bounded
  have hball : ∀ x ∈ U, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ ⊆ U ∧
      (∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ, AnalyticAt ℂ (f n ∘ (chartAt ℂ x).symm) z) ∧
      (∃ C : ℝ, ∀ n, ∀ z ∈ Metric.ball ((chartAt ℂ x) x) ρ,
        ‖f n ((chartAt ℂ x).symm z)‖ ≤ C) := by
    intro x hx
    obtain ⟨V, hV, hVU, M, hM⟩ := hb x hx
    obtain ⟨ρ, hρ, htgt, hVsub, hana⟩ := exists_chartBall_analyticAt_of_isOpen hU hf hx hV
    exact ⟨ρ, hρ, htgt, hVsub.trans hVU, hana, M,
      fun n z hz => hM n _ (hVsub ⟨z, hz, rfl⟩)⟩
  -- ## Diagonal extraction of a locally uniformly convergent subsequence
  obtain ⟨φ, g, hφ, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_chartBall_bounded hU hball
  -- ## The limit is analytic in every preferred chart
  have hana : ∀ x ∈ U, AnalyticAt ℂ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    Commons.Analysis.Complex.ChartedSpace.analyticAt_comp_chart_symm_of_tendstoLocallyUniformlyOn_of_isOpen
      (fun x hx => by
        obtain ⟨ρ, hρ, htgt, hU', hana, -⟩ := hball x hx
        exact ⟨ρ, hρ, htgt, hU', fun n z hz => hana (φ n) z hz⟩) hconv
  exact ⟨φ, g, hφ, hconv, hana⟩

end Commons.Analysis.Complex.Montel
