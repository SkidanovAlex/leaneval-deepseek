import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.harnackReach
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall
import Submission.Lib.Unif2.Work.Drive.chartBall
import Submission.Lib.Unif2.Work.Drive.isPreconnected_sdiff_finite
import Submission.Lib.Unif2.Work.Drive.osc_sphere_le_of_harmonicOnNhd
import Submission.Lib.Unif2.Work.Potential.removable_singularity_of_bounded_near
import Submission.Lib.Unif2.Work.Potential.punctured_ball_abs_le_of_bounded_near
import Submission.Lib.Unif2.DirichletLim
import Submission.Lib.Unif2.MaxPrincipleRegion

open Filter Set
open scoped Topology

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A compact set contained in a monotone union of open sets is contained in one member. -/
theorem exists_subset_iUnion_of_isCompact'' {Ω : ℕ → Set X} (hΩo : ∀ n, IsOpen (Ω n))
    (hmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ) {K : Set X}
    (hK : IsCompact K) : ∃ N : ℕ, K ⊆ Ω N := by
  classical
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩo (by rw [hcov]; exact subset_univ K)
  rcases t.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (ht hx)
    exact absurd hi (Finset.notMem_empty i)
  · exact ⟨t.max' hne, fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact hmono' i (t.max' hne) (Finset.le_max' t i hi) hxi⟩

/-- The frontier of a proper nonempty subset of a preconnected space is nonempty. -/
theorem frontier_nonempty_of_ne_univ'' {U : Set X} (hU : U ≠ Set.univ) (hne : U.Nonempty) :
    (frontier U).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  rcases (frontier_eq_empty_iff.mp h) with h0 | h0
  · exact hne.ne_empty h0
  · exact hU h0

/-- The chart sphere is compact. -/
theorem isCompact_chartSphere_aux {c : OpenPartialHomeomorph X ℂ} {ca : ℂ} {t : ℝ}
    (hsub : Metric.closedBall ca t ⊆ c.target) :
    IsCompact (Submission.chartSphere c ca t) := by
  have himg : Submission.chartSphere c ca t = c.symm '' Metric.sphere ca t := by
    ext y
    constructor
    · intro hy
      rw [Submission.mem_chartSphere] at hy
      exact ⟨c y, hy.2, c.left_inv hy.1⟩
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ c.target := hsub (Metric.sphere_subset_closedBall hw)
      rw [Submission.mem_chartSphere]
      exact ⟨c.map_target hwt, by
        rw [c.right_inv hwt]
        exact hw⟩
  rw [himg]
  exact (isCompact_sphere ca t).image_of_continuousOn
    (c.continuousOn_symm.mono fun z hz => hsub (Metric.sphere_subset_closedBall hz))

/-- The frontier of a set with a closed piece removed is contained in the union of the frontier
and the closed piece. -/
theorem frontier_sdiff_subset_of_isClosed {Ω A : Set X} (hA : IsClosed A) :
    frontier (Ω \ A) ⊆ frontier Ω ∪ A := by
  intro ξ hξ
  rw [frontier_eq_closure_inter_closure] at hξ ⊢
  obtain ⟨h1, h2⟩ := hξ
  have hcompl : (Ω \ A)ᶜ = Ωᶜ ∪ A := by
    ext y
    rw [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [hcompl, closure_union, hA.closure_eq] at h2
  rcases h2 with h | h
  · exact Or.inl ⟨closure_mono Set.sdiff_subset h1, h⟩
  · exact Or.inr h

/-- The open chart ball is contained in the interior of the closed chart ball. -/
theorem chartBall_subset_interior_chartClosedBall_aux {c : OpenPartialHomeomorph X ℂ} {ca : ℂ}
    {ρ : ℝ} (hsub : Metric.closedBall ca ρ ⊆ c.target) :
    Submission.chartBall c ca ρ ⊆ interior (Submission.chartClosedBall c ca ρ) := by
  intro y hy
  rw [Submission.mem_chartBall] at hy
  obtain ⟨hys, hyb⟩ := hy
  have hyd : ‖c y - ca‖ < ρ := by
    have := Metric.mem_ball.mp hyb
    rwa [dist_eq_norm] at this
  set t : ℝ := (ρ - ‖c y - ca‖) / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  refine mem_interior_iff_mem_nhds.mpr ?_
  refine Filter.mem_of_superset (Filter.inter_mem (c.open_source.mem_nhds hys)
    ((c.continuousAt hys).preimage_mem_nhds (Metric.ball_mem_nhds (c y) htpos))) ?_
  rintro z ⟨hzsrc, hz⟩
  have hzd : ‖c z - c y‖ < t := by
    have := Metric.mem_ball.mp hz
    rwa [dist_eq_norm] at this
  have hzn : ‖c z - ca‖ < ρ := by
    calc ‖c z - ca‖ ≤ ‖c z - c y‖ + ‖c y - ca‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
      _ < t + ‖c y - ca‖ := by linarith
      _ = (ρ + ‖c y - ca‖) / 2 := by rw [ht]; ring
      _ < ρ := by linarith
  rw [Submission.mem_chartClosedBall]
  exact ⟨hzsrc, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hzn.le⟩

/-- **The maximum principle on the complement of a chart ball.**  If `G` is harmonic on `Ω \ {a}`,
non-negative there, tends to `0` at `∂Ω` (decay), and `M` bounds `G` on the chart sphere of radius
`r`, then `G ≤ M` on all of `Ω` outside the closed chart ball of radius `r`. -/
theorem le_max_chartSphere_of_isGreenOn {Ω : Set X} {G : X → ℝ} {a : X}
    {c : OpenPartialHomeomorph X ℂ} {ca : ℂ} {r M : ℝ} (hr : 0 < r)
    (hsubr : Metric.closedBall ca r ⊆ c.target)
    (hΩopen : IsOpen Ω) (hΩcomp : IsCompact (closure Ω))
    (hGharm : Submission.HarmonicOnX G (Ω \ {a}))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ Kc : Set X, IsCompact Kc ∧ Kc ⊆ Ω ∧ ∀ x ∈ Ω, x ∉ Kc → G x < ε)
    (hArΩ : Submission.chartClosedBall c ca r ⊆ Ω) (hasrc : a ∈ c.source) (hca : c a = ca)
    (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ Submission.chartSphere c ca r, G y ≤ M) :
    ∀ y ∈ Ω \ Submission.chartClosedBall c ca r, G y ≤ M := by
  classical
  set A : Set X := Submission.chartClosedBall c ca r with hAdef
  set U : Set X := Ω \ A with hUdef
  have haA : a ∈ A := by
    rw [hAdef, Submission.mem_chartClosedBall]
    exact ⟨hasrc, by rw [hca, Metric.mem_closedBall, dist_self]; exact hr.le⟩
  have hAclosed : IsClosed A := Submission.isClosed_chartClosedBall hsubr
  have hUopen : IsOpen U := hΩopen.sdiff hAclosed
  have hUsub : U ⊆ Ω \ {a} := by
    intro z hz
    exact ⟨hz.1, fun h => hz.2 (h ▸ haA)⟩
  have hGharmU : Submission.HarmonicOnX G U := hGharm.mono hUsub
  have hcont : ContinuousOn G U := fun z hz => ((hGharmU z hz).continuousAt).continuousWithinAt
  have hsubh : Submission.SubharmonicOnX G U := hGharmU.subharmonic hcont
  have hcomp : IsCompact (closure U) :=
    hΩcomp.of_isClosed_subset isClosed_closure (closure_mono Set.sdiff_subset)
  intro y hy
  by_cases hUe : U = ∅
  · rw [hUe] at hy; exact absurd hy (Set.notMem_empty y)
  have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hUe
  have hUuniv : U ≠ Set.univ := by
    intro h
    have : a ∈ U := by rw [h]; exact Set.mem_univ a
    exact this.2 haA
  have hfront : (frontier U).Nonempty := frontier_nonempty_of_ne_univ'' hUuniv hUne
  refine Submission.SubharmonicOnX.le_of_frontier_limsup hUopen hsubh hcomp hfront ?_ y hy
  intro ξ hξ ε hε
  rcases frontier_sdiff_subset_of_isClosed hAclosed hξ with hξΩ | hξA
  · -- ξ ∈ frontier Ω: the decay clause
    obtain ⟨Kc, hKccomp, hKcΩ, hKcdec⟩ := hdecay (M + ε) (by linarith)
    have hξnotΩ : ξ ∉ Ω := by
      have hξcl : ξ ∈ closure (Ωᶜ) := by
        rw [frontier_eq_closure_inter_closure] at hξΩ
        exact hξΩ.2
      rwa [hΩopen.isClosed_compl.closure_eq] at hξcl
    have hξKc : ξ ∉ Kc := fun h => hξnotΩ (hKcΩ h)
    have hmem : (Kc)ᶜ ∈ 𝓝 ξ := hKccomp.isClosed.isOpen_compl.mem_nhds hξKc
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with z hzU hzKc
    exact le_of_lt (hKcdec z hzU.1 hzKc)
  · -- ξ ∈ A: either ξ is inside the chart ball (impossible on the frontier) or on the sphere
    have hξnotint : ξ ∉ interior A := by
      intro hint
      have hcl : ξ ∈ closure U := by
        rw [frontier_eq_closure_inter_closure] at hξ
        exact hξ.1
      have hsubc : closure U ⊆ (interior A)ᶜ :=
        closure_minimal (fun z hz hzint => hz.2 (interior_subset hzint)) isOpen_interior.isClosed_compl
      exact hsubc hcl hint
    have hξsp : ξ ∈ Submission.chartSphere c ca r := by
      rw [hAdef, Submission.mem_chartClosedBall] at hξA
      obtain ⟨hsrc, hball⟩ := hξA
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      rw [Submission.mem_chartSphere]
      refine ⟨hsrc, ?_⟩
      rw [Metric.mem_sphere, dist_eq_norm]
      by_contra hne
      have hlt : ‖c ξ - ca‖ < r := lt_of_le_of_ne hball hne
      exact hξnotint (chartBall_subset_interior_chartClosedBall_aux hsubr
        (Submission.mem_chartBall.mpr ⟨hsrc, by rw [Metric.mem_ball, dist_eq_norm]; exact hlt⟩))
    have hξnorm : ‖c ξ - ca‖ = r := by
      rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hξsp
      exact hξsp.2
    have hξne : ξ ≠ a := by
      intro h
      rw [h, hca, sub_self, norm_zero] at hξnorm
      linarith [hr, hξnorm]
    have hcontξ : ContinuousAt G ξ := (hGharm ξ ⟨hArΩ hξA, hξne⟩).continuousAt
    have hmem : G ⁻¹' (Metric.ball (G ξ) ε) ∈ 𝓝 ξ :=
      hcontξ.preimage_mem_nhds (Metric.ball_mem_nhds (G ξ) hε)
    filter_upwards [nhdsWithin_le_nhds hmem] with z hz
    simp only [Set.mem_preimage] at hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have h1 : G z < G ξ + ε := by
      rw [abs_lt] at hz
      linarith [hz.2]
    have h2 : G ξ ≤ M := hM ξ hξsp
    linarith

theorem chartLocalGreenExtension {a : X} {Ω : Set X} {G : X → ℝ} {R₁ R₂ : ℝ}
    (hR₁ : 0 < R₁) (hR₁R₂ : R₁ < R₂)
    (hsub : Metric.closedBall ((chartAt ℂ a) a) R₂ ⊆ (chartAt ℂ a).target)
    (hΩ : Submission.chartBall (chartAt ℂ a) ((chartAt ℂ a) a) R₂ \ {a} ⊆ Ω)
    (hGa : Submission.HarmonicOnX G (Ω \ {a}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn Ω a G) :
    ∃ h : ℂ → ℝ,
      (∀ z : ℂ, ‖z - (chartAt ℂ a) a‖ < R₁ → InnerProductSpace.HarmonicAt h z) ∧
      (∀ z : ℂ, ‖z - (chartAt ℂ a) a‖ < R₁ → z ≠ (chartAt ℂ a) a →
        h z = G ((chartAt ℂ a).symm z) + Real.log ‖z - (chartAt ℂ a) a‖) := by
  classical
  obtain ⟨C, V, hVmem, hCV⟩ := hpole
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ a with hc
  set ca : ℂ := c a with hca
  have hR₂ : 0 < R₂ := lt_trans hR₁ hR₁R₂
  have hsrc : a ∈ c.source := mem_chart_source ℂ a
  -- chart-target membership
  have hmemtgt : ∀ z : ℂ, ‖z - ca‖ < R₂ → z ∈ c.target := fun z hz =>
    hsub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hz.le))
  -- the pullback of a punctured chart ball lies in `Ω \ {a}`
  have hmemX : ∀ z : ℂ, 0 < ‖z - ca‖ → ‖z - ca‖ < R₂ →
      c.symm z ∈ Ω ∧ c.symm z ≠ a ∧ c (c.symm z) = z := by
    intro z hz0 hz
    have hzt : z ∈ c.target := hmemtgt z hz
    have hxs : c.symm z ∈ c.source := c.map_target hzt
    have hrt : c (c.symm z) = z := c.right_inv hzt
    have hne : c.symm z ≠ a := by
      intro h
      have h2 : c (c.symm z) = ca := by rw [h, hca]
      rw [hrt] at h2
      rw [h2] at hz0
      simp at hz0
    have hball : c.symm z ∈ Submission.chartBall c ca R₂ := by
      rw [Submission.mem_chartBall]
      exact ⟨hxs, by rw [hrt]; rwa [Metric.mem_ball, dist_eq_norm]⟩
    exact ⟨hΩ ⟨hball, hne⟩, hne, hrt⟩
  -- harmonicity in the chart coordinates
  have hwharm : ∀ z : ℂ, ‖z - ca‖ < R₂ → z ≠ ca →
      InnerProductSpace.HarmonicAt (fun y : ℂ => G (c.symm y) + Real.log ‖y - ca‖) z := by
    intro z hz hzne
    have hz0 : 0 < ‖z - ca‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
    obtain ⟨hΩmem, hxne, hrt⟩ := hmemX z hz0 hz
    have h1 : InnerProductSpace.HarmonicAt (G ∘ c.symm) z := by
      have h2 := (Submission.HarmonicOnXAt_iff_chart (x := c.symm z) (y := a)
        (c.map_target (hmemtgt z hz))).mp (hGa (c.symm z) ⟨hΩmem, hxne⟩)
      rwa [hrt] at h2
    have h4 : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y - ca‖) z :=
      AnalyticAt.harmonicAt_log_norm (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzne)
    exact h1.add h4
  -- boundedness near the puncture
  have hsymm_ca : c.symm ca = a := by rw [hca]; exact c.left_inv hsrc
  have hsymm_cont : ContinuousAt c.symm ca := by
    have h2 : ContinuousAt c.symm (c a) := c.continuousAt_symm (c.map_source hsrc)
    rwa [hca]
  have hVmem' : V ∈ 𝓝 (c.symm ca) := by rw [hsymm_ca]; exact hVmem
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hsymm_cont.preimage_mem_nhds hVmem')
  have hnear : ∀ z : ℂ, 0 < ‖z - ca‖ → ‖z - ca‖ < min δ R₁ →
      |G (c.symm z) + Real.log ‖z - ca‖| ≤ C := by
    intro z hz0 hz
    have hzd : ‖z - ca‖ < δ := lt_of_lt_of_le hz (min_le_left δ R₁)
    have hzR₁ : ‖z - ca‖ ≤ R₁ := le_of_lt (lt_of_lt_of_le hz (min_le_right δ R₁))
    have hsymmV : c.symm z ∈ V := hδV (by rwa [Metric.mem_ball, dist_eq_norm])
    obtain ⟨hΩmem, hxne, hrt⟩ := hmemX z hz0 (lt_of_le_of_lt hzR₁ hR₁R₂)
    have h := hCV (c.symm z) hsymmV hΩmem hxne
    rwa [hca, hrt] at h
  -- the sphere bound
  have hcomp : IsCompact {z : ℂ | ‖z - ca‖ = R₁} := by
    have : {z : ℂ | ‖z - ca‖ = R₁} = Metric.sphere ca R₁ := by
      ext z
      simp [Metric.mem_sphere, dist_eq_norm]
    rw [this]
    exact isCompact_sphere ca R₁
  have hneS : ({z : ℂ | ‖z - ca‖ = R₁}).Nonempty :=
    ⟨ca + (R₁ : ℂ), by
      change ‖ca + (R₁ : ℂ) - ca‖ = R₁
      have h1 : ca + (R₁ : ℂ) - ca = (R₁ : ℂ) := by ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₁]⟩
  have hcontw : ContinuousOn (fun y : ℂ => |G (c.symm y) + Real.log ‖y - ca‖|)
      {z : ℂ | ‖z - ca‖ = R₁} := by
    intro z hz
    have hz' : ‖z - ca‖ = R₁ := hz
    have hzne : z ≠ ca := by
      intro h; rw [h, sub_self, norm_zero] at hz'; exact absurd hz' (ne_of_lt hR₁)
    have hzd : ‖z - ca‖ < R₂ := by rw [hz']; exact hR₁R₂
    exact ((hwharm z hzd hzne).1.continuousAt.abs).continuousWithinAt
  obtain ⟨zm, hzmS, hzmax⟩ := hcomp.exists_isMaxOn hneS hcontw
  -- the bound on the punctured `R₁`-ball
  have hbnd : ∀ z : ℂ, ‖z - ca‖ < R₁ → z ≠ ca →
      |G (c.symm z) + Real.log ‖z - ca‖| ≤ |G (c.symm zm) + Real.log ‖zm - ca‖| := by
    intro z hz hzne
    refine Work.Potential.punctured_ball_abs_le_of_bounded_near (a := ca) (ρ := R₂) (r := R₁)
      (w := fun y : ℂ => G (c.symm y) + Real.log ‖y - ca‖)
      (M := |G (c.symm zm) + Real.log ‖zm - ca‖|) hR₂ hR₁ hR₁R₂ ?_ ?_ ?_ z hz hzne
    · intro y hy hyne
      exact hwharm y hy hyne
    · refine ⟨C, min δ R₁ / 2, by positivity, ?_, ?_⟩
      · have hle : min δ R₁ ≤ R₁ := min_le_right δ R₁
        linarith
      · intro y hy0 hye
        refine hnear y hy0 ?_
        have h2 : min δ R₁ / 2 < min δ R₁ := by
          have hpos : 0 < min δ R₁ := lt_min hδ hR₁
          linarith
        exact lt_trans hye h2
    · intro y hy
      exact hzmax hy
  obtain ⟨h, hh, heq⟩ := Work.Potential.punctured_ball_harmonic_extension (a := ca) (ρ := R₁)
    (w := fun y : ℂ => G (c.symm y) + Real.log ‖y - ca‖)
    (M := |G (c.symm zm) + Real.log ‖zm - ca‖|) hR₁
    (fun z hz hzne => hwharm z (lt_trans hz hR₁R₂) hzne)
    (fun z hz hzne => hbnd z hz hzne)
  refine ⟨h, fun z hz => hh z hz, ?_⟩
  intro z hz hzne
  rw [heq z hz hzne]


/-- **The mean value identity for the chart-pulled-back Green function.**  If `v` is harmonic on
the closed disc of radius `R` and agrees off `ca` with `G ∘ c.symm + log‖· - ca‖`, then the circle
average of `G ∘ c.symm` differs between the circles of radii `R` and `t` by `log (R/t)`. -/
theorem circleAverage_chart_symm_eq {c : OpenPartialHomeomorph X ℂ} {ca : ℂ} {G : X → ℝ}
    {v : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall ca R))
    (hveq : ∀ z : ℂ, ‖z - ca‖ ≤ R → z ≠ ca → v z = G (c.symm z) + Real.log ‖z - ca‖)
    (hc : ∀ t : ℝ, 0 < t → t ≤ R →
      ContinuousOn (fun z : ℂ => G (c.symm z)) (Metric.sphere ca t)) :
    ∀ t : ℝ, 0 < t → t ≤ R →
      Real.circleAverage (fun z : ℂ => G (c.symm z)) ca t = v ca - Real.log t := by
  intro t ht htR
  have hlogcont : ContinuousOn (fun z : ℂ => Real.log ‖z - ca‖) (Metric.sphere ca t) := by
    intro z hz
    have hdist : dist z ca = t := by rw [Metric.mem_sphere] at hz; exact hz
    have hzne : z ≠ ca := by
      intro h
      rw [h, dist_self] at hdist
      exact absurd hdist.symm (ne_of_gt ht)
    have hne : ‖z - ca‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzne)
    have h1 : ContinuousAt (fun w : ℂ => w - ca) z := continuousAt_id.sub continuousAt_const
    have h2 : ContinuousAt (fun w : ℂ => ‖w - ca‖) z := continuous_norm.continuousAt.comp h1
    exact (h2.log hne).continuousWithinAt
  have h1 : CircleIntegrable (fun z : ℂ => G (c.symm z) + Real.log ‖z - ca‖) ca t :=
    ContinuousOn.circleIntegrable (le_of_lt ht) ((hc t ht htR).add hlogcont)
  have h2 : CircleIntegrable (fun z : ℂ => Real.log ‖z - ca‖) ca t :=
    ContinuousOn.circleIntegrable (le_of_lt ht) hlogcont
  have hsum : Real.circleAverage (fun z : ℂ => G (c.symm z) + Real.log ‖z - ca‖) ca t = v ca := by
    rw [Real.circleAverage_congr_sphere (f₁ := fun z : ℂ => G (c.symm z) + Real.log ‖z - ca‖)
      (f₂ := v) (by
        intro z hz
        rw [Metric.mem_sphere] at hz
        have hzt : ‖z - ca‖ = t := by rw [← dist_eq_norm, hz, abs_of_pos ht]
        have hzne : z ≠ ca := by
          intro h
          rw [h, sub_self, norm_zero] at hzt
          exact absurd hzt.symm (ne_of_gt ht)
        exact (hveq z (by rw [hzt]; exact htR) hzne).symm)]
    have hv' : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall ca |t|) :=
      hv.mono (Metric.closedBall_subset_closedBall (by rw [abs_of_pos ht]; exact htR))
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq hv'
  have hlog : Real.circleAverage (fun z : ℂ => Real.log ‖z - ca‖) ca t = Real.log t :=
    Real.circleAverage_const_on_circle (fun z hz => by
      rw [Metric.mem_sphere] at hz
      rw [dist_eq_norm] at hz
      rw [hz, abs_of_pos ht])
  have hfd : Real.circleAverage (fun z : ℂ => G (c.symm z)) ca t
      = Real.circleAverage (fun z : ℂ => G (c.symm z) + Real.log ‖z - ca‖) ca t
        - Real.circleAverage (fun z : ℂ => Real.log ‖z - ca‖) ca t := by
    rw [← Real.circleAverage_sub h1 h2]
    exact Real.circleAverage_congr_sphere
      (f₁ := fun z : ℂ => G (c.symm z))
      (f₂ := fun z : ℂ => G (c.symm z) + Real.log ‖z - ca‖ - Real.log ‖z - ca‖)
      (by intro z _; ring)
  rw [hfd, hsum, hlog]

/-- **The oscillation estimate on chart spheres.**  If `v` is harmonic on the closed disc of
radius `R` and agrees off `ca` with `G ∘ c.symm + log‖· - ca‖`, and `Ms`, `ms` bound `G` above and
below on the chart sphere of radius `R`, then the oscillation of `G` on the small chart sphere of
radius `r < R` is at most `θ (Ms - ms)` with `θ = (R+r)/(R-r) - (R-r)/(R+r) < 1`. -/
theorem osc_chartSphere_le {c : OpenPartialHomeomorph X ℂ} {ca : ℂ} {G : X → ℝ} {v : ℂ → ℝ}
    {r R Ms ms : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r < R)
    (hsubR : Metric.closedBall ca R ⊆ c.target)
    (hv : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall ca R))
    (hveq : ∀ z : ℂ, ‖z - ca‖ ≤ R → z ≠ ca → v z = G (c.symm z) + Real.log ‖z - ca‖)
    (hMs : ∀ y ∈ Submission.chartSphere c ca R, G y ≤ Ms)
    (hms : ∀ y ∈ Submission.chartSphere c ca R, ms ≤ G y) :
    ∀ x ∈ Submission.chartSphere c ca r, ∀ y ∈ Submission.chartSphere c ca r,
      G x - G y ≤ ((R + r) / (R - r) - (R - r) / (R + r)) * (Ms - ms) := by
  intro x hx y hy
  have hxnorm : ‖c x - ca‖ = r := by
    rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hx
    exact hx.2
  have hynorm : ‖c y - ca‖ = r := by
    rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hy
    exact hy.2
  have hxne : c x ≠ ca := by rw [← sub_ne_zero, ← norm_ne_zero_iff, hxnorm]; exact ne_of_gt hr
  have hyne : c y ≠ ca := by rw [← sub_ne_zero, ← norm_ne_zero_iff, hynorm]; exact ne_of_gt hr
  have hvx : v (c x) = G x + Real.log r := by
    rw [hveq (c x) (by rw [hxnorm]; exact hrR.le) hxne, hxnorm,
      c.left_inv (Submission.mem_chartSphere.mp hx).1]
  have hvy : v (c y) = G y + Real.log r := by
    rw [hveq (c y) (by rw [hynorm]; exact hrR.le) hyne, hynorm,
      c.left_inv (Submission.mem_chartSphere.mp hy).1]
  have hM : ∀ z : ℂ, dist z ca = R → v z ≤ Ms + Real.log R := by
    intro z hz
    have hzR : ‖z - ca‖ = R := by rw [← dist_eq_norm]; exact hz
    have hzt : z ∈ c.target := hsubR (by rw [Metric.mem_closedBall, dist_eq_norm, hzR])
    have hzne : z ≠ ca := by rw [← sub_ne_zero, ← norm_ne_zero_iff, hzR]; exact ne_of_gt hR
    rw [hveq z hzR.le hzne, hzR]
    have hzsp : c.symm z ∈ Submission.chartSphere c ca R := by
      rw [Submission.mem_chartSphere]
      exact ⟨c.map_target hzt, by rw [c.right_inv hzt, Metric.mem_sphere, dist_eq_norm]; exact hzR⟩
    linarith [hMs (c.symm z) hzsp]
  have hm : ∀ z : ℂ, dist z ca = R → ms + Real.log R ≤ v z := by
    intro z hz
    have hzR : ‖z - ca‖ = R := by rw [← dist_eq_norm]; exact hz
    have hzt : z ∈ c.target := hsubR (by rw [Metric.mem_closedBall, dist_eq_norm, hzR])
    have hzne : z ≠ ca := by rw [← sub_ne_zero, ← norm_ne_zero_iff, hzR]; exact ne_of_gt hR
    rw [hveq z hzR.le hzne, hzR]
    have hzsp : c.symm z ∈ Submission.chartSphere c ca R := by
      rw [Submission.mem_chartSphere]
      exact ⟨c.map_target hzt, by rw [c.right_inv hzt, Metric.mem_sphere, dist_eq_norm]; exact hzR⟩
    linarith [hms (c.symm z) hzsp]
  have hkey := Work.Drive.osc_sphere_le_of_harmonicOnNhd (u := v) (c := ca) (R := R) (ρ := r)
    (M := Ms + Real.log R) (m := ms + Real.log R) hR hr hrR hv hM hm (c x) (c y)
    (by rw [dist_eq_norm, hxnorm]) (by rw [dist_eq_norm, hynorm])
  rw [hvx, hvy] at hkey
  have hcancel : (Ms + Real.log R) - (ms + Real.log R) = Ms - ms := by ring
  rw [hcancel] at hkey
  linarith


/-- `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_abs_add'' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

/-- **The parabolic case of the local boundedness of the normalized exhaustion Green functions.**

`Ω n` is an exhaustion of a connected second countable `ℂ`-charted surface by nested relatively
compact open sets covering `X`, `G n` is the Green function of `Ω n` with pole `a` (in the sense of
`Work.SimplyConnected.ABS.IsGreenOn`, extended by `0` off `Ω n`), and the values `G n x` are
*unbounded* at every point `x ≠ a` (the classical parabolic case, which is what the negation of
"bounded at one point x₀ ≠ a" gives).  Conclusion: the normalized Green functions
`G n · - G n x₁` are uniformly bounded on every compact `K` disjoint from the pole.

This is the classical result of Ahlfors (*Conformal invariants*, Chapter 10) and Hubbard
(*Teichmuller theory* Vol. 1, Chapter 1): the normalized Green functions of an exhaustion of a
parabolic surface converge locally uniformly, which implies the statement.  Route: on a fixed chart
ball `D ∋ a` the functions `W n := G n + log ‖ζ - ζ a‖` are harmonic with `W n a = ρ n` (the Robin
constant), and `W n - ρ n` has zero mean on every circle about `a`; the oscillation of `W n` on
`∂D ρ` is therefore controlled by that on `∂D R` (`ρ < R`), and on a fixed annulus it is comparable
to the Dirichlet energy `∫ ‖∇G n‖²` there.  The maximum principle on the level-set domains
`{G n > t}` (whose Green function is `G n - t`) applied to `(G n - G m) - (ρ n - ρ m)` on the fixed
domain `Ω m` shows that a failure of boundedness produces a locally uniform limit of the positive
harmonic functions `(G n - G m)/(ρ n - ρ m)` which is not the constant `1`, and that classical
parabolicity (the vanishing of the harmonic measure of the ideal boundary) excludes.

`Work.Drive.greenExhaustion_hyperbolicCase` (in the same directory, sorry-free) is the companion
case: `∃ x₀ ≠ a, ∃ C, ∀ n, G n x₀ ≤ C`, proved via the uniform Harnack bound.  The two together
give the target `Work.Drive.normalizedGreenExhaustion_locallyBounded`. -/
theorem greenExhaustion_parabolicCase {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a x₁ : X} (hx₁ : x₁ ≠ a) {Ω : ℕ → Set X} {G : ℕ → X → ℝ}
    (hΩopen : ∀ n, IsOpen (Ω n)) (hΩcomp : ∀ n, IsCompact (closure (Ω n)))
    (hΩmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hΩcover : (⋃ n, Ω n) = Set.univ)
    (hgreen : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hvanish : ∀ n, ∀ x, x ∉ Ω n → G n x = 0)
    (hunbdd : ∀ x : X, x ≠ a → ∀ C : ℝ, ∃ n, C < G n x) :
    ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
      |G n x - G n x₁| ≤ C := by
  classical
  intro K hK hKsub
  -- ## 1. the chart at the pole, the radius `R`
  obtain ⟨R', hR'pos, hR'sub⟩ : ∃ R' : ℝ, 0 < R' ∧
      Metric.closedBall ((chartAt ℂ a) a) R' ⊆ (chartAt ℂ a).target := by
    have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target := mem_chart_target ℂ a
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (chartAt ℂ a).open_target _ hmem
    exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ a with hcdef
  set ca : ℂ := c a with hcadef
  have hca' : c a = ca := rfl
  have hasrc : a ∈ c.source := mem_chart_source ℂ a
  have hR'sub' : Metric.closedBall ca R' ⊆ c.target := hR'sub
  set R : ℝ := R' / 4 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hsub4R : Metric.closedBall ca (4 * R) ⊆ c.target := by
    refine (Metric.closedBall_subset_closedBall ?_).trans hR'sub'
    rw [hRdef]; linarith
  have hsubR' : Metric.closedBall ca R ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub4R
  have hcCBmono : ∀ {ρ ρ' : ℝ}, ρ ≤ ρ' →
      Submission.chartClosedBall c ca ρ ⊆ Submission.chartClosedBall c ca ρ' := by
    intro ρ ρ' hρ y hy
    rw [Submission.mem_chartClosedBall] at hy ⊢
    exact ⟨hy.1, Metric.closedBall_subset_closedBall hρ hy.2⟩
  -- ## 2. a member of the exhaustion containing the compact set
  have hKc : IsCompact (Submission.chartClosedBall c ca (4 * R) ∪ K ∪ {x₁}) :=
    ((Submission.isCompact_chartClosedBall hsub4R).union hK).union
      (Set.finite_singleton x₁).isCompact
  obtain ⟨m, hm⟩ := exists_subset_iUnion_of_isCompact'' hΩopen hΩmono hΩcover hKc
  have hA4m : Submission.chartClosedBall c ca (4 * R) ⊆ Ω m :=
    fun y hy => hm (Or.inl (Or.inl hy))
  have hKm : K ⊆ Ω m := fun y hy => hm (Or.inl (Or.inr hy))
  have hx₁m : x₁ ∈ Ω m := hm (Or.inr rfl)
  have ham : a ∈ Ω m := hA4m (by
    rw [Submission.mem_chartClosedBall]
    exact ⟨hasrc, by rw [hca', Metric.mem_closedBall, dist_self]; linarith⟩)
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro p q hpq
    induction hpq with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hΩmono _)
  have hΩm_pre : IsPreconnected (Ω m) := by
    rcases eq_or_ne (Ω m) Set.univ with h | h
    · rw [h]; exact PreconnectedSpace.isPreconnected_univ
    · exact Work.SimplyConnected.ABS.isPreconnected_of_isGreenOn (hΩopen m) h (hgreen m)
  -- ## 3. the small radius `s` avoiding `K ∪ {x₁}`
  have hKUclosed : IsClosed (K ∪ {x₁}) := (hK.union (Set.finite_singleton x₁).isCompact).isClosed
  have haNotK : a ∉ K ∪ {x₁} := by
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => (hKsub h).2 rfl, fun h => hx₁ h.symm⟩
  have hUnhds : ((K ∪ {x₁})ᶜ : Set X) ∈ 𝓝 a :=
    hKUclosed.isOpen_compl.mem_nhds (by simpa using haNotK)
  have hsymm_ca : c.symm ca = a := by rw [hcadef]; exact c.left_inv hasrc
  have hsymm_cont : ContinuousAt c.symm ca := by
    have h2 : ContinuousAt c.symm (c a) := c.continuousAt_symm (c.map_source hasrc)
    simpa [hcadef] using h2
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (hsymm_cont.preimage_mem_nhds (by rw [hsymm_ca]; exact hUnhds))
  set s : ℝ := min (R / 4) (δ / 2) with hsdef
  have hs : 0 < s := lt_min (by linarith) (by linarith)
  have hsR : s ≤ R / 4 := min_le_left _ _
  have hsδ : s ≤ δ / 2 := min_le_right _ _
  have hsubs : Metric.closedBall ca s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub4R
  have hAs_sub : Submission.chartClosedBall c ca s ⊆ Submission.chartClosedBall c ca (4 * R) := by
    intro y hy
    rw [Submission.mem_chartClosedBall] at hy ⊢
    exact ⟨hy.1, Metric.closedBall_subset_closedBall (by linarith) hy.2⟩
  have hAs_Ωm : Submission.chartClosedBall c ca s ⊆ Ω m := hAs_sub.trans hA4m
  have hAs_disj : ∀ y ∈ Submission.chartClosedBall c ca s, y ∉ K ∪ {x₁} := by
    intro y hy hyKU
    rw [Submission.mem_chartClosedBall] at hy
    have h1 : c y ∈ Metric.ball ca δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h2 := hy.2
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      linarith
    have h3 : c.symm (c y) ∈ (K ∪ {x₁})ᶜ := hδsub h1
    rw [c.left_inv hy.1] at h3
    exact h3 hyKU
  -- ## 4. the fixed Harnack region `U'`, the base point `y₀`, the Harnack constant `N`
  set U' : Set X := Ω m \ Submission.chartClosedBall c ca s with hU'def
  have hU'open : IsOpen U' := (hΩopen m).sdiff (Submission.isClosed_chartClosedBall hsubs)
  have hU'pre : IsPreconnected U' :=
    Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall (hΩopen m) hΩm_pre hsubs hAs_Ωm
  have hcaRs : ca + (R : ℂ) ∈ c.target := hsub4R (Metric.mem_closedBall.mpr (by
    rw [dist_eq_norm]
    have h1 : ca + (R : ℂ) - ca = (R : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    linarith))
  set y₀ : X := c.symm (ca + (R : ℂ)) with hy₀def
  have hy₀c : c y₀ = ca + (R : ℂ) := c.right_inv hcaRs
  have hy₀norm : ‖c y₀ - ca‖ = R := by
    rw [hy₀c]
    have h1 : ca + (R : ℂ) - ca = (R : ℂ) := by ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hy₀S : y₀ ∈ Submission.chartSphere c ca R := by
    rw [Submission.mem_chartSphere]
    exact ⟨c.map_target hcaRs, by rw [Metric.mem_sphere, dist_eq_norm]; exact hy₀norm⟩
  have hy₀U' : y₀ ∈ U' := by
    refine ⟨hA4m ?_, ?_⟩
    · rw [Submission.mem_chartClosedBall]
      exact ⟨c.map_target hcaRs,
        by rw [Metric.mem_closedBall, dist_eq_norm, hy₀norm]; linarith⟩
    · intro hyA
      rw [Submission.mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm, hy₀norm] at hyA
      linarith [hyA.2, hsR, hR]
  have hK'comp : IsCompact (Submission.chartSphere c ca R ∪ K ∪ {x₁}) :=
    ((isCompact_chartSphere_aux hsubR').union hK).union (Set.finite_singleton x₁).isCompact
  have hK'U' : Submission.chartSphere c ca R ∪ K ∪ {x₁} ⊆ U' := by
    intro y hy
    rcases hy with (hyS | hyK) | hyx
    · have hynorm : ‖c y - ca‖ = R := by
        rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hyS
        exact hyS.2
      refine ⟨hA4m ?_, ?_⟩
      · rw [Submission.mem_chartClosedBall]
        exact ⟨(Submission.mem_chartSphere.mp hyS).1,
          by rw [Metric.mem_closedBall, dist_eq_norm, hynorm]; linarith⟩
      · intro hyA
        rw [Submission.mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm, hynorm] at hyA
        linarith [hyA.2, hsR, hR]
    · exact ⟨hKm hyK, fun hyA => hAs_disj y hyA (Or.inl hyK)⟩
    · rw [Set.mem_singleton_iff] at hyx
      rw [hyx]
      exact ⟨hx₁m, fun hyA => hAs_disj x₁ hyA (Or.inr rfl)⟩
  obtain ⟨N, hN⟩ := Work.SimplyConnected.ABS.harnack_uniform_bound_of_preconnected
    hU'open hU'pre hy₀U' hK'comp hK'U'
  -- ## 5. the inner radius `r`
  set r : ℝ := min s (R / (100 * 25 ^ (2 * N))) with hrdef
  have hr : 0 < r := lt_min hs (by positivity)
  have hr_s : r ≤ s := min_le_left _ _
  have hr_R100 : r ≤ R / (100 * 25 ^ (2 * N)) := min_le_right _ _
  have h25N : (1 : ℝ) ≤ 25 ^ (2 * N) := one_le_pow₀ (by norm_num)
  have hr4 : r ≤ R / 4 := le_trans hr_s hsR
  have hrR : r < R := lt_of_le_of_lt hr4 (by linarith)
  have hsubr : Metric.closedBall ca r ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hsub4R
  have hAr_sub : Submission.chartClosedBall c ca r ⊆ Submission.chartClosedBall c ca s := by
    intro y hy
    rw [Submission.mem_chartClosedBall] at hy ⊢
    exact ⟨hy.1, Metric.closedBall_subset_closedBall hr_s hy.2⟩
  have hAr_Ωm : Submission.chartClosedBall c ca r ⊆ Ω m := hAr_sub.trans hAs_Ωm
  -- ## 6. the constant `θ` and `θ * 25 ^ (2N) ≤ 1/2`
  set θ : ℝ := (R + r) / (R - r) - (R - r) / (R + r) with hθdef
  have hθK : θ * (25 : ℝ) ^ (2 * N) ≤ 1 / 2 := by
    have h1 : θ ≤ 8 * r / R := by
      rw [hθdef]
      have h1a : (0 : ℝ) < R - r := by linarith
      have h1b : (0 : ℝ) < R + r := by linarith
      rw [div_sub_div _ _ (ne_of_gt h1a) (ne_of_gt h1b)]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (R - r) * (R + r)) hR]
      have e1 : (R + r) * (R + r) - (R - r) * (R - r) = 4 * R * r := by ring
      have e2 : 8 * r * ((R - r) * (R + r)) = 8 * r * (R ^ 2 - r ^ 2) := by ring
      rw [e1, e2]
      have hsq : r ^ 2 ≤ R ^ 2 / 16 := by nlinarith [hr4, hr, hR]
      nlinarith [hsq, hR, hr]
    have hrN : r * (25 : ℝ) ^ (2 * N) ≤ R / 100 := by
      calc r * 25 ^ (2 * N) ≤ (R / (100 * 25 ^ (2 * N))) * 25 ^ (2 * N) :=
            mul_le_mul_of_nonneg_right hr_R100 (by positivity)
        _ = R / 100 := by
            rw [div_mul_eq_mul_div]
            field_simp
    have h2 : 8 * r / R * (25 : ℝ) ^ (2 * N) ≤ 1 / 2 := by
      have h3 : 8 * r / R * 25 ^ (2 * N) = 8 * (r * 25 ^ (2 * N)) / R := by ring
      rw [h3]
      calc 8 * (r * 25 ^ (2 * N)) / R ≤ 8 * (R / 100) / R := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hR)
            linarith
        _ = 8 / 100 := by field_simp
        _ ≤ 1 / 2 := by norm_num
    calc θ * 25 ^ (2 * N) ≤ (8 * r / R) * 25 ^ (2 * N) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 / 2 := h2
  have hLnonneg : 0 ≤ Real.log (R / r) := Real.log_nonneg (by
    rw [le_div_iff₀ hr, one_mul]
    exact hrR.le)
  -- ## 7. the main estimate for `n ≥ m`
  have hmain : ∀ n : ℕ, m ≤ n → ∀ x ∈ K,
      |G n x - G n x₁| ≤ 2 * (25 : ℝ) ^ (2 * N) * Real.log (R / r) := by
    intro n hmn x hxK
    have hΩmn : Ω m ⊆ Ω n := hmono' m n hmn
    have hAn : Submission.chartClosedBall c ca r ⊆ Ω n := hAr_Ωm.trans hΩmn
    have hharmn : Submission.HarmonicOnX (G n) (Ω n \ {a}) := (hgreen n).2.1
    have hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Ω n) a (G n) := (hgreen n).2.2.2
    have hdecayn := (hgreen n).2.2.1
    -- the chart-local harmonic extension of the pole
    have hballR₂ : Submission.chartBall c ca (4 * R) \ {a} ⊆ Ω n := by
      intro y hy
      have hy4 : y ∈ Submission.chartClosedBall c ca (4 * R) := by
        have hy1 : y ∈ Submission.chartBall c ca (4 * R) := hy.1
        rw [Submission.mem_chartBall] at hy1
        rw [Submission.mem_chartClosedBall]
        exact ⟨hy1.1, Metric.ball_subset_closedBall hy1.2⟩
      exact hΩmn (hA4m hy4)
    obtain ⟨v, hvharm, hveq⟩ := chartLocalGreenExtension (a := a) (Ω := Ω n) (G := G n)
      (R₁ := 2 * R) (R₂ := 4 * R) (by linarith) (by linarith) hsub4R hballR₂ hharmn hpole
    have hvball : InnerProductSpace.HarmonicOnNhd v (Metric.closedBall ca R) := by
      intro z hz
      refine hvharm z ?_
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      linarith
    have hveqR : ∀ z : ℂ, ‖z - ca‖ ≤ R → z ≠ ca →
        v z = G n (c.symm z) + Real.log ‖z - ca‖ := by
      intro z hz hzne
      exact hveq z (by linarith) hzne
    -- the extremal points on the small chart sphere
    have hScomp : IsCompact (Submission.chartSphere c ca r) := isCompact_chartSphere_aux hsubr
    have hcaR_t : ca + (r : ℂ) ∈ c.target := hsub4R (Metric.mem_closedBall.mpr (by
      rw [dist_eq_norm]
      have h1 : ca + (r : ℂ) - ca = (r : ℂ) := by ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      linarith))
    have hSne : (Submission.chartSphere c ca r).Nonempty :=
      ⟨c.symm (ca + (r : ℂ)), by
        rw [Submission.mem_chartSphere]
        exact ⟨c.map_target hcaR_t, by
          rw [c.right_inv hcaR_t, Metric.mem_sphere, dist_eq_norm]
          have h1 : ca + (r : ℂ) - ca = (r : ℂ) := by ring
          rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]⟩⟩
    have hScont : ContinuousOn (G n) (Submission.chartSphere c ca r) := by
      intro y hy
      obtain ⟨hysrc, hysph⟩ := Submission.mem_chartSphere.mp hy
      have hynorm : ‖c y - ca‖ = r := by
        rw [Metric.mem_sphere, dist_eq_norm] at hysph
        exact hysph
      have hya : y ≠ a := by
        intro hcon
        rw [hcon, hca', sub_self, norm_zero] at hynorm
        linarith
      exact ((hharmn y ⟨hAn (Submission.chartSphere_subset_chartClosedBall c ca r hy), hya⟩).continuousAt).continuousWithinAt
    obtain ⟨xmax, hxmaxS, hxmax⟩ := hScomp.exists_isMaxOn hSne hScont
    obtain ⟨xmin, hxminS, hxmin⟩ := hScomp.exists_isMinOn hSne hScont
    set Mv : ℝ := G n xmax with hMvdef
    set mv : ℝ := G n xmin with hmvdef
    have hMv0 : 0 ≤ Mv := by
      rw [hMvdef]
      have hynorm : ‖c xmax - ca‖ = r := by
        rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hxmaxS
        exact hxmaxS.2
      refine le_of_lt ((hgreen n).1 xmax
        (hAn (Submission.chartSphere_subset_chartClosedBall c ca r hxmaxS)) ?_)
      intro hcon
      rw [hcon, hca', sub_self, norm_zero] at hynorm
      linarith
    have hmvMv : mv ≤ Mv := by
      rw [hmvdef, hMvdef]
      exact hxmin hxmaxS
    -- the free upper bound `G n ≤ Mv` outside the small chart ball
    have hGle : ∀ y ∈ Ω n \ Submission.chartClosedBall c ca r, G n y ≤ Mv := by
      refine le_max_chartSphere_of_isGreenOn hr hsubr (hΩopen n) (hΩcomp n) hharmn hdecayn
        hAn hasrc hca' hMv0 ?_
      intro y hy
      rw [hMvdef]
      exact hxmax hy
    -- the escape function
    set Ψ : X → ℝ := fun y => Mv - G n y with hΨdef
    have haA : a ∈ Submission.chartClosedBall c ca r := by
      rw [Submission.mem_chartClosedBall]
      exact ⟨hasrc, by rw [hca', Metric.mem_closedBall, dist_self]; linarith⟩
    have hsubU : Ω n \ Submission.chartClosedBall c ca r ⊆ Ω n \ {a} :=
      Set.sdiff_subset_sdiff subset_rfl (Set.singleton_subset_iff.mpr haA)
    have hfun : ((fun _ : X => Mv) - (G n)) = Ψ := by
      rw [hΨdef]; funext y; rfl
    have hΨharm : Submission.HarmonicOnX Ψ (Ω n \ Submission.chartClosedBall c ca r) := by
      rw [← hfun]
      exact (Submission.harmonicOnX_const Mv).sub (hharmn.mono hsubU)
    have hU'U : U' ⊆ Ω n \ Submission.chartClosedBall c ca r := by
      intro y hy
      exact ⟨hΩmn hy.1, fun hyA => hy.2 (hAr_sub hyA)⟩
    have hΨU' : Submission.HarmonicOnX Ψ U' := hΨharm.mono hU'U
    have hΨnonneg : ∀ y ∈ U', 0 ≤ Ψ y := by
      intro y hy
      have h1 : G n y ≤ Mv := hGle y (hU'U hy)
      rw [hΨdef]
      simp only
      linarith
    -- continuity of `G n ∘ c.symm` on the chart spheres
    have hccont : ∀ t : ℝ, 0 < t → t ≤ R →
        ContinuousOn (fun z : ℂ => G n (c.symm z)) (Metric.sphere ca t) := by
      intro t ht htR z hz
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      have hzt : z ∈ c.target := hsub4R (Metric.mem_closedBall.mpr (by
        rw [dist_eq_norm]; linarith))
      have hzsp : c.symm z ∈ Submission.chartClosedBall c ca (4 * R) := by
        rw [Submission.mem_chartClosedBall]
        refine ⟨c.map_target hzt, ?_⟩
        rw [Metric.mem_closedBall, dist_eq_norm, c.right_inv hzt]
        linarith
      have hzne : c.symm z ≠ a := by
        intro h
        have h2 : ‖c (c.symm z) - ca‖ = t := by rw [c.right_inv hzt]; exact hz
        rw [h, hca', sub_self, norm_zero] at h2
        linarith
      exact (((hharmn (c.symm z) ⟨hΩmn (hA4m hzsp), hzne⟩).continuousAt).comp
        (c.continuousAt_symm hzt)).continuousWithinAt
    -- the mean value identity
    have hmvId : Real.circleAverage (fun z : ℂ => G n (c.symm z)) ca R = v ca - Real.log R :=
      circleAverage_chart_symm_eq (c := c) (ca := ca) (G := G n) (v := v) (R := R)
        hR hvball hveqR hccont R hR le_rfl
    have hmvIdr : Real.circleAverage (fun z : ℂ => G n (c.symm z)) ca r = v ca - Real.log r :=
      circleAverage_chart_symm_eq (c := c) (ca := ca) (G := G n) (v := v) (R := R)
        hR hvball hveqR hccont r hr hrR.le
    -- the minimum is at most the average
    have havg_ge : mv ≤ Real.circleAverage (fun z : ℂ => G n (c.symm z)) ca r := by
      have hmono := Real.circleAverage_mono (c := ca) (R := r)
        (f₁ := fun _ : ℂ => mv) (f₂ := fun z : ℂ => G n (c.symm z))
        (ContinuousOn.circleIntegrable (le_of_lt hr) continuousOn_const)
        (ContinuousOn.circleIntegrable (le_of_lt hr) (hccont r hr hrR.le))
        (fun z hz => by
          rw [Metric.mem_sphere] at hz
          have hzr : dist z ca = r := by rw [hz, abs_of_pos hr]
          have hzt : z ∈ c.target := hsub4R (Metric.mem_closedBall.mpr (by
            rw [dist_eq_norm]
            rw [dist_eq_norm] at hzr
            linarith))
          have hzsp : c.symm z ∈ Submission.chartSphere c ca r := by
            rw [Submission.mem_chartSphere]
            exact ⟨c.map_target hzt, by
              rw [c.right_inv hzt, Metric.mem_sphere, dist_eq_norm]
              rw [dist_eq_norm] at hzr
              exact hzr⟩
          rw [hmvdef]
          exact hxmin hzsp)
      rwa [Real.circleAverage_const] at hmono
    -- the average of the escape function on the outer circle
    have havgΨ : Real.circleAverage (fun z : ℂ => Mv - G n (c.symm z)) ca R
        ≤ (Mv - mv) + Real.log (R / r) := by
      have hsub := Real.circleAverage_sub (c := ca) (R := R)
        (f₁ := fun _ : ℂ => Mv) (f₂ := fun z : ℂ => G n (c.symm z))
        (ContinuousOn.circleIntegrable (le_of_lt hR) continuousOn_const)
        (ContinuousOn.circleIntegrable (le_of_lt hR) (hccont R hR le_rfl))
      have heq : Real.circleAverage (fun z : ℂ => Mv - G n (c.symm z)) ca R
          = Mv - Real.circleAverage (fun z : ℂ => G n (c.symm z)) ca R := by
        rw [show (fun z : ℂ => Mv - G n (c.symm z))
              = (fun _ : ℂ => Mv) - (fun z : ℂ => G n (c.symm z)) from rfl, hsub,
          Real.circleAverage_const]
      rw [heq, hmvId]
      have hlog : Real.log R - Real.log r = Real.log (R / r) :=
        (Real.log_div (ne_of_gt hR) (ne_of_gt hr)).symm
      have h2 : mv + Real.log r ≤ v ca := by linarith [havg_ge, hmvIdr]
      linarith
    -- the Harnack bounds
    have hSRcomp : IsCompact (Submission.chartSphere c ca R) := isCompact_chartSphere_aux hsubR'
    have hSRne : (Submission.chartSphere c ca R).Nonempty := ⟨y₀, hy₀S⟩
    have hSRcontG : ContinuousOn (G n) (Submission.chartSphere c ca R) := by
      intro y hy
      obtain ⟨hysrc, hysph⟩ := Submission.mem_chartSphere.mp hy
      have hynorm : ‖c y - ca‖ = R := by
        rw [Metric.mem_sphere, dist_eq_norm] at hysph
        exact hysph
      have hya : y ≠ a := by
        intro hcon
        rw [hcon, hca', sub_self, norm_zero] at hynorm
        linarith
      exact ((hharmn y ⟨hΩmn (hA4m (hcCBmono (by linarith)
        (Submission.chartSphere_subset_chartClosedBall c ca R hy))), hya⟩).continuousAt).continuousWithinAt
    have hSRcontΨ : ContinuousOn Ψ (Submission.chartSphere c ca R) := by
      intro y hy
      show ContinuousWithinAt (fun z => Mv - G n z) (Submission.chartSphere c ca R) y
      exact continuousWithinAt_const.sub (hSRcontG y hy)
    obtain ⟨ymin, hyminS, hymin⟩ := hSRcomp.exists_isMinOn hSRne hSRcontΨ
    have hN1 : ∀ y ∈ Submission.chartSphere c ca R ∪ K ∪ {x₁}, Ψ y ≤ 25 ^ N * Ψ y₀ :=
      fun y hy => (hN y hy Ψ hΨU' hΨnonneg).1
    have hN2 : Ψ y₀ ≤ 25 ^ N * Ψ ymin :=
      (hN ymin (Or.inl (Or.inl hyminS)) Ψ hΨU' hΨnonneg).2
    have hminavg : Ψ ymin ≤ Real.circleAverage (fun z : ℂ => Mv - G n (c.symm z)) ca R := by
      have hmono := Real.circleAverage_mono (c := ca) (R := R)
        (f₁ := fun _ : ℂ => Ψ ymin) (f₂ := fun z : ℂ => Mv - G n (c.symm z))
        (ContinuousOn.circleIntegrable (le_of_lt hR) continuousOn_const)
        (ContinuousOn.circleIntegrable (le_of_lt hR)
          (continuousOn_const.sub (hccont R hR le_rfl)))
        (fun z hz => by
          rw [Metric.mem_sphere] at hz
          have hzr : dist z ca = R := by rw [hz, abs_of_pos hR]
          have hzt : z ∈ c.target := hsub4R (Metric.mem_closedBall.mpr (by
            rw [dist_eq_norm]; rw [dist_eq_norm] at hzr; linarith))
          have hzsp : c.symm z ∈ Submission.chartSphere c ca R := by
            rw [Submission.mem_chartSphere]
            exact ⟨c.map_target hzt, by
              rw [c.right_inv hzt, Metric.mem_sphere, dist_eq_norm]
              rw [dist_eq_norm] at hzr
              exact hzr⟩
          exact hymin hzsp)
      rwa [Real.circleAverage_const] at hmono
    have hK1 : ∀ y ∈ Submission.chartSphere c ca R ∪ K ∪ {x₁},
        Ψ y ≤ 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) := by
      intro y hy
      have h1 := hN1 y hy
      have h2 : Ψ y₀ ≤ 25 ^ N * ((Mv - mv) + Real.log (R / r)) := by
        have h3 : Ψ ymin ≤ (Mv - mv) + Real.log (R / r) := le_trans hminavg havgΨ
        calc Ψ y₀ ≤ 25 ^ N * Ψ ymin := hN2
          _ ≤ 25 ^ N * ((Mv - mv) + Real.log (R / r)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      calc Ψ y ≤ 25 ^ N * Ψ y₀ := h1
        _ ≤ 25 ^ N * (25 ^ N * ((Mv - mv) + Real.log (R / r))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) := by
            rw [← mul_assoc, ← pow_add, show N + N = 2 * N from by ring]
    -- the oscillation on the small sphere
    obtain ⟨yM, hyMS, hyM⟩ := hSRcomp.exists_isMaxOn hSRne hSRcontG
    obtain ⟨ym, hymS, hym⟩ := hSRcomp.exists_isMinOn hSRne hSRcontG
    set Ms : ℝ := G n yM with hMsdef
    set ms : ℝ := G n ym with hmsdef
    have hSRsub : Submission.chartSphere c ca R ⊆ Ω n \ Submission.chartClosedBall c ca r := by
      intro y hy
      refine ⟨hΩmn (hA4m (hcCBmono (by linarith)
        (Submission.chartSphere_subset_chartClosedBall c ca R hy))), ?_⟩
      intro hyA
      rw [Submission.mem_chartClosedBall, Metric.mem_closedBall, dist_eq_norm] at hyA
      rw [Submission.mem_chartSphere, Metric.mem_sphere, dist_eq_norm] at hy
      linarith [hyA.2, hy.2, hrR]
    have hMsMv : Ms ≤ Mv := by
      rw [hMsdef]
      exact hGle yM (hSRsub hyMS)
    have hoscr : Mv - mv ≤ θ * (Ms - ms) := by
      rw [hθdef]
      have h := osc_chartSphere_le (c := c) (ca := ca) (G := G n) (v := v) (r := r) (R := R)
        (Ms := Ms) (ms := ms) hr hR hrR hsubR' hvball hveqR
        (fun y hy => by rw [hMsdef]; exact hyM hy)
        (fun y hy => by rw [hmsdef]; exact hym hy)
        xmax hxmaxS xmin hxminS
      rw [hMvdef, hmvdef]
      exact h
    have hoscR : Ms - ms ≤ 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) := by
      have h := hK1 ym (Or.inl (Or.inl hymS))
      have h' : Ψ ym = Mv - ms := by rw [hΨdef, hmsdef]
      rw [h'] at h
      linarith [h, hMsMv]
    have hθnonneg : 0 ≤ θ := by
      rw [hθdef]
      have h1 : 0 < R - r := by linarith
      have h2 : 0 < R + r := by linarith
      have h3 : (R - r) / (R + r) ≤ (R + r) / (R - r) := by
        rw [div_le_div_iff₀ h2 h1]; nlinarith
      linarith
    have hfinal : Mv - mv ≤ Real.log (R / r) := by
      have h1 : Mv - mv ≤ θ * (25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r))) :=
        le_trans hoscr (mul_le_mul_of_nonneg_left hoscR hθnonneg)
      have h2 : θ * (25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)))
          = (θ * 25 ^ (2 * N)) * ((Mv - mv) + Real.log (R / r)) := by ring
      have h3 : (θ * 25 ^ (2 * N)) * ((Mv - mv) + Real.log (R / r))
          ≤ (1 / 2) * ((Mv - mv) + Real.log (R / r)) :=
        mul_le_mul_of_nonneg_right hθK (by linarith)
      linarith
    -- the conclusion
    have hxU' : x ∈ U' :=
      ⟨hKm hxK, fun hxAs => hAs_disj x hxAs (Or.inl hxK)⟩
    have hx₁U' : x₁ ∈ U' := ⟨hx₁m, fun hxAs => hAs_disj x₁ hxAs (Or.inr rfl)⟩
    have h0x : 0 ≤ Ψ x := hΨnonneg x hxU'
    have h0x₁ : 0 ≤ Ψ x₁ := hΨnonneg x₁ hx₁U'
    have hcx : Ψ x ≤ 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) :=
      hK1 x (Or.inl (Or.inr hxK))
    have hcx₁ : Ψ x₁ ≤ 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) :=
      hK1 x₁ (Or.inr rfl)
    have hKpos : (0 : ℝ) ≤ 25 ^ (2 * N) := by positivity
    calc |G n x - G n x₁| = |Ψ x - Ψ x₁| := by
          have h : Ψ x - Ψ x₁ = -(G n x - G n x₁) := by
            rw [hΨdef]; simp only; ring
          rw [h, abs_neg]
      _ ≤ 25 ^ (2 * N) * ((Mv - mv) + Real.log (R / r)) := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith, by linarith⟩
      _ ≤ 25 ^ (2 * N) * (Real.log (R / r) + Real.log (R / r)) := by
          have h : (Mv - mv) + Real.log (R / r) ≤ Real.log (R / r) + Real.log (R / r) := by
            linarith [hfinal]
          exact mul_le_mul_of_nonneg_left h hKpos
      _ = 2 * (25 : ℝ) ^ (2 * N) * Real.log (R / r) := by ring
  -- ## 8. the finitely many remaining indices
  have hsingle : ∀ n : ℕ, ∃ B : ℝ, ∀ x ∈ K, |G n x - G n x₁| ≤ B := by
    intro n
    obtain ⟨Kc, hKccomp, hKcΩ, hKc⟩ := (hgreen n).2.2.1 1 one_pos
    have hKc' : ∀ x ∈ Ω n, 1 ≤ G n x → x ∈ Kc := by
      intro x hxΩ hxge
      by_contra hxKc
      exact absurd hxge (not_le.mpr (hKc x hxΩ hxKc))
    have hcont : ContinuousOn (G n) (K ∩ Kc) := by
      intro y hy
      have hyΩ : y ∈ Ω n := hKcΩ hy.2
      have hya : y ≠ a := fun h => (hKsub hy.1).2 h
      exact (((hgreen n).2.1 y ⟨hyΩ, hya⟩).continuousAt).continuousWithinAt
    obtain ⟨b, hb⟩ := (hK.inter_right hKccomp.isClosed).exists_bound_of_continuousOn hcont
    have hb' : ∀ x ∈ K ∩ Kc, G n x ≤ b := fun x hx =>
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb x hx)
    refine ⟨max 1 b + |G n x₁|, fun x hxK => ?_⟩
    by_cases hxΩ : x ∈ Ω n
    · have hxpos : 0 ≤ G n x := le_of_lt ((hgreen n).1 x hxΩ (fun h => (hKsub hxK).2 h))
      have hle : G n x ≤ max 1 b := by
        by_cases hge : 1 ≤ G n x
        · exact le_trans (hb' x ⟨hxK, hKc' x hxΩ hge⟩) (le_max_right _ _)
        · exact le_trans (le_of_lt (lt_of_not_ge hge)) (le_max_left _ _)
      calc |G n x - G n x₁| ≤ |G n x| + |G n x₁| := abs_sub_le_abs_add'' _ _
        _ = G n x + |G n x₁| := by rw [abs_of_nonneg hxpos]
        _ ≤ max 1 b + |G n x₁| := add_le_add hle le_rfl
    · have hx0 : G n x = 0 := hvanish n x hxΩ
      rw [hx0, zero_sub, abs_neg]
      exact le_add_of_nonneg_left (le_trans zero_le_one (le_max_left 1 b))
  choose B hB using hsingle
  by_cases hm0 : m = 0
  · exact ⟨2 * (25 : ℝ) ^ (2 * N) * Real.log (R / r), fun n x hxK => hmain n (by omega) x hxK⟩
  · have hne : (Finset.range m).Nonempty :=
      ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hm0)⟩
    refine ⟨max (2 * (25 : ℝ) ^ (2 * N) * Real.log (R / r))
      ((Finset.range m).sup' hne B), fun n x hxK => ?_⟩
    by_cases hn : n < m
    · exact le_trans (hB n x hxK)
        (le_trans (Finset.le_sup' B (Finset.mem_range.mpr hn)) (le_max_right _ _))
    · exact le_trans (hmain n (by omega) x hxK) (le_max_left _ _)

end Work.Drive
