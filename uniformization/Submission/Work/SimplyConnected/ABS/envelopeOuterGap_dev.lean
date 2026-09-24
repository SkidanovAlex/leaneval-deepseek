import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.outerGapDesign
import Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts
import Submission.Work.SimplyConnected.ABS.isPreconnected_sdiff_chartClosedBall

/-!
# The outer gap for the Perron envelope on `Ω \ chartClosedBall`

Here we assemble the main theorem `Work.SimplyConnected.ABS.envelopeOuterGap_dev` from

* the topological fact that `Ω \ chartClosedBall c a s` is preconnected
  (`Work.SimplyConnected.ABS.isPreconnected_sdiff_chartClosedBall`),
* the classical Perron barrier argument giving a point of the region where the envelope is `< 1`
  (`Work.SimplyConnected.ABS.exists_limEnvelope_lt_one_of_barrier`),
* the strong maximum principle, which then forces the envelope to be `< 1` on the whole region,
* compactness of the outer chart sphere, which upgrades this to a uniform gap.

-/

open Filter Set Metric

namespace Work.SimplyConnected.ABS

/-! ## The chart sphere is preconnected -/

theorem isPreconnected_chartSphere {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} (hsub : Metric.closedBall a ρ ⊆ c.target) :
    IsPreconnected (Submission.chartSphere c a ρ) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have heq : Submission.chartSphere c a ρ = c.symm '' Metric.sphere a ρ := by
    ext x
    constructor
    · rintro ⟨hxs, hx⟩
      exact ⟨c x, hx, c.left_inv hxs⟩
    · rintro ⟨w, hw, rfl⟩
      have hwT : w ∈ c.target := hsub (Metric.sphere_subset_closedBall hw)
      refine ⟨c.map_target hwT, ?_⟩
      simp only [Set.mem_preimage]
      rw [c.right_inv hwT]
      exact hw
  rw [heq]
  exact (isPreconnected_sphere hrank a ρ).image c.symm
    (c.continuousOn_symm.mono fun w hw => hsub (Metric.sphere_subset_closedBall hw))

/-! ## The strong maximum principle, in the form needed here -/

/-- If a function harmonic on a preconnected open set `U` is bounded above by `1` and is strictly
below `1` at one point of `U`, then it is strictly below `1` everywhere on `U`. -/
theorem harmonicOnX_lt_one_of_lt_one {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {U : Set X} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {u : X → ℝ} (hu : Submission.HarmonicOnX u U) (hle : ∀ x : X, u x ≤ 1) {z₀ : X}
    (hz₀ : z₀ ∈ U) (hz₀lt : u z₀ < 1) : ∀ x ∈ U, u x < 1 := by
  intro x hx
  by_contra hcon
  have hx1 : u x = 1 := le_antisymm (hle x) (not_lt.mp hcon)
  haveI : PreconnectedSpace U := (isPreconnected_iff_preconnectedSpace (s := U)).mp hUpc
  have hcont : Continuous (fun y : U => u y) :=
    continuousOn_iff_continuous_restrict.mp
      (fun y hy => (hu y hy).continuousAt.continuousWithinAt)
  set S : Set U := {y : U | u y = 1} with hSdef
  have hScl : IsClosed S := by
    have hSe : S = (fun y : U => u y) ⁻¹' ({1} : Set ℝ) := rfl
    rw [hSe]
    exact isClosed_singleton.preimage hcont
  have hSop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyU : (y : X) ∈ U := y.2
    have hyval : u (y : X) = 1 := hy
    obtain ⟨V, hVn, hVeq⟩ := Submission.SubharmonicOnXAt.eqOn_of_le
      ((hu (y : X) hyU).subharmonic) (hUo.mem_nhds hyU)
      (fun z _ => by rw [hyval]; exact hle z)
    obtain ⟨W, hWV, hWo, hyW⟩ := mem_nhds_iff.mp hVn
    refine Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hyW) ?_
    intro z hz
    rw [hSdef]
    exact (hVeq z (hWV hz)).trans hyval
  rcases isClopen_iff.mp ⟨hScl, hSop⟩ with h | h
  · have hmem : (⟨x, hx⟩ : U) ∈ S := by rw [hSdef]; simpa using hx1
    rw [h] at hmem
    exact (Set.notMem_empty _ hmem).elim
  · have hmem : (⟨z₀, hz₀⟩ : U) ∈ S := by rw [h]; exact Set.mem_univ _
    have hz1 : u z₀ = 1 := by rw [hSdef] at hmem; exact hmem
    linarith

/-! ## Temporary local copy of the delegated barrier lemma -/

theorem exists_limEnvelope_lt_one_of_barrier_TEMP {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {x₀ : X} (hx₀ : x₀ ∈ Ω) {ρ s : ℝ} (hρ : 0 < ρ)
    (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    (hfr : (frontier Ω).Nonempty)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z) (hf1 : ∀ z : X, f z ≤ 1)
    (hfsph : ∀ z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, f z = 1)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ z ∈ Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s,
      Submission.limEnvelope
        (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 z < 1 := by sorry

/-- **Outer gap for the Perron envelope.** -/
theorem envelopeOuterGap_dev {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩne : Ω ≠ Set.univ)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    {s : ℝ} (hs : 0 < s) (hsρ : s < ρ)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z) (hf1 : ∀ z : X, f z ≤ 1)
    (hfsph : ∀ z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, f z = 1)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ θ : ℝ, 0 < θ ∧ 1 - θ ≥ 0 ∧
      ∀ x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s),
        x ∈ (chartAt ℂ x₀).source → ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ = ρ →
          Submission.limEnvelope
            (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x ≤ 1 - θ := by
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hcdef
  set a : ℂ := c x₀ with hadef
  set D : Set X := Submission.chartClosedBall c a s with hDdef
  set U : Set X := Ω \ D with hUdef
  set h : X → ℝ := Submission.limEnvelope U f 1 with hhdef
  -- basic facts about `D`, `U`
  have hsubs : Metric.closedBall a s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hDc : IsClosed D := Submission.isClosed_chartClosedBall hsubs
  have hDΩ : D ⊆ Ω := by
    intro y hy
    rw [hDdef] at hy
    exact hρΩ ⟨hy.1, Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hy.2) hsρ.le)⟩
  have hUo : IsOpen U := hΩo.sdiff hDc
  have hUpc : IsPreconnected U :=
    isPreconnected_sdiff_chartClosedBall hΩo hΩc.isPreconnected hs hsρ hρsub hρΩ
  -- frontier Ω is nonempty
  have hfr : (frontier Ω).Nonempty := by
    rcases Set.eq_empty_or_nonempty (frontier Ω) with h | h
    · exfalso
      rcases (frontier_eq_empty_iff (s := Ω)).mp h with h' | h'
      · exact hΩc.nonempty.ne_empty h'
      · exact hΩne h'
    · exact h
  -- the Perron family is nonempty (the zero function is a member)
  have hzero : (fun _ : X => (0 : ℝ)) ∈ Submission.limFamily U f 1 :=
    ⟨(Submission.subharmonicOnX_const 0).mono (subset_univ U) continuousOn_const,
      fun _ => zero_le_one,
      fun ζ _ ε hε => by
        filter_upwards with z
        linarith [hf0 ζ, hε.le]⟩
  have hneF : (Submission.limFamily U f 1).Nonempty := ⟨_, hzero⟩
  have hharm : Submission.HarmonicOnX h U := Submission.harmonicOnX_limEnvelope hUo hneF
  have hleone : ∀ x : X, h x ≤ 1 := fun x =>
    Submission.upperEnvelope_le hneF (fun w hw x => Submission.limFamily_bound hw x) x
  -- some point of `U` where the envelope is `< 1`
  obtain ⟨z₀, hz₀U, hz₀lt⟩ :=
    exists_limEnvelope_lt_one_of_barrier_TEMP hΩo hx₀ hρ hs hsρ hρsub hρΩ hfr hf0 hf1 hfsph hfbd hbar
  have hlt1 : ∀ x ∈ U, h x < 1 :=
    harmonicOnX_lt_one_of_lt_one hUo hUpc hharm hleone hz₀U hz₀lt
  -- the outer chart sphere
  have hSsub : Submission.chartSphere c a ρ ⊆ U := by
    intro y hy
    obtain ⟨hysrc, hysph⟩ := Submission.mem_chartSphere.mp hy
    have hyDρ : y ∈ Submission.chartClosedBall c a ρ :=
      Submission.chartSphere_subset_chartClosedBall c a ρ hy
    refine ⟨hρΩ hyDρ, ?_⟩
    intro hyD
    rw [hDdef] at hyD
    have h1 : ‖c y - a‖ ≤ s := by
      have h := Metric.mem_closedBall.mp hyD.2
      simpa [dist_eq_norm] using h
    have h2 : ‖c y - a‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hysph
    linarith [h1, h2, hsρ]
  have hSne : (Submission.chartSphere c a ρ).Nonempty := chartSphere_nonempty hρ hρsub
  have hScont : ContinuousOn h (Submission.chartSphere c a ρ) := fun y hy =>
    ((hharm y (hSsub hy)).continuousAt).continuousWithinAt
  obtain ⟨y, hyS, hyMax⟩ := (isCompact_chartSphere hρsub).exists_isMaxOn hSne hScont
  have hyU : y ∈ U := hSsub hyS
  have hy0 : 0 ≤ h y := by
    have hle := Submission.limFamily_le_limEnvelope hUo hneF hzero y hyU
    simpa using hle
  have hy1 : h y < 1 := hlt1 y hyU
  refine ⟨(1 - h y) / 2, by linarith, by linarith, ?_⟩
  intro x hxU hxsrc hxsph
  have hxS : x ∈ Submission.chartSphere c a ρ := by
    rw [Submission.mem_chartSphere]
    exact ⟨hxsrc, by rw [Metric.mem_sphere, dist_eq_norm]; exact hxsph⟩
  have hxyle : h x ≤ h y := hyMax hxS
  have hx1 : h x ≤ 1 := hleone x
  linarith

end Work.SimplyConnected.ABS
