import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Perron.globalizedBarrier
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts

/-!
# The Perron envelope is `< 1` somewhere, from a local barrier

This is the barrier step of the Anghel--Bruin--Stan Perron construction, now proved with the
*continuous* global barrier `Work.SimplyConnected.Perron.globalizedBarrier` (no
upper-semicontinuity argument is needed, contrary to the analysis in the docstring of
`ABS/dirichletSphereEnvelope_outerGap.lean`): compare every member of the Perron family with a
multiple of the barrier at a frontier point `p` (`limEnvelope_le_smul_of_barrier`), and evaluate at a
point of the annulus close to `p`, where the barrier is small.
-/

open Filter Set
open scoped Topology Manifold ContDiff

noncomputable section
open Classical

namespace Work.SimplyConnected.Perron

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The barrier step**: with a local barrier at every frontier point of `Ω`, the Perron envelope
of `U = Ω \ chartClosedBall c a s` with data `0` at `frontier Ω` is `< 1` at some point of `U`
(namely at a point of the annulus close to a frontier point `p`). -/
theorem limEnvelope_lt_one_of_localBarrier_clamp {Ω : Set X} (hΩo : IsOpen Ω)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    (hfr : (frontier Ω).Nonempty)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ z ∈ Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s,
      Submission.limEnvelope
        (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 z < 1 := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hcdef
  set a : ℂ := c x₀ with hadef
  set D : Set X := Submission.chartClosedBall c a s with hDdef
  set U : Set X := Ω \ D with hUdef
  have hsubs : Metric.closedBall a s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hDc : IsClosed D := Submission.isClosed_chartClosedBall hsubs
  have hDΩ : D ⊆ Ω := by
    intro y hy
    rw [hDdef] at hy
    exact hρΩ ⟨hy.1, Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hy.2) hsρ.le)⟩
  have hUo : IsOpen U := hΩo.sdiff hDc
  have hUcomp : IsCompact (closure U) := hcomp.of_isClosed_subset isClosed_closure (closure_mono Set.sdiff_subset)
  obtain ⟨p, hp⟩ := hfr
  obtain ⟨u, V, hVo, hpV, hsup, hpos, hcont, hup⟩ := hbar p hp
  obtain ⟨β, hβsup, hβ0, hβp, hβcont, hβpos, hβsmall⟩ :=
    globalizedBarrier hΩo hp ⟨u, V, hVo, hpV, hsup, hpos, hcont, hup⟩
  -- the barrier is bounded below by a positive `m` on the inner chart sphere
  have hKsphΩ : Submission.chartSphere c a s ⊆ Ω := fun y hy =>
    hDΩ (Submission.chartSphere_subset_chartClosedBall c a s hy)
  have hKcontβ : ∀ ζ ∈ Submission.chartSphere c a s, ContinuousAt β ζ := fun ζ hζ =>
    hβcont.continuousAt (hΩo.mem_nhds (hKsphΩ hζ))
  obtain ⟨z₀, hz₀K, hz₀min⟩ := (Work.SimplyConnected.ABS.isCompact_chartSphere hsubs).exists_isMinOn
    (Work.SimplyConnected.ABS.chartSphere_nonempty hs hsubs) (hβcont.mono hKsphΩ)
  have hz₀Ω : z₀ ∈ Ω := hKsphΩ hz₀K
  have hz₀ne : z₀ ≠ p := fun h => hp.2 (by rw [hΩo.interior_eq]; exact h ▸ hz₀Ω)
  have hmpos : 0 < β z₀ := hβpos z₀ hz₀Ω hz₀ne
  have hmβ : ∀ ζ ∈ Submission.chartSphere c a s, β z₀ ≤ β ζ := fun ζ hζ => hz₀min hζ
  -- the Perron family and the comparison
  have hKfr : Submission.chartSphere c a s ⊆ frontier U :=
    Work.SimplyConnected.ABS.chartSphere_subset_frontier_sdiff_chartClosedBall hΩo hDΩ
  have hne' : (frontier U).Nonempty :=
    (Work.SimplyConnected.ABS.chartSphere_nonempty hs hsubs).mono hKfr
  have hzero : (fun _ : X => (0 : ℝ)) ∈ Submission.limFamily U f 1 :=
    ⟨(Submission.subharmonicOnX_const 0).mono (subset_univ U) continuousOn_const,
      fun _ => zero_le_one,
      fun ζ _ ε hε => by
        filter_upwards with z
        linarith [hf0 ζ, hε.le]⟩
  have hneF : (Submission.limFamily U f 1).Nonempty := ⟨_, hzero⟩
  have hβU : Submission.SuperharmonicOnX β U := hβsup.mono Set.sdiff_subset (hβcont.mono Set.sdiff_subset)
  have hβ0U : ∀ x ∈ U, 0 ≤ β x := fun x hx => hβ0 x hx.1
  have hf : ∀ ζ ∈ frontier U, ζ ∉ Submission.chartSphere c a s → f ζ ≤ 0 := by
    intro ζ hζU hζK
    have hζΩ : ζ ∈ frontier Ω := by
      rcases Work.SimplyConnected.ABS.frontier_sdiff_chartClosedBall_subset (Ω := Ω) hsubs hζU with h | h
      · exact h
      · exact absurd h hζK
    rw [hfbd ζ hζΩ]
  have hcmp := Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier (M := 1) hUo hUcomp hne'
    zero_le_one hneF hβU hβ0U hKfr hKcontβ hmpos hmβ hf
  -- a point of `U` close to `p`, where the barrier is below `β z₀`
  obtain ⟨V', hV', hV'small⟩ := hβsmall (β z₀) hmpos
  have hpD : p ∉ D := fun h => hp.2 (by rw [hΩo.interior_eq]; exact hDΩ h)
  have hV'' : V' \ D ∈ 𝓝 p := by
    have hmem : V' ∩ Dᶜ ∈ 𝓝 p := Filter.inter_mem hV' (hDc.isOpen_compl.mem_nhds hpD)
    simpa [Set.sdiff_eq] using hmem
  obtain ⟨z, hzVD, hzΩ⟩ := (mem_closure_iff_nhds.mp hp.1) (V' \ D) hV''
  obtain ⟨hzV', hzD⟩ := hzVD
  have hzU' : z ∈ U := by
    rw [hUdef, Set.mem_sdiff]
    exact ⟨hzΩ, hzD⟩
  have h1 : Submission.limEnvelope U f 1 z ≤ (1 / β z₀) * β z := hcmp z hzU'
  have h2 : β z < β z₀ := hV'small z ⟨hzΩ, hzV'⟩
  refine ⟨z, hzU', ?_⟩
  have h3 : (1 / β z₀) * β z < (1 / β z₀) * β z₀ :=
    mul_lt_mul_of_pos_left h2 (one_div_pos.mpr hmpos)
  have h4 : (1 / β z₀) * β z₀ = 1 := by field_simp
  linarith [h1, h3, h4]

end Work.SimplyConnected.Perron
