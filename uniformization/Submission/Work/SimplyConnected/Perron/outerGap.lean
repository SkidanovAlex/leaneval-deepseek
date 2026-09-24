import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.Perron.dirichletSphereEnvelopeFacts
import Submission.Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall
import Submission.Work.SimplyConnected.ABS.envelopeOuterGap_dev
import Submission.Work.SimplyConnected.Perron.limEnvelopeLtOne

/-!
# The outer gap for the Perron envelope on `Ω \ chartClosedBall`

The target `Work.SimplyConnected.ABS.dirichletSphereEnvelope_outerGap` is the "outer gap" step of
the Anghel–Bruin–Stan Perron construction (arXiv:2008.12189, Proposition 9): the Perron envelope
`u = limEnvelope U f 1` of the region `U = Ω \ chartClosedBall c a s` (data `1` on the inner chart
sphere, `0` on `frontier Ω`) is *uniformly* below `1` on the outer chart sphere of radius `ρ`.

The proof is assembled from three ingredients:

1. **Some point of `U` where the envelope is `< 1`** — the classical Perron barrier argument at a
   frontier point.  This is isolated here as `limEnvelope_lt_one_of_localBarrier`; see its docstring
   for the proof route and for the missing maximum principle for upper-semicontinuous functions.
2. **The strong maximum principle** on the preconnected open set `U`
   (`Work.SimplyConnected.ABS.Work.SimplyConnected.ABS.harmonicOnX_lt_one_of_lt_one`, proved in
   `Submission/Work/SimplyConnected/ABS/envelopeOuterGap_dev.lean`): a harmonic `u ≤ 1` which is
   `< 1` at one point of `U` is `< 1` everywhere on `U`.  Preconnectedness of `U` is
   `Work.SimplyConnected.ABS.Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall`, proved in this workspace: a
   closed chart disc does not disconnect a connected open surface.
3. **Compactness** of the outer chart sphere (`isCompact_chartSphere`, `chartSphere_nonempty`),
   upgrading the pointwise inequality to a uniform gap `θ > 0`.
-/

open Filter Set
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.Perron

/-! **The Perron barrier step.**  The limsup Perron envelope of `U = Ω \ chartClosedBall c a s`
with data `0` on `frontier Ω` is `< 1` at some point of `U`, provided `Ω` is Dirichlet regular
(`hbar`).

Intended proof (design note `MajorantRegDesign.lean` §1; docstring of
`Submission/Work/SimplyConnected/ABS/exists_limEnvelope_lt_one_of_barrier.lean`).

* Fix `p ∈ frontier Ω` with its local barrier `(u, V)` from `hbar`, and shrink `V` to a chart ball
  `B ∋ p` with `closure B ⊆ V` whose closure misses the inner sphere `chartSphere c a s`.
* Put `u' x := if x ∈ V then min (u x) C else C` for a constant `C > 0`.  Then `u'` is *upper
  semicontinuous* on `X`, satisfies the circle mean value inequality at every point of `Ω`
  (`Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev`), is nonnegative on `Ω`, and is `0` at
  `p`.
* For a Perron family member `v` and `λ := (M - a' + 1)/C`, the function `v - λ u'` is upper
  semicontinuous on `U`, satisfies the circle mean value inequality there, and has limsup `≤ a'` at
  every point of `frontier U`: at `frontier Ω` by the family condition and `u' ≥ 0`, at the inner
  sphere by `v ≤ M` and `u' = C` near it.
* Hence `limEnvelope U f 1 ≤ a' + λ u'` on `U`, and `u'` is small on `U` near `p`.

The **missing ingredient** is a maximum principle on a relatively compact region for *upper
semicontinuous* functions satisfying the circle mean value inequality (the classical definition of
superharmonicity); the workspace's `Submission.SubharmonicOnX.le_of_frontier_limsup` requires
continuity.  Its proof is that lemma's proof with continuity replaced by upper semicontinuity. -/


/-! **The outer gap for the Perron envelope.**  There is `θ > 0` with `1 - θ ≥ 0` and
`limEnvelope U f 1 x ≤ 1 - θ` for every `x ∈ U` on the outer chart sphere of radius `ρ`
(`U = Ω \ chartClosedBall c a s`, `c = chartAt ℂ x₀`, `a = c x₀`). -/
theorem dirichletSphereEnvelope_outerGap_aux {X : Type*} [TopologicalSpace X] [T2Space X]
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
  have hsubs : Metric.closedBall a s ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hDc : IsClosed D := Submission.isClosed_chartClosedBall hsubs
  have hDΩ : D ⊆ Ω := by
    intro y hy
    rw [hDdef] at hy
    exact hρΩ ⟨hy.1, Metric.mem_closedBall.mpr (le_trans (Metric.mem_closedBall.mp hy.2) hsρ.le)⟩
  have hUo : IsOpen U := hΩo.sdiff hDc
  have hUpc : IsPreconnected U :=
    Work.SimplyConnected.ABS.isPreconnected_diff_chartClosedBall hΩo hΩc.isPreconnected hsubs hDΩ
  have hfr : (frontier Ω).Nonempty := by
    rcases Set.eq_empty_or_nonempty (frontier Ω) with h | h
    · exfalso
      rcases (frontier_eq_empty_iff (s := Ω)).mp h with h' | h'
      · exact hΩc.nonempty.ne_empty h'
      · exact hΩne h'
    · exact h
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
  obtain ⟨z₀, hz₀U, hz₀lt⟩ :=
    limEnvelope_lt_one_of_localBarrier_clamp hΩo hcomp hx₀ hρ hs hsρ hρsub hρΩ hfr hf0 hfbd hbar
  have hlt1 : ∀ x ∈ U, h x < 1 :=
    Work.SimplyConnected.ABS.harmonicOnX_lt_one_of_lt_one hUo hUpc hharm hleone hz₀U hz₀lt
  have hSsub : Submission.chartSphere c a ρ ⊆ U := by
    intro y hy
    obtain ⟨hysrc, hysph⟩ := Submission.mem_chartSphere.mp hy
    have hyDρ : y ∈ Submission.chartClosedBall c a ρ :=
      Submission.chartSphere_subset_chartClosedBall c a ρ hy
    refine ⟨hρΩ hyDρ, ?_⟩
    intro hyD
    rw [hDdef] at hyD
    have h1 : ‖c y - a‖ ≤ s := by
      have := Metric.mem_closedBall.mp hyD.2
      simpa [dist_eq_norm] using this
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
  linarith

end Work.SimplyConnected.Perron
