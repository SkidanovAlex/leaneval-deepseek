import Mathlib
import Submission.Work.SimplyConnected.ABS.MajorantBarrierDefs
import Submission.Work.SimplyConnected.Perron.dirichletSphereEnvelopeFacts
import Submission.Work.SimplyConnected.Perron.outerGap
import Submission.Work.SimplyConnected.ABS.piecewiseBarrier_subharmonic
import Submission.Sweep
import Submission.GreenConditional
import Submission.DirichletX

/-!
# A superharmonic majorant of the clamped logarithmic potential

(Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, arXiv:2008.12189,
Proposition 9 — the Perron construction of the Green function of a regular bounded sub-surface.)

Let `Ω` be a relatively compact, connected, proper open subset of a Riemann surface `X` which is
Dirichlet regular at every frontier point (`hbar`), let `x₀ ∈ Ω` and `ρ > 0` with the closed chart
ball of radius `ρ` around `x₀` contained in `Ω`.  This module constructs a superharmonic function
`W` on `Ω ∖ {x₀}` which dominates the clamped logarithmic potential
`chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ`, has a logarithmic pole of order at most one
at `x₀` and tends to `0` at the frontier of `Ω`.

The construction follows the classical route: pick `s = ρ/2`, let `h₁` be the Perron envelope on
`Ω ∖ chartClosedBall c a s` with data `1` on the inner chart sphere and `0` on `∂Ω`
(`Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts`, with the uniform gap
`Submission.Work.SimplyConnected.ABS.dirichletSphereEnvelope_outerGap` on the outer chart sphere),
take the piecewise barrier `hb = piecewiseBarrier c a ρ s A B h₁` of
`Submission.Work.SimplyConnected.ABS.MajorantBarrierDefs` — the logarithmic potential on the inner
chart ball, the pointwise maximum of the potential and `-B * h₁` on the rest of the chart ball and
`-B * h₁` outside it, with constants `A`, `B` chosen from the gap — and set
`W = - sweep hb (Ω ∖ {x₀})`, the negative of the least superharmonic majorant of `hb`.  The barrier
`hb` is subharmonic (`Submission.Work.SimplyConnected.ABS.piecewiseBarrier_subharmonic`), so the
sweep is harmonic and `W` is superharmonic; the domination of `chartLogClamp` follows from the
explicit member `-chartLogClamp` of the sweep family, the pole bound from `W ≤ -hb`, and the decay
from `W ≤ -hb ≤ B * h₁` together with the vanishing of `h₁` at the frontier of `Ω`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.Perron

theorem exists_superharmonic_majorant_chartLogClamp_aux {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩne : Ω ≠ Set.univ)
    (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    (hbar : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ W : X → ℝ, Submission.SuperharmonicOnX W (Ω \ {x₀}) ∧
      (∀ x ∈ Ω \ {x₀}, Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ x ≤ W x) ∧
      (∃ C : ℝ, ∃ V : Set X, V ∈ nhds x₀ ∧ ∀ x ∈ V, x ∈ Ω → x ≠ x₀ →
        W x + Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧ K ⊆ Ω ∧ ∀ x ∈ Ω, x ∉ K → W x < ε) := by
  set s : ℝ := ρ / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hsρ : s < ρ := by rw [hsdef]; linarith
  have hscB : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s ⊆
      Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ :=
    fun x hx => ⟨hx.1, Metric.closedBall_subset_closedBall (le_of_lt hsρ) hx.2⟩
  set f : X → ℝ := Set.indicator (Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s)
    (fun _ => (1 : ℝ)) with hfdef
  have hf0 : ∀ z : X, 0 ≤ f z := by
    intro z
    rw [hfdef, Set.indicator_apply]
    by_cases hz : z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s <;> simp [hz]
  have hf1 : ∀ z : X, f z ≤ 1 := by
    intro z
    rw [hfdef, Set.indicator_apply]
    by_cases hz : z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s <;> simp [hz]
  have hfsph : ∀ z ∈ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, f z = 1 := by
    intro z hz
    rw [hfdef, Set.indicator_of_mem hz]
  have hfbd : ∀ z ∈ frontier Ω, f z = 0 := by
    intro z hz
    have hznot : z ∉ Submission.chartSphere (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s := by
      intro hzs
      have h1 : z ∈ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ :=
        hscB (Submission.chartSphere_subset_chartClosedBall _ _ _ hzs)
      have h2 : z ∈ Ω := hρΩ h1
      have h3 : z ∉ Ω := by
        have hh : interior Ω = Ω := hΩo.interior_eq
        exact fun hzΩ => hz.2 (hh.symm ▸ hzΩ)
      exact h3 h2
    rw [hfdef, Set.indicator_of_notMem hznot]
  obtain ⟨h1harm, h1nonneg, h1le, h1lb, h1lim, h1decay⟩ :=
    dirichletSphereEnvelope_facts (X := X) hΩo hΩc hΩne hcomp hx₀ hρ hρsub hρΩ hs hsρ
      (f := f) hf0 hf1 hfsph hfbd hbar
  obtain ⟨θ, hθ0, hθ1, hθ⟩ :=
    dirichletSphereEnvelope_outerGap_aux (X := X) hΩo hΩc hΩne hcomp hx₀ hρ hρsub hρΩ hs hsρ
      (f := f) hf0 hf1 hfsph hfbd hbar
  set L : ℝ := Real.log (ρ / s) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by rw [one_lt_div hs]; exact hsρ)
  set M : ℝ := (L + 1) / θ + 1 with hMdef
  have hMpos : 0 < M := by
    have h1 : 0 < L + 1 := by linarith
    have h2 : 0 < (L + 1) / θ := div_pos h1 hθ0
    rw [hMdef]; linarith
  have hMbig : L + 1 < θ * M := by
    have h1 : θ * ((L + 1) / θ) = L + 1 := by field_simp
    have h2 : θ * M = (L + 1) + θ := by rw [hMdef, mul_add, h1]; ring
    rw [h2]; linarith
  set A : ℝ := Real.log ρ + M with hAdef
  set B : ℝ := L + M + 1 with hBdef
  have hA : Real.log ρ ≤ A := by rw [hAdef]; linarith
  have hBpos : 0 < B := by rw [hBdef]; linarith [hLpos]
  have hB1 : Real.log (ρ / s) ≤ B := by rw [hBdef, ← hLdef]; linarith [hMpos]
  have hslog : Real.log s = Real.log ρ - L := by
    rw [hLdef, Real.log_div (ne_of_gt hρ) (ne_of_gt hs)]; ring
  have hB2 : A - Real.log s < B := by rw [hAdef, hslog, hBdef]; linarith
  have hB3 : B * (1 - θ) < A - Real.log ρ := by
    rw [hAdef, hBdef]
    have h3 : (L + M + 1) * (1 - θ) < M := by nlinarith [hMbig, hθ0, hLpos]
    linarith
  set hb : X → ℝ := Submission.piecewiseBarrier (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ s A B
    (Submission.limEnvelope (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1)
    with hbdef
  obtain ⟨hb_sub, hb_le_negchi, hb_ge, hb_inner⟩ :=
    Work.SimplyConnected.ABS.piecewiseBarrier_subharmonic (X := X) (Ω := Ω) (x₀ := x₀) hρ hs hsρ hρsub hρΩ
      (h₁ := Submission.limEnvelope
        (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1)
      hA hBpos hB1 hB2 h1harm h1nonneg h1le h1lb h1lim hθ0 hθ1 hθ hB3
  have hUo : IsOpen (Ω \ {x₀}) := hΩo.sdiff isClosed_singleton
  have hssub : Metric.closedBall ((chartAt ℂ x₀) x₀) s ⊆ (chartAt ℂ x₀).target :=
    (Metric.closedBall_subset_closedBall (le_of_lt hsρ)).trans hρsub
  have hzero : Submission.SuperharmonicOnX (fun _ : X => (0 : ℝ)) (Ω \ {x₀}) := by
    have hsub0 : Submission.SubharmonicOnX (fun _ : X => (0 : ℝ)) (univ : Set X) :=
      Submission.subharmonicOnX_const (0 : ℝ)
    have hcont : ContinuousOn (fun _ : X => (0 : ℝ)) (Ω \ {x₀}) := continuousOn_const
    have hmono : Submission.SubharmonicOnX (fun _ : X => (0 : ℝ)) (Ω \ {x₀}) :=
      hsub0.mono (subset_univ _) hcont
    simpa using hmono.neg
  have hne : (Submission.sweepFamily hb (Ω \ {x₀})).Nonempty := by
    refine ⟨fun _ => 0, hzero, ?_⟩
    intro y hy
    have h1 := hb_le_negchi y hy
    have h2 : 0 ≤ Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ y :=
      Submission.chartLogClamp_nonneg y
    linarith
  refine ⟨fun x => - Submission.sweep hb (Ω \ {x₀}) x, ?_, ?_, ?_, ?_⟩
  · have hEharm : Submission.HarmonicOnX (Submission.sweep hb (Ω \ {x₀})) (Ω \ {x₀}) :=
      Submission.sweep_harmonic hUo hb_sub hne
    have hEcont : ContinuousOn (Submission.sweep hb (Ω \ {x₀})) (Ω \ {x₀}) :=
      continuousOn_of_forall_continuousAt (fun x hx => (hEharm x hx).continuousAt)
    have hEsub : Submission.SubharmonicOnX (Submission.sweep hb (Ω \ {x₀})) (Ω \ {x₀}) :=
      hEharm.subharmonic hEcont
    simpa using hEsub.neg
  · intro x hx
    have hmem : (fun y => - Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ y)
        ∈ Submission.sweepFamily hb (Ω \ {x₀}) := by
      refine ⟨?_, ?_⟩
      · have hsubχ : Submission.SubharmonicOnX
            (Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ) (univ \ {x₀}) :=
          Submission.subharmonicOnX_chartLogClamp (z₀ := x₀) (ρ := ρ) hρ hρsub
        have hcontχ : ContinuousOn (Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ)
            (Ω \ {x₀}) := hsubχ.1.mono (fun y hy => ⟨mem_univ y, hy.2⟩)
        have hmono : Submission.SubharmonicOnX
            (Submission.chartLogClamp (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ) (Ω \ {x₀}) :=
          hsubχ.mono (fun y hy => ⟨mem_univ y, hy.2⟩) hcontχ
        simpa using hmono.neg
      · intro y hy
        have h1 := hb_le_negchi y hy
        linarith
    have hle := Submission.sweep_le_of_mem hmem hx
    linarith
  · refine ⟨A, Submission.chartBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s, ?_, ?_⟩
    · exact Submission.chartBall_mem_nhds hs (mem_chart_source ℂ x₀) rfl
    · intro x hxV hxΩ hxne
      have hxU : x ∈ Ω \ {x₀} := ⟨hxΩ, hxne⟩
      have hxcB : x ∈ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s :=
        Submission.chartBall_subset_chartClosedBall _ _ _ hxV
      have h1 : hb x = Real.log ‖(chartAt ℂ x₀) x - (chartAt ℂ x₀) x₀‖ - A := hb_inner x hxU hxcB
      have h2 : hb x ≤ Submission.sweep hb (Ω \ {x₀}) x := Submission.barrier_le_sweep hne hxU
      linarith
  · intro ε hε
    obtain ⟨N, hNopen, hNfront, hNdecay⟩ := h1decay (ε / B) (by positivity)
    have hclN : closure (Ω \ N) ⊆ Nᶜ :=
      closure_minimal (fun y hy => by simpa using hy.2) (isClosed_compl_iff.mpr hNopen)
    have hclΩ : closure (Ω \ N) ⊆ Ω := by
      intro x hx
      have hxcl : x ∈ closure Ω := closure_mono Set.diff_subset hx
      have hcl' : closure Ω = Ω ∪ frontier Ω := by
        rw [closure_eq_interior_union_frontier, hΩo.interior_eq]
      rw [hcl'] at hxcl
      rcases hxcl with hxΩ' | hxfr
      · exact hxΩ'
      · exact absurd (hclN hx) (by simpa using hNfront hxfr)
    refine ⟨closure (Ω \ N) ∪ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s,
      ?_, ?_, ?_⟩
    · refine IsCompact.union ?_ (Submission.isCompact_chartClosedBall hssub)
      exact IsCompact.of_isClosed_subset hcomp isClosed_closure (hclΩ.trans subset_closure)
    · intro x hx
      rcases hx with hx | hx
      · exact hclΩ hx
      · exact hρΩ (hscB hx)
    · intro x hxΩ hxK
      have hxnotC : x ∉ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s :=
        fun hc => hxK (Or.inr hc)
      have hxU : x ∈ Ω \ {x₀} := by
        refine ⟨hxΩ, fun hxx => hxnotC ?_⟩
        rw [hxx]
        refine ⟨mem_chart_source ℂ x₀, ?_⟩
        rw [Set.mem_preimage, Metric.mem_closedBall, dist_self]
        exact hs.le
      have hxU'' : x ∈ (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) :=
        ⟨hxΩ, hxnotC⟩
      have hxN : x ∈ N := by
        by_contra hxnot
        exact hxK (Or.inl (subset_closure ⟨hxΩ, hxnot⟩))
      have h1 : Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x < ε / B :=
        hNdecay x hxU'' hxN
      have h2 : hb x ≤ Submission.sweep hb (Ω \ {x₀}) x := Submission.barrier_le_sweep hne hxU
      have h3 : -B * Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x ≤ hb x :=
        hb_ge x hxU hxnotC
      have h4 : - Submission.sweep hb (Ω \ {x₀}) x ≤
          B * Submission.limEnvelope
            (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x := by
        linarith
      have h5 : B * Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x < B * (ε / B) :=
        mul_lt_mul_of_pos_left h1 hBpos
      have h6 : B * (ε / B) = ε := by field_simp
      linarith [h6 ▸ h5]


end Work.SimplyConnected.Perron
