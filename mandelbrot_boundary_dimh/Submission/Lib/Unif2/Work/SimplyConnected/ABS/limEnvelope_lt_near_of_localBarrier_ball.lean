import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.limEnvelope_lt_one_of_localBarrier_v2
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.coveringAux

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

/-- **Bouligand's regularity step on the punctured ball region.**

Let `Ω` be a relatively compact open region, `x₀ ∈ Ω`, and suppose a chart disc
`chartClosedBall c a ρ` around `x₀` is contained in `Ω`.  For `s < ρ` let
`U = Ω \ chartClosedBall c a s` be the region obtained by removing the (smaller) closed
chart disc.  If `f ≥ 0` vanishes on `frontier Ω` and every frontier point `p` of `Ω`
carries a local barrier, then the limsup Perron envelope of `U` with data `f` and bound `1`
is `< ε` on a neighbourhood of `p` intersected with `U`.

This is the "ball" form of `Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier`:
the extra separation hypothesis `∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V` of that
lemma is automatic here, because the only frontier points of `U` that are not frontier
points of `Ω` lie on the compact inner chart sphere `chartClosedBall c a s`, which is
disjoint from `frontier Ω`; the barrier neighbourhood `V` may therefore be shrunk (using
`exists_chartClosedBall_subset_compl_v2`) to miss it. -/
theorem limEnvelope_lt_near_of_localBarrier_ball {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hsρ : s < ρ)
    (hρsub : Metric.closedBall ((chartAt ℂ x₀) x₀) ρ ⊆ (chartAt ℂ x₀).target)
    (hρΩ : Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ ⊆ Ω)
    {p : X} (hp : p ∈ frontier Ω)
    {f : X → ℝ} (hf0 : ∀ z : X, 0 ≤ f z)
    (hfbd : ∀ z ∈ frontier Ω, f z = 0)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s,
        x ∈ N → Submission.limEnvelope
          (Ω \ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s) f 1 x < ε := by
  classical
  intro ε hε
  set D : Set X := Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) s with hD
  set U : Set X := Ω \ D with hU
  have hsρle : s ≤ ρ := hsρ.le
  have hsubs : Metric.closedBall ((chartAt ℂ x₀) x₀) s ⊆ (chartAt ℂ x₀).target :=
    (Metric.closedBall_subset_closedBall hsρle).trans hρsub
  have hDc : IsClosed D := by
    rw [hD]
    exact Submission.isClosed_chartClosedBall hsubs
  have hDs : D ⊆ Submission.chartClosedBall (chartAt ℂ x₀) ((chartAt ℂ x₀) x₀) ρ := by
    rw [hD]
    exact fun y hy => ⟨hy.1, Metric.closedBall_subset_closedBall hsρle hy.2⟩
  have hDΩ : D ⊆ Ω := hDs.trans hρΩ
  have hUo : IsOpen U := by rw [hU]; exact hΩo.sdiff hDc
  have hUΩ : U ⊆ Ω := by rw [hU]; exact Set.sdiff_subset
  have hcompU : IsCompact (closure U) := by
    rw [hU]
    exact hcomp.of_isClosed_subset isClosed_closure (closure_mono Set.sdiff_subset)
  -- the Perron family is non-empty
  have hneF : (Submission.limFamily U f 1).Nonempty :=
    ⟨fun _ => (0 : ℝ),
      (Submission.subharmonicOnX_const 0).mono (Set.subset_univ U) continuousOn_const,
      (fun _ => zero_le_one),
      (fun ζ _ ε hε => by
        filter_upwards with z
        linarith [hf0 ζ, hε.le])⟩
  -- `p` is outside `Ω`
  have hpΩ : p ∉ Ω := by
    intro h
    exact hp.2 (by rwa [← hΩo.interior_eq] at h)
  have hpD : p ∉ D := fun h => hpΩ (hDΩ h)
  have hpclU : p ∈ closure U := by
    rw [hU, mem_closure_iff_nhds]
    intro t ht
    have hDsn : Dᶜ ∈ 𝓝 p := hDc.isOpen_compl.mem_nhds hpD
    obtain ⟨z, ⟨hzt, hzD⟩, hzΩ⟩ :=
      mem_closure_iff_nhds.mp hp.1 (t ∩ Dᶜ) (Filter.inter_mem ht hDsn)
    exact ⟨z, hzt, hzΩ, hzD⟩
  have hfrU : (frontier U).Nonempty :=
    ⟨p, hpclU, by rw [hUo.interior_eq]; exact fun h => hpΩ h.1⟩
  -- the frontier of `U` is contained in `frontier Ω ∪ D`
  have hfrontU : frontier U ⊆ frontier Ω ∪ D := by
    intro y hy
    rw [frontier, Set.mem_sdiff, hUo.interior_eq] at hy
    by_cases hyΩ : y ∈ frontier Ω
    · exact Or.inl hyΩ
    · refine Or.inr ?_
      have hyclΩ : y ∈ closure Ω := closure_mono hUΩ hy.1
      have hdecomp : closure Ω = Ω ∪ frontier Ω := by
        rw [closure_eq_interior_union_frontier, hΩo.interior_eq]
      rw [hdecomp] at hyclΩ
      rcases hyclΩ with h | h
      · by_contra hyD
        exact hy.2 ⟨h, hyD⟩
      · exact absurd h hyΩ
  -- the barrier at `p`, shrunk so that its closure misses the inner chart disc `D`
  obtain ⟨u, V, hVo, hpV, huSC, hupos, hucont, hup0⟩ := hb
  obtain ⟨r, hr, hBsub, hBtarget⟩ := exists_chartClosedBall_subset_compl_v2 hDc hpD
  set V' : Set X := V ∩ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) r with hV'def
  have hV'o : IsOpen V' := hVo.inter (Submission.chartBall_isOpen _ _ _)
  have hpV' : p ∈ V' := by
    refine ⟨hpV, ?_⟩
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ p, Metric.mem_ball_self hr⟩
  have hV'subV : V' ⊆ V := Set.inter_subset_left
  have hclV'D : ∀ ζ : X, ζ ∈ closure V' → ζ ∉ D := by
    intro ζ hζ hζD
    have h3 : ζ ∈ closure (Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) r) :=
      closure_mono Set.inter_subset_right hζ
    rw [Submission.closure_chartBall_eq_chartClosedBall hr hBtarget] at h3
    exact hBsub h3 hζD
  -- the barrier condition required by `limEnvelope_lt_near_of_localBarrier`
  have hb' : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 ∧
      (∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V) :=
    ⟨u, V', hV'o, hpV',
      Submission.SuperharmonicOnX.mono huSC (fun x hx => ⟨hx.1, hV'subV hx.2⟩)
        (hucont.mono (fun x hx => hV'subV hx.2)),
      (fun x hx => hupos x ⟨hx.1, hV'subV hx.2⟩),
      hucont.mono hV'subV, hup0,
      (fun ζ hζU hζfr hζcl => hclV'D ζ hζcl ((hfrontU hζU).resolve_left hζfr))⟩
  -- Bouligand's regularity step on `U`
  obtain ⟨N, hNo, hpN, hsmall⟩ :=
    limEnvelope_lt_near_of_localBarrier (X := X) hΩo hUo hUΩ hcompU hfrU
      (M := 1) (ε := ε) (by norm_num : (0 : ℝ) ≤ 1) hε hneF
      (fun ζ hζ => (hfbd ζ hζ).le) hp hpclU hb'
  refine ⟨N, hNo, hpN, ?_⟩
  intro x hxU hxN
  exact hsmall x hxU hxN

end Work.SimplyConnected.ABS
