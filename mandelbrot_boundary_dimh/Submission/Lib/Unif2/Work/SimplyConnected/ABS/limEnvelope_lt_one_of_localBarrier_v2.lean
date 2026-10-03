import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier

open Filter Set
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SimplyConnected.ABS

/-- A closed chart disc around a point outside a closed set, contained in the complement of that
set.  (Local replacement for the same lemma inside the deleted module
`limEnvelope_lt_one_of_localBarrier`.) -/
theorem exists_chartClosedBall_subset_compl_v2 {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {D : Set X} (hDc : IsClosed D) {p : X} (hp : p ∉ D) :
    ∃ r : ℝ, 0 < r ∧ Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) r ⊆ Dᶜ ∧
      Metric.closedBall ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target := by
  have hmem : Dᶜ ∩ (chartAt ℂ p).source ∈ 𝓝 p :=
    Filter.inter_mem (hDc.isOpen_compl.mem_nhds hp)
      ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ p).image_mem_nhds (mem_chart_source ℂ p) hmem)
  refine ⟨r₀ / 2, half_pos hr₀, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxsrc, hxc⟩ := hx
    have hsub : Metric.closedBall ((chartAt ℂ p) p) (r₀/2) ⊆
        (chartAt ℂ p) '' (Dᶜ ∩ (chartAt ℂ p).source) :=
      (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hr₀sub
    obtain ⟨y, hy, hyc⟩ := hsub hxc
    have hyx : y = x := by
      calc y = (chartAt ℂ p).symm ((chartAt ℂ p) y) := ((chartAt ℂ p).left_inv hy.2).symm
        _ = (chartAt ℂ p).symm ((chartAt ℂ p) x) := by rw [hyc]
        _ = x := (chartAt ℂ p).left_inv hxsrc
    simpa [hyx] using hy.1
  · refine (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans ?_
    refine hr₀sub.trans ?_
    rintro z ⟨y, hy, rfl⟩
    exact (chartAt ℂ p).map_source hy.2

/-- **The Perron barrier step.**  If `Ω` is Dirichlet regular at every frontier point (`hbar`),
then the limsup Perron envelope of `U = Ω \ chartClosedBall c a s` with data `0` on `frontier Ω`
and global bound `1` is `< 1` somewhere on `U`.

Proof.  Pick `p ∈ frontier Ω` and its local barrier `(u, V)`.  Shrinking `V` to a chart ball around
`p` that misses the inner chart sphere `chartClosedBall c a s` (which is legitimate, since
`p ∉ chartClosedBall c a s`), the barrier satisfies the extra separation hypothesis
`∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V` of the classical Bouligand regularity step
`Work.SimplyConnected.ABS.limEnvelope_lt_near_of_localBarrier`, which gives a neighbourhood `N`
of `p` with `limEnvelope U f 1 < 1` on `U ∩ N`.  Since `p ∈ closure U`, that intersection is
non-empty, and any of its points is a point of `U` witnessing the claim. -/
theorem limEnvelope_lt_one_of_localBarrier_v2 {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hcomp : IsCompact (closure Ω)) {x₀ : X} (hx₀ : x₀ ∈ Ω)
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
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  set D : Set X := Submission.chartClosedBall c a s with hD
  set U : Set X := Ω \ D with hU
  have hsubs : Metric.closedBall a s ⊆ c.target := by
    rw [hc, ha]
    exact (Metric.closedBall_subset_closedBall hsρ.le).trans hρsub
  have hρΩ' : Submission.chartClosedBall c a ρ ⊆ Ω := by
    rw [hc, ha] at hρΩ
    exact hρΩ
  have hsubsρ : Metric.closedBall a s ⊆ Metric.closedBall a ρ :=
    Metric.closedBall_subset_closedBall hsρ.le
  have hDc : IsClosed D := by rw [hD]; exact Submission.isClosed_chartClosedBall hsubs
  have hDΩ : D ⊆ Ω := by
    rw [hD]
    rintro y ⟨hy, hyb⟩
    exact hρΩ' ⟨hy, hsubsρ hyb⟩
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
  -- a frontier point of `Ω`
  obtain ⟨p, hpfr⟩ := hfr
  have hpΩ : p ∉ Ω := by
    intro h
    exact hpfr.2 (by rwa [← hΩo.interior_eq] at h)
  have hpD : p ∉ D := fun h => hpΩ (hDΩ h)
  have hpclU : p ∈ closure U := by
    rw [hU, mem_closure_iff_nhds]
    intro t ht
    have hDs : Dᶜ ∈ 𝓝 p := hDc.isOpen_compl.mem_nhds hpD
    obtain ⟨z, ⟨hzt, hzD⟩, hzΩ⟩ :=
      mem_closure_iff_nhds.mp hpfr.1 (t ∩ Dᶜ) (Filter.inter_mem ht hDs)
    exact ⟨z, hzt, hzΩ, hzD⟩
  have hfrU : (frontier U).Nonempty :=
    ⟨p, hpclU, by rw [hUo.interior_eq]; exact fun h => hpΩ h.1⟩
  -- the barrier at `p`, shrunk so that its closure misses the inner chart sphere
  obtain ⟨u, V, hVo, hpV, huSC, hupos, hucont, hup0⟩ := hbar p hpfr
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
  -- the barrier condition required by `limEnvelope_lt_near_of_localBarrier`
  have hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0 ∧
      (∀ ζ ∈ frontier U, ζ ∉ frontier Ω → ζ ∉ closure V) :=
    ⟨u, V', hV'o, hpV',
      Submission.SuperharmonicOnX.mono huSC (fun x hx => ⟨hx.1, hV'subV hx.2⟩)
        (hucont.mono (fun x hx => hV'subV hx.2)),
      (fun x hx => hupos x ⟨hx.1, hV'subV hx.2⟩),
      hucont.mono hV'subV, hup0,
      (fun ζ hζ hζfr hζcl => hclV'D ζ hζcl ((hfrontU hζ).resolve_left hζfr))⟩
  -- Bouligand's regularity step
  obtain ⟨N, hNo, hpN, hsmall⟩ :=
    limEnvelope_lt_near_of_localBarrier hΩo hUo hUΩ hcompU hfrU (M := 1) (ε := 1)
      (by norm_num) one_pos hneF (fun ζ hζ => le_of_eq (hfbd ζ hζ)) hpfr hpclU hb
  obtain ⟨z, hzN, hzU⟩ := mem_closure_iff_nhds.mp hpclU N (hNo.mem_nhds hpN)
  refine ⟨z, ?_, hsmall z hzU hzN⟩
  rw [hU] at hzU
  simpa only [hD, hc, ha] using hzU

end Work.SimplyConnected.ABS
