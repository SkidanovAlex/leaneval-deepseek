import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Submission.Lib.Unif2.Commons.Geometry.Manifold.analyticAt_pullback_iff_chart
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Lib.Unif2.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace Commons.Analysis.Complex

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

private def IsLocalHomeoAt {X : Type*} [TopologicalSpace X] (Φ : X → ℂ) (x : X) : Prop :=
  ∃ e : OpenPartialHomeomorph X ℂ, x ∈ e.source ∧ Set.EqOn Φ e e.source

private def LocallyConstantAt {X : Type*} [TopologicalSpace X] (Φ : X → ℂ) (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, Φ y = Φ x

section Basic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ}

private lemma isOpen_isLocalHomeoAt : IsOpen {x : X | IsLocalHomeoAt Φ x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨e, hx, heq⟩
  exact mem_of_superset (e.open_source.mem_nhds hx) (fun y hy => ⟨e, hy, heq⟩)

private lemma isLocalHomeoAt_of_deriv_ne_zero {c y : X} (hy : y ∈ (chartAt ℂ c).source)
    (han : AnalyticAt ℂ (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) y))
    (hd : deriv (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) y) ≠ 0) : IsLocalHomeoAt Φ y := by
  set ψ : ℂ → ℂ := Φ ∘ (chartAt ℂ c).symm with hψ
  set z : ℂ := (chartAt ℂ c) y with hz
  have han' : AnalyticAt ℂ ψ z := han
  have hd' : deriv ψ z ≠ 0 := hd
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 _ hd')
  have hfd : HasStrictFDerivAt ψ i.toContinuousLinearMap z := han'.hasStrictDerivAt
  let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph ψ
  have hz₂ : z ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
  have he₂ : (e₂ : ℂ → ℂ) = ψ := rfl
  refine ⟨(chartAt ℂ c).trans e₂, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hy, by simpa only [Set.mem_preimage, hz] using hz₂⟩
  · intro u hu
    rw [OpenPartialHomeomorph.trans_apply, he₂]
    simp only [hψ, Function.comp_apply]
    rw [(chartAt ℂ c).left_inv hu.1]

private lemma deriv_eq_zero_of_not_isLocalHomeoAt {y : X}
    (hhol : AnalyticAt ℂ (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y))
    (h : ¬ IsLocalHomeoAt Φ y) : deriv (Φ ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = 0 := by
  by_contra hne
  exact h (isLocalHomeoAt_of_deriv_ne_zero (mem_chart_source ℂ y) hhol hne)

private lemma isOpen_locallyConstantAt : IsOpen {x : X | LocallyConstantAt Φ x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hxU, hUc⟩
  exact mem_of_superset (hU.mem_nhds hxU)
    (fun y hy => ⟨U, hU, hy, fun y' hy' => (hUc y' hy').trans (hUc y hy).symm⟩)

private lemma deriv_chart_eq_zero_of_locallyConstantAt {c x : X} (hx : x ∈ (chartAt ℂ c).source)
    (h : LocallyConstantAt Φ x) :
    deriv (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) x) = 0 := by
  obtain ⟨U, hU, hxU, hUc⟩ := h
  set e := chartAt ℂ c with he
  have hVopen : IsOpen (e '' (U ∩ e.source)) := e.isOpen_image_of_subset_source
    (hU.inter e.open_source) inter_subset_right
  have hmem : e x ∈ e '' (U ∩ e.source) := ⟨x, ⟨hxU, hx⟩, rfl⟩
  have heq : ∀ z ∈ e '' (U ∩ e.source), (Φ ∘ e.symm) z = Φ x := by
    rintro z ⟨y, ⟨hyU, hysrc⟩, rfl⟩
    simp only [Function.comp_apply]
    rw [e.left_inv hysrc]
    exact hUc y hyU
  have hev : (Φ ∘ e.symm) =ᶠ[𝓝 (e x)] (fun _ => Φ x) :=
    Filter.eventually_of_mem (hVopen.mem_nhds hmem) heq
  have := (hasDerivAt_const (e x) (Φ x)).congr_of_eventuallyEq hev
  simpa using this.deriv

private lemma isClosed_locallyConstantAt
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    IsClosed {x : X | LocallyConstantAt Φ x} := by
  rw [isClosed_iff_clusterPt]
  intro y hy
  rw [clusterPt_principal_iff] at hy
  classical
  by_cases hyA : LocallyConstantAt Φ y
  · exact hyA
  have hfreqA : ∃ᶠ x in 𝓝 y, x ∈ {x : X | LocallyConstantAt Φ x} := by
    rw [frequently_iff]
    intro U hU
    obtain ⟨x, hxU, hxA⟩ := hy U hU
    exact ⟨x, hxU, hxA⟩
  have hfreqA' : ∃ᶠ x in 𝓝[{y}ᶜ] y, x ∈ {x : X | LocallyConstantAt Φ x} := by
    rw [frequently_nhdsWithin_iff]
    refine hfreqA.mono (fun x hx => ⟨hx, ?_⟩)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxy
    exact hyA (hxy ▸ hx)
  have hsrc : (chartAt ℂ y).source ∈ 𝓝 y :=
    (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
  have hfreq2 : ∃ᶠ x in 𝓝[{y}ᶜ] y,
      x ∈ {x : X | LocallyConstantAt Φ x} ∧ x ∈ (chartAt ℂ y).source :=
    hfreqA'.and_eventually (Eventually.filter_mono nhdsWithin_le_nhds hsrc)
  set c : ℂ := (chartAt ℂ y) y with hc
  have hTendsto : Tendsto (chartAt ℂ y) (𝓝[{y}ᶜ] y) (𝓝[{c}ᶜ] c) := by
    show Filter.map (chartAt ℂ y) (𝓝[{y}ᶜ] y) ≤ 𝓝[{c}ᶜ] c
    rw [(chartAt ℂ y).map_nhdsWithin_eq (mem_chart_source ℂ y) {y}ᶜ]
    apply nhdsWithin_mono
    rintro z ⟨x, ⟨hxs, hxy⟩, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hxy ⊢
    intro hcon
    exact hxy ((chartAt ℂ y).injOn hxs (mem_chart_source ℂ y) (by rw [← hc]; exact hcon))
  have hfreqzero : ∃ᶠ z in 𝓝[{c}ᶜ] c, deriv (Φ ∘ (chartAt ℂ y).symm) z = 0 :=
    hTendsto.frequently_map (chartAt ℂ y)
      (fun x hx => deriv_chart_eq_zero_of_locallyConstantAt hx.2 hx.1) hfreq2
  have han : AnalyticAt ℂ (Φ ∘ (chartAt ℂ y).symm) c := hhol y
  have hevzero : ∀ᶠ z in 𝓝 c, deriv (Φ ∘ (chartAt ℂ y).symm) z = 0 :=
    (AnalyticAt.frequently_zero_iff_eventually_zero han.deriv).mp (by simpa [hc] using hfreqzero)
  have hevan : ∀ᶠ z in 𝓝 c, AnalyticAt ℂ (Φ ∘ (chartAt ℂ y).symm) z :=
    (isOpen_analyticAt ℂ _).mem_nhds han
  have htarget : ∀ᶠ z in 𝓝 c, z ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).open_target.mem_nhds ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
  have hall : ∀ᶠ z in 𝓝 c, deriv (Φ ∘ (chartAt ℂ y).symm) z = 0 ∧
      AnalyticAt ℂ (Φ ∘ (chartAt ℂ y).symm) z ∧ z ∈ (chartAt ℂ y).target := by
    filter_upwards [hevzero, hevan, htarget] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hconst : ∀ z ∈ Metric.ball c r, (Φ ∘ (chartAt ℂ y).symm) z = (Φ ∘ (chartAt ℂ y).symm) c :=
    fun z hz => IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball
      (convex_ball c r).isPreconnected
      (fun w hw => ((hball (Metric.mem_ball.mp hw)).2.1).differentiableAt.differentiableWithinAt)
      (fun w hw => (hball (Metric.mem_ball.mp hw)).1) hz (Metric.mem_ball_self hr)
  refine ⟨(chartAt ℂ y).symm '' Metric.ball c r, ?_, ?_, ?_⟩
  · exact ((chartAt ℂ y).symm).isOpen_image_of_subset_source Metric.isOpen_ball
      (fun z hz => (hball hz).2.2)
  · exact ⟨c, Metric.mem_ball_self hr, by
      rw [show c = (chartAt ℂ y) y from rfl, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]⟩
  · rintro x ⟨z, hz, rfl⟩
    have hcy : (chartAt ℂ y).symm c = y := by
      rw [show c = (chartAt ℂ y) y from rfl, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
    have h1 : Φ ((chartAt ℂ y).symm z) = Φ ((chartAt ℂ y).symm c) := hconst z hz
    rw [h1, hcy]

end Basic

section NotLocallyConstant

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [ConnectedSpace X] {Φ : X → ℂ}

private lemma not_locallyConstantAt_of_deriv_ne_zero
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) {z : X}
    (hz : deriv (Φ ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0) :
    ∀ y, ¬ LocallyConstantAt Φ y := by
  intro y hy
  have hclop : IsClopen {x : X | LocallyConstantAt Φ x} :=
    ⟨isClosed_locallyConstantAt (Φ := Φ) hhol, isOpen_locallyConstantAt⟩
  have huniv : {x : X | LocallyConstantAt Φ x} = univ :=
    IsClopen.eq_univ hclop ⟨y, hy⟩
  have hzA : LocallyConstantAt Φ z := by
    have : z ∈ ({x : X | LocallyConstantAt Φ x} : Set X) := by rw [huniv]; trivial
    exact this
  exact hz (deriv_chart_eq_zero_of_locallyConstantAt (mem_chart_source ℂ z) hzA)

end NotLocallyConstant

section Isolation

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ}

/-- At a non-local-homeomorphism point `c` of `Φ`, the other such points are isolated away from `c`. -/
private lemma exists_isLocalHomeoAt_nhds_of_not
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) {c : X} (hc : ¬ IsLocalHomeoAt Φ c) :
    ∃ N : Set X, IsOpen N ∧ c ∈ N ∧ ∀ y ∈ N, y ≠ c → IsLocalHomeoAt Φ y := by
  set ψ : ℂ → ℂ := Φ ∘ (chartAt ℂ c).symm with hψ
  set cc : ℂ := (chartAt ℂ c) c with hcc
  have han : AnalyticAt ℂ ψ cc := hhol c
  -- ψ is not eventually constant, hence ψ' is not eventually zero
  have hne0 : ¬ (∀ᶠ z in 𝓝 cc, deriv ψ z = 0) := by
    intro hz0
    have hevan : ∀ᶠ z in 𝓝 cc, AnalyticAt ℂ ψ z := (isOpen_analyticAt ℂ ψ).mem_nhds han
    have htgt : ∀ᶠ z in 𝓝 cc, z ∈ (chartAt ℂ c).target :=
      (chartAt ℂ c).open_target.mem_nhds ((chartAt ℂ c).map_source (mem_chart_source ℂ c))
    have hall : ∀ᶠ z in 𝓝 cc, deriv ψ z = 0 ∧ AnalyticAt ℂ ψ z ∧ z ∈ (chartAt ℂ c).target := by
      filter_upwards [hz0, hevan, htgt] with z h1 h2 h3; exact ⟨h1, h2, h3⟩
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
    have hconst : ∀ z ∈ Metric.ball cc r, ψ z = ψ cc := fun z hz =>
      IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball cc r).isPreconnected
        (fun w hw => ((hball (Metric.mem_ball.mp hw)).2.1).differentiableAt.differentiableWithinAt)
        (fun w hw => (hball (Metric.mem_ball.mp hw)).1) hz (Metric.mem_ball_self hr)
    refine hnlc c ⟨(chartAt ℂ c).symm '' Metric.ball cc r, ?_, ?_, ?_⟩
    · exact ((chartAt ℂ c).symm).isOpen_image_of_subset_source Metric.isOpen_ball
        (fun z hz => (hball hz).2.2)
    · exact ⟨cc, Metric.mem_ball_self hr, by
        rw [show cc = (chartAt ℂ c) c from rfl, (chartAt ℂ c).left_inv (mem_chart_source ℂ c)]⟩
    · rintro x ⟨z, hz, rfl⟩
      have hcy : (chartAt ℂ c).symm cc = c := by
        rw [show cc = (chartAt ℂ c) c from rfl, (chartAt ℂ c).left_inv (mem_chart_source ℂ c)]
      have h1 : Φ ((chartAt ℂ c).symm z) = Φ ((chartAt ℂ c).symm cc) := hconst z hz
      rw [h1, hcy]
  have hnonzero : ∀ᶠ z in 𝓝[≠] cc, deriv ψ z ≠ 0 :=
    (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero han.deriv).resolve_left hne0
  have hnonzero' : ∀ᶠ z in 𝓝 cc, z ≠ cc → deriv ψ z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hnonzero
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hnonzero'
  have htgt : ∀ᶠ z in 𝓝 cc, z ∈ (chartAt ℂ c).target :=
    (chartAt ℂ c).open_target.mem_nhds ((chartAt ℂ c).map_source (mem_chart_source ℂ c))
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp htgt
  refine ⟨(chartAt ℂ c).source ∩ (chartAt ℂ c) ⁻¹' Metric.ball cc (min δ₁ δ₂), ?_, ?_, ?_⟩
  · exact (chartAt ℂ c).isOpen_inter_preimage Metric.isOpen_ball
  · refine ⟨mem_chart_source ℂ c, ?_⟩
    rw [show cc = (chartAt ℂ c) c from rfl]
    exact Metric.mem_ball_self (lt_min hδ₁pos hδ₂pos)
  · rintro y ⟨hysrc, hyball⟩ hyne
    simp only [Set.mem_preimage] at hyball
    have hyne' : (chartAt ℂ c) y ≠ cc := by
      intro hcon
      rw [hcc] at hcon
      exact hyne ((chartAt ℂ c).injOn hysrc (mem_chart_source ℂ c) hcon)
    have hderiv : deriv ψ ((chartAt ℂ c) y) ≠ 0 :=
      hδ₁ (lt_of_lt_of_le (Metric.mem_ball.mp hyball) (min_le_left δ₁ δ₂)) hyne'
    have hzan : AnalyticAt ℂ ψ ((chartAt ℂ c) y) :=
      (Commons.Geometry.Manifold.analyticAt_pullback_iff_chart
        (x := y) (y := c) hysrc).mp (hhol y)
    exact isLocalHomeoAt_of_deriv_ne_zero hysrc hzan hderiv

end Isolation


section Global

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
  {Φ : X → ℂ}

/-- The set of points where `Φ` is not a local homeomorphism. -/
private def Crit (Φ : X → ℂ) : Set X := {x | ¬ IsLocalHomeoAt Φ x}

/-- The set of critical values of `Φ`. -/
private def critVal (Φ : X → ℂ) : Set ℂ := Φ '' Crit Φ

private lemma isClosed_crit : IsClosed (Crit Φ) :=
  (isOpen_isLocalHomeoAt (Φ := Φ)).isClosed_compl

private lemma rank_gt_one_complex : 1 < Module.rank ℝ ℂ := by
  have h : Module.rank ℝ ℂ = 2 := by
    rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
    simp
  rw [h]; norm_num

/-- The fibre of `Φ` over any value is discrete. -/
private lemma isDiscrete_fiber
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) (w : ℂ) : IsDiscrete (Φ ⁻¹' {w}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  set ψ : ℂ → ℂ := Φ ∘ (chartAt ℂ x).symm with hψ
  set cc : ℂ := (chartAt ℂ x) x with hcc
  have hxw : Φ x = w := Set.mem_singleton_iff.mp hx
  have han : AnalyticAt ℂ (fun z => ψ z - w) cc := (hhol x).sub analyticAt_const
  have hnotconst : ¬ (∀ᶠ z in 𝓝 cc, (fun z => ψ z - w) z = 0) := by
    intro h
    refine hnlc x ?_
    have hzev : ∀ᶠ z in 𝓝 cc, ψ z = w := by
      filter_upwards [h] with z hz
      simpa using sub_eq_zero.mp hz
    have hcont := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    have hzev' : ∀ᶠ y in 𝓝 x, ψ ((chartAt ℂ x) y) = w := hcont.eventually hzev
    have hsrc : ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
    have hev : ∀ᶠ y in 𝓝 x, Φ y = Φ x := by
      filter_upwards [hzev', hsrc] with y hy hys
      rw [show ψ ((chartAt ℂ x) y) = Φ y from by
        simp only [hψ, Function.comp_apply]; rw [(chartAt ℂ x).left_inv hys]] at hy
      exact hy.trans hxw.symm
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hev
    exact ⟨U, hUopen, hxU, fun y hy => hUsub hy⟩
  have hne : ∀ᶠ z in 𝓝[≠] cc, (fun z => ψ z - w) z ≠ 0 :=
    (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero han).resolve_left hnotconst
  have hne' : ∀ᶠ z in 𝓝 cc, z ≠ cc → (fun z => ψ z - w) z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hne
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hne'
  refine ⟨(chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball cc δ,
    (chartAt ℂ x).isOpen_inter_preimage Metric.isOpen_ball, ?_⟩
  ext y; constructor
  · rintro ⟨hy, hyf⟩
    simp only [Set.mem_singleton_iff]
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hy
    have hyeq : Φ y = w := Set.mem_singleton_iff.mp hyf
    have : ψ ((chartAt ℂ x) y) = w := by
      simp only [hψ, Function.comp_apply]
      rw [(chartAt ℂ x).left_inv hy.1]
      exact hyeq
    have hdist : dist ((chartAt ℂ x) y) cc < δ := Metric.mem_ball.mp hy.2
    have hcy : (chartAt ℂ x) y = cc := by
      by_contra hne''
      exact (hδ hdist hne'') (by simp [this])
    exact (chartAt ℂ x).injOn hy.1 (mem_chart_source ℂ x) (by rw [hcy, hcc])
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨⟨mem_chart_source ℂ x, Metric.mem_ball_self hδpos⟩, hx⟩

/-- Every fibre of `Φ` is finite. -/
private lemma finite_fiber
    (hprop : IsProperMap Φ)
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) (w : ℂ) : (Φ ⁻¹' {w}).Finite :=
  (hprop.isCompact_preimage isCompact_singleton).finite (isDiscrete_fiber hhol hnlc w)

end Global


section Covering

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
  {Φ : X → ℂ}

private lemma crit_isDiscrete
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) : IsDiscrete (Crit Φ) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨N, hNo, hxN, hN⟩ := exists_isLocalHomeoAt_nhds_of_not hhol hnlc hx
  refine ⟨N, hNo, ?_⟩
  ext y; constructor
  · rintro ⟨hyN, hyCrit⟩
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hyCrit (hN y hyN hne)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨hxN, hx⟩

private lemma crit_countable
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) : (Crit Φ).Countable :=
  IsLindelof.countable_of_isDiscrete
    (IsLindelof.of_isClosed_subset isLindelof_univ (isClosed_crit (Φ := Φ)) (subset_univ _))
    (crit_isDiscrete hhol hnlc)

private lemma critVal_countable
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) : (critVal Φ).Countable :=
  (crit_countable hhol hnlc).image Φ

private lemma critVal_compl_preconnected
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) : IsPreconnected (critVal Φ)ᶜ :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ) rank_gt_one_complex
    (critVal_countable hhol hnlc)).isPreconnected

private lemma finite_fiber_off_critVal (hprop : IsProperMap Φ) {w : ℂ} (hw : w ∉ critVal Φ) :
    (Φ ⁻¹' {w}).Finite := by
  refine (hprop.isCompact_preimage isCompact_singleton).finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hxc : IsLocalHomeoAt Φ x := by
    by_contra hcon
    exact hw ⟨x, hcon, Set.mem_singleton_iff.mp hx⟩
  obtain ⟨e, hxe, heq⟩ := hxc
  refine ⟨e.source, e.open_source, ?_⟩
  ext y; constructor
  · rintro ⟨hye, hyf⟩
    simp only [Set.mem_singleton_iff]
    apply e.injOn hye hxe
    rw [← heq hye, ← heq hxe, Set.mem_singleton_iff.mp hyf, Set.mem_singleton_iff.mp hx]
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨hxe, hx⟩

private lemma isLocalHomeomorphOn_off_critVal : IsLocalHomeomorphOn Φ (Φ ⁻¹' (critVal Φ)ᶜ) :=
  IsLocalHomeomorphOn.mk Φ _ (fun x hx => by
    have hxc : IsLocalHomeoAt Φ x := by
      by_contra hcon
      exact hx ⟨x, hcon, rfl⟩
    exact hxc)

private lemma isCoveringMapOn_off_critVal (hprop : IsProperMap Φ) :
    IsCoveringMapOn Φ (critVal Φ)ᶜ :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hprop.isClosedMap
    (fun w hw => finite_fiber_off_critVal hprop hw) isLocalHomeomorphOn_off_critVal

private lemma natCard_fiber_eq_one_off_critVal (hprop : IsProperMap Φ)
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) (h0 : (0 : ℂ) ∉ critVal Φ)
    (hcard0 : Nat.card (Φ ⁻¹' {(0 : ℂ)}) = 1) {w : ℂ} (hw : w ∉ critVal Φ) :
    Nat.card (Φ ⁻¹' {w}) = 1 := by
  have h := Commons.Topology.Covering.natCard_fiber_eq_of_preconnected
    (isCoveringMapOn_off_critVal hprop) (critVal_compl_preconnected hhol hnlc) h0 hw
  rw [hcard0] at h
  exact h.symm

/-- The set of critical values is isolated: every critical value is an isolated point of `critVal`. -/
private lemma critVal_isolated (hprop : IsProperMap Φ)
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) {w : ℂ} (hw : w ∈ critVal Φ) :
    ∃ N ∈ 𝓝 w, ∀ w' ∈ N, w' ∈ critVal Φ → w' = w := by
  classical
  have hN : ∀ p : Φ ⁻¹' {w}, ∃ N : Set X, IsOpen N ∧ (p : X) ∈ N ∧ N ∩ Crit Φ ⊆ {(p : X)} := by
    intro p
    by_cases hp : (p : X) ∈ Crit Φ
    · obtain ⟨N, hNo, hpN, hNi⟩ := exists_isLocalHomeoAt_nhds_of_not hhol hnlc hp
      exact ⟨N, hNo, hpN, fun y hy => by
        simp only [Set.mem_singleton_iff]
        by_contra hne
        exact hy.2 (hNi y hy.1 hne)⟩
    · refine ⟨{x : X | IsLocalHomeoAt Φ x}, isOpen_isLocalHomeoAt, ?_, ?_⟩
      · by_contra h; exact hp h
      · intro y hy
        exact absurd hy.1 (show ¬ IsLocalHomeoAt Φ y from hy.2)
  let N : Φ ⁻¹' {w} → Set X := fun p => (hN p).choose
  have hNspec : ∀ p, IsOpen (N p) ∧ (p : X) ∈ N p ∧ N p ∩ Crit Φ ⊆ {(p : X)} :=
    fun p => (hN p).choose_spec
  let U : Set X := ⋃ p : Φ ⁻¹' {w}, N p
  have hUopen : IsOpen U := isOpen_iUnion fun p => (hNspec p).1
  have hfibsub : Φ ⁻¹' {w} ⊆ U :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hNspec ⟨x, hx⟩).2.1⟩
  have hclosed : IsClosed (Φ '' Uᶜ) := hprop.isClosedMap Uᶜ hUopen.isClosed_compl
  have hwnot : w ∉ Φ '' Uᶜ := by
    rintro ⟨x, hxU, hxw⟩
    exact hxU (hfibsub (by simp [hxw]))
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hwnot)
  refine ⟨Metric.ball w ε, Metric.ball_mem_nhds w hεpos, ?_⟩
  intro w' hw'ball hw'crit
  by_contra hw'ne
  obtain ⟨c', hc'crit, hc'w'⟩ := hw'crit
  have hc'U : c' ∈ U := by
    by_contra hc'notU
    exact (hε hw'ball) ⟨c', hc'notU, hc'w'⟩
  obtain ⟨p, hc'Np⟩ := mem_iUnion.mp hc'U
  have hpw : Φ (p : X) = w := Set.mem_singleton_iff.mp p.2
  have hcp : c' = (p : X) := by
    have := (hNspec p).2.2 ⟨hc'Np, hc'crit⟩
    simpa using this
  exact hw'ne (by rw [← hc'w', hcp, hpw])

end Covering


section Final

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
  {Φ : X → ℂ}

private lemma locallyConstantAt_of_eventuallyEq_chart {c : X}
    (h : ∀ᶠ z in 𝓝 ((chartAt ℂ c) c),
      (Φ ∘ (chartAt ℂ c).symm) z = (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) c)) :
    LocallyConstantAt Φ c := by
  have hcont := (chartAt ℂ c).continuousAt (mem_chart_source ℂ c)
  have hzev' : ∀ᶠ y in 𝓝 c,
      (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) y) = (Φ ∘ (chartAt ℂ c).symm) ((chartAt ℂ c) c) :=
    hcont.eventually h
  have hsrc : ∀ᶠ y in 𝓝 c, y ∈ (chartAt ℂ c).source :=
    (chartAt ℂ c).open_source.mem_nhds (mem_chart_source ℂ c)
  have hev : ∀ᶠ y in 𝓝 c, Φ y = Φ c := by
    filter_upwards [hzev', hsrc] with y hy hys
    simp only [Function.comp_apply] at hy
    rw [(chartAt ℂ c).left_inv hys,
      (chartAt ℂ c).left_inv (mem_chart_source ℂ c)] at hy
    exact hy
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hev
  exact ⟨U, hUopen, hxU, fun y hy => hUsub hy⟩

private lemma bijective_of_natCard_fiber_eq_one {Φ : X → ℂ}
    (h : ∀ w, Nat.card (Φ ⁻¹' {w}) = 1) : Function.Bijective Φ := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · haveI : Subsingleton (Φ ⁻¹' {Φ a}) := (Nat.card_eq_one_iff_unique.mp (h (Φ a))).1
    exact Subtype.ext_iff.mp (Subsingleton.elim (⟨a, rfl⟩ : Φ ⁻¹' {Φ a}) ⟨b, hab.symm⟩)
  · have hpos : 0 < Nat.card (Φ ⁻¹' {w}) := by rw [h w]; norm_num
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x.1, x.2⟩

end Final


/-- **Main lemma.** A proper holomorphic map `Φ : X → ℂ` on a connected complex curve `X` whose
only zero is a simple one is bijective. -/
theorem bijective_of_isProperMap_holomorphic_single_zero {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ} {z₀ : X}
    (hhol : ∀ x : X, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hprop : IsProperMap Φ) (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Function.Bijective Φ := by
  have hnlc : ∀ y, ¬ LocallyConstantAt Φ y :=
    not_locallyConstantAt_of_deriv_ne_zero (Φ := Φ) hhol hloc
  have h0notmem : (0 : ℂ) ∉ critVal Φ := by
    rintro ⟨x, hxc, hx0⟩
    have hxz : x = z₀ := by
      have hx : x ∈ Φ ⁻¹' {(0 : ℂ)} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hx0
      rw [hfib] at hx
      simpa using hx
    rw [hxz] at hxc
    exact hloc (deriv_eq_zero_of_not_isLocalHomeoAt (Φ := Φ) (hhol z₀) hxc)
  have hcard0 : Nat.card (Φ ⁻¹' {(0 : ℂ)}) = 1 := by
    rw [hfib]; exact Nat.card_unique
  have hcritEmpty : Crit Φ = ∅ := by
    by_contra hne
    obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hw₀ : Φ c₀ ∈ critVal Φ := ⟨c₀, hc₀, rfl⟩
    obtain ⟨N₀, hN₀mem, hN₀⟩ := critVal_isolated hprop hhol hnlc hw₀
    obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.mem_nhds_iff.mp hN₀mem
    have hncψ : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ c₀) c₀),
        (Φ ∘ (chartAt ℂ c₀).symm) z = (Φ ∘ (chartAt ℂ c₀).symm) ((chartAt ℂ c₀) c₀) :=
      fun h => hnlc c₀ (locallyConstantAt_of_eventuallyEq_chart h)
    have hderiv0 : deriv (Φ ∘ (chartAt ℂ c₀).symm) ((chartAt ℂ c₀) c₀) = 0 :=
      deriv_eq_zero_of_not_isLocalHomeoAt (Φ := Φ) (hhol c₀) hc₀
    have hψcc : (Φ ∘ (chartAt ℂ c₀).symm) ((chartAt ℂ c₀) c₀) = Φ c₀ := by
      simp only [Function.comp_apply]
      rw [(chartAt ℂ c₀).left_inv (mem_chart_source ℂ c₀)]
    obtain ⟨εt, hεtpos, hεt⟩ := Metric.mem_nhds_iff.mp
      ((chartAt ℂ c₀).open_target.mem_nhds ((chartAt ℂ c₀).map_source (mem_chart_source ℂ c₀)))
    have hεpos : 0 < min ε₀ εt := lt_min hε₀pos hεtpos
    obtain ⟨w', hw'ne, hw'lt, a', b', ha'b', ha'lt, hb'lt, hfa, hfb⟩ :=
      exists_two_preimages_near_of_deriv_eq_zero (hhol c₀) hderiv0 hncψ hεpos
    rw [hψcc] at hw'ne
    have hball_a : a' ∈ Metric.ball ((chartAt ℂ c₀) c₀) εt := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le ha'lt (min_le_right ε₀ εt)
    have hball_b : b' ∈ Metric.ball ((chartAt ℂ c₀) c₀) εt := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hb'lt (min_le_right ε₀ εt)
    have ha'tgt : a' ∈ (chartAt ℂ c₀).target := hεt hball_a
    have hb'tgt : b' ∈ (chartAt ℂ c₀).target := hεt hball_b
    have hw'close : dist w' (Φ c₀) < ε₀ := by
      rw [dist_eq_norm, ← hψcc]
      exact lt_of_lt_of_le hw'lt (min_le_left ε₀ εt)
    have hinj : (chartAt ℂ c₀).symm a' ≠ (chartAt ℂ c₀).symm b' := by
      intro h
      apply ha'b'
      have hh := congrArg (chartAt ℂ c₀) h
      rwa [(chartAt ℂ c₀).right_inv ha'tgt, (chartAt ℂ c₀).right_inv hb'tgt] at hh
    have hma : (chartAt ℂ c₀).symm a' ∈ Φ ⁻¹' {w'} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      simpa only [Function.comp_apply] using hfa
    have hmb : (chartAt ℂ c₀).symm b' ∈ Φ ⁻¹' {w'} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      simpa only [Function.comp_apply] using hfb
    by_cases hw'crit : w' ∈ critVal Φ
    · exact hw'ne (hN₀ w' (hε₀ (Metric.mem_ball.mpr hw'close)) hw'crit)
    · have hcard := natCard_fiber_eq_one_off_critVal hprop hhol hnlc h0notmem hcard0 hw'crit
      haveI : Subsingleton (Φ ⁻¹' {w'}) := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact hinj (Subtype.ext_iff.mp (Subsingleton.elim ⟨_, hma⟩ ⟨_, hmb⟩))
  have hcritValEmpty : critVal Φ = ∅ := by
    rw [critVal, hcritEmpty, Set.image_empty]
  refine bijective_of_natCard_fiber_eq_one (fun w => ?_)
  have hw : w ∉ critVal Φ := by rw [hcritValEmpty]; exact nofun
  exact natCard_fiber_eq_one_off_critVal hprop hhol hnlc h0notmem hcard0 hw

end Commons.Analysis.Complex

