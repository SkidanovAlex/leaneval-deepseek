import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Submission.Commons.Geometry.Manifold.analyticAt_pullback_iff_chart
import Submission.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected

open Set Filter Function Metric
open scoped Topology Manifold ContDiff

namespace Commons.Analysis.Complex.ProperIntoBall

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false


/-! ## Preliminaries on the unit ball of `ℂ` -/

/-- The inclusion of the unit ball of `ℂ` into `ℂ`, as an open partial homeomorphism. -/
private noncomputable def ballIncl : OpenPartialHomeomorph (Metric.ball (0 : ℂ) 1) ℂ :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph (Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ)
    (Metric.isOpen_ball.isOpenEmbedding_subtypeVal)

/-- The inverse of `ballIncl`. -/
private noncomputable def ballCoe : OpenPartialHomeomorph ℂ (Metric.ball (0 : ℂ) 1) :=
  ballIncl.symm

private theorem ballCoe_source : ballCoe.source = Metric.ball (0 : ℂ) 1 := by
  simp only [ballCoe, ballIncl, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_val]

private theorem ballCoe_apply (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    ballCoe z = (⟨z, hz⟩ : Metric.ball (0 : ℂ) 1) := by
  have h := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
    (Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ)
    (Metric.isOpen_ball.isOpenEmbedding_subtypeVal)
    (x := (⟨z, hz⟩ : Metric.ball (0 : ℂ) 1))
  simpa only [ballCoe, ballIncl] using h

private lemma rank_gt_one_complex : 1 < Module.rank ℝ ℂ := by
  have h : Module.rank ℝ ℂ = 2 := by
    rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
    simp
  rw [h]; norm_num

/-- The complement of a countable set in the unit ball of `ℂ` (viewed as a subtype) is
preconnected. -/
private theorem isPreconnected_ball_compl_countable (C : Set ℂ) (hC : C.Countable) :
    IsPreconnected ((↑) ⁻¹' (Cᶜ) : Set (Metric.ball (0 : ℂ) 1)) := by
  set e : ℂ ≃ₜ Metric.ball (0 : ℂ) 1 := Homeomorph.unitBall with he
  have hinj : Function.Injective (fun z : ℂ => ((e z : Metric.ball (0 : ℂ) 1) : ℂ)) :=
    fun a b hab => e.injective (Subtype.ext hab)
  have hpre : e ⁻¹' ((↑) ⁻¹' (Cᶜ) : Set (Metric.ball (0 : ℂ) 1))
      = ((fun z : ℂ => ((e z : Metric.ball (0 : ℂ) 1) : ℂ)) ⁻¹' C)ᶜ := by
    ext z; simp only [mem_preimage, mem_compl_iff]
  have hconn : IsConnected (e ⁻¹' ((↑) ⁻¹' (Cᶜ) : Set (Metric.ball (0 : ℂ) 1))) := by
    rw [hpre]
    exact Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ) rank_gt_one_complex
      (hC.preimage hinj)
  exact (Homeomorph.isPreconnected_preimage e).mp hconn.isPreconnected

/-- The corestriction of a map with values in the unit ball. -/
private def toBall {X : Type*} {Φ : X → ℂ} (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1) :
    X → Metric.ball (0 : ℂ) 1 := fun x => ⟨Φ x, hmaps x⟩

/-- The centre of the unit ball, as a point of the ball. -/
private def zeroBall : Metric.ball (0 : ℂ) 1 :=
  ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)⟩

@[simp] private theorem zeroBall_coe : (zeroBall : ℂ) = 0 := rfl

/-- The corestriction of a continuous map with values in the open unit ball, whose preimages of
compact subsets of the ball are compact, is a closed map. -/
private theorem isClosedMap_toBall {X : Type*} [TopologicalSpace X] [T2Space X] {Φ : X → ℂ}
    (hcont : Continuous Φ) (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (Φ ⁻¹' K)) :
    IsClosedMap (toBall hmaps) := by
  set U : Set ℂ := Metric.ball (0 : ℂ) 1 with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  set g : X → U := fun x => ⟨Φ x, hmaps x⟩ with hg
  have hgc : Continuous g := hcont.subtype_mk _
  have hmain : IsClosedMap g := by
    intro F hF
    rw [← closure_subset_iff_isClosed]
    rintro y hy
    obtain ⟨r, hrpos, hrB⟩ : ∃ r > 0, closedBall (y : ℂ) r ⊆ U := by
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds y.2)
      refine ⟨r / 2, by positivity, fun z hz => hsub ?_⟩
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
    set K : Set ℂ := closedBall (y : ℂ) r with hK
    have hKcompact : IsCompact K := isCompact_closedBall _ _
    have hKB : K ⊆ U := hrB
    have hcompK : IsCompact (Φ ⁻¹' K) := hprop K hKcompact hKB
    have hKB_nhds : ((↑) ⁻¹' K : Set U) ∈ 𝓝 y := by
      have h1 : K ∈ 𝓝 (y : ℂ) := Metric.closedBall_mem_nhds _ hrpos
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds h1
    have hyK : y ∈ closure (g '' F ∩ ((↑) ⁻¹' K : Set U)) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro V hV
      have hVK : V ∩ ((↑) ⁻¹' K : Set U) ∈ 𝓝 y := Filter.inter_mem hV hKB_nhds
      obtain ⟨z, hz⟩ := hy (V ∩ ((↑) ⁻¹' K : Set U)) hVK
      exact ⟨z, hz.1.1, hz.2, hz.1.2⟩
    have himg : g '' (F ∩ g ⁻¹' ((↑) ⁻¹' K : Set U)) = (g '' F) ∩ ((↑) ⁻¹' K : Set U) := by
      ext z; constructor
      · rintro ⟨x, ⟨hxF, hxK⟩, rfl⟩
        exact ⟨⟨x, hxF, rfl⟩, hxK⟩
      · rintro ⟨⟨x, hxF, rfl⟩, hxK⟩
        exact ⟨x, ⟨hxF, hxK⟩, rfl⟩
    have hpre : g ⁻¹' ((↑) ⁻¹' K : Set U) = Φ ⁻¹' K := by
      ext x; rfl
    have hclosed : IsClosed ((g '' F) ∩ ((↑) ⁻¹' K : Set U)) := by
      rw [← himg]
      refine ((hcompK.of_isClosed_subset ?_ ?_).image hgc).isClosed
      · rw [hpre]
        exact hF.inter hcompK.isClosed
      · exact inter_subset_right
    exact (hclosed.closure_subset hyK).1
  have : toBall hmaps = g := rfl
  rw [this]
  exact hmain

/-- Every fibre of a map into the ball whose preimages of compact subsets of the ball are compact
is compact (as a subset of the domain). -/
private lemma isCompact_fiber {X : Type*} [TopologicalSpace X] {Φ : X → ℂ}
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (Φ ⁻¹' K))
    (w : ℂ) : IsCompact (Φ ⁻¹' {w}) := by
  by_cases hw : w ∈ Metric.ball (0 : ℂ) 1
  · exact hprop {w} isCompact_singleton (Set.singleton_subset_iff.mpr hw)
  · have h : Φ ⁻¹' {w} = ∅ := by
      ext x; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hx; exact hw (hx ▸ hmaps x)
    rw [h]; exact isCompact_empty

/-- Local analyticity in charts implies continuity. -/
private lemma continuous_of_analyticAt_charts {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {Φ : X → ℂ}
    (hhol : ∀ x : X, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : ContinuousAt (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := (hhol x).continuousAt
  have h2 : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have h3 : ContinuousAt ((Φ ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) x := h1.comp h2
  refine h3.congr ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  simp only [Function.comp_apply]
  rw [(chartAt ℂ x).left_inv hy]
private def IsLocalHomeoAt {X : Type*} [TopologicalSpace X] (Φ : X → ℂ) (x : X) : Prop :=
  ∃ e : OpenPartialHomeomorph X ℂ, x ∈ e.source ∧ Set.EqOn Φ e e.source

private def LocallyConstantAt {X : Type*} [TopologicalSpace X] (Φ : X → ℂ) (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, Φ y = Φ x


/-- At a point where `Φ` is a local homeomorphism onto `ℂ` and takes values in the ball, `Φ` is a
local homeomorphism onto the ball. -/
private theorem exists_openPartialHomeomorph_toBall {X : Type*} [TopologicalSpace X]
    {Φ : X → ℂ} (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1) {x : X}
    (hx : IsLocalHomeoAt Φ x) :
    ∃ e' : OpenPartialHomeomorph X (Metric.ball (0 : ℂ) 1),
      x ∈ e'.source ∧ EqOn (toBall hmaps) e' e'.source := by
  obtain ⟨e, hxe, heq⟩ := hx
  refine ⟨e.trans ballCoe, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hxe, ?_⟩
    simp only [Set.mem_preimage]
    rw [ballCoe_source]
    rw [← heq hxe]
    exact hmaps x
  · intro y hy
    rw [OpenPartialHomeomorph.trans_apply]
    have hy1 : y ∈ e.source := hy.1
    have hy2 : e y ∈ ballCoe.source := hy.2
    rw [ballCoe_source] at hy2
    rw [ballCoe_apply (e y) hy2]
    exact Subtype.ext (heq hy1)
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
  [LindelofSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
  {Φ : X → ℂ}

/-- The set of points where `Φ` is not a local homeomorphism. -/
private def Crit (Φ : X → ℂ) : Set X := {x | ¬ IsLocalHomeoAt Φ x}

/-- The set of critical values of `Φ`. -/
private def critVal (Φ : X → ℂ) : Set ℂ := Φ '' Crit Φ

private lemma isClosed_crit : IsClosed (Crit Φ) :=
  (isOpen_isLocalHomeoAt (Φ := Φ)).isClosed_compl

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

/-- Critical values of a map into the ball lie in the ball. -/
private lemma critVal_subset_ball
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1) : critVal Φ ⊆ Metric.ball (0 : ℂ) 1 :=
  fun _ ⟨x, _, hx⟩ => hx ▸ hmaps x

end Global

section Covering

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [LindelofSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
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

/-- The complement of the critical values, inside the ball, is preconnected. -/
private lemma critVal_compl_preconnected
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) :
    IsPreconnected ((↑) ⁻¹' ((critVal Φ)ᶜ) : Set (Metric.ball (0 : ℂ) 1)) :=
  isPreconnected_ball_compl_countable (critVal Φ) (critVal_countable hhol hnlc)

private lemma finite_fiber_off_critVal (hcompact : ∀ w : ℂ, IsCompact (Φ ⁻¹' {w}))
    {w : ℂ} (hw : w ∉ critVal Φ) : (Φ ⁻¹' {w}).Finite := by
  refine (hcompact w).finite ?_
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

/-- Off the critical values, `toBall hmaps` is a local homeomorphism (onto the ball). -/
private lemma isLocalHomeomorphOn_toBall_off_critVal
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) :
    IsLocalHomeomorphOn (toBall hmaps)
      ((toBall hmaps) ⁻¹' ((↑) ⁻¹' ((critVal Φ)ᶜ) : Set (Metric.ball (0 : ℂ) 1))) :=
  IsLocalHomeomorphOn.mk _ _ (fun x hx => by
    have hx' : (toBall hmaps x : ℂ) ∉ critVal Φ := by simpa using hx
    have hxc : IsLocalHomeoAt Φ x := by
      by_contra hcon
      exact hx' ⟨x, hcon, rfl⟩
    exact exists_openPartialHomeomorph_toBall hmaps hxc)

/-- Off the critical values, `toBall hmaps` is a covering map. -/
private lemma isCoveringMapOn_toBall_off_critVal
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hgclosed : IsClosedMap (toBall hmaps))
    (hcompact : ∀ w : ℂ, IsCompact (Φ ⁻¹' {w}))
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) :
    IsCoveringMapOn (toBall hmaps)
      ((↑) ⁻¹' ((critVal Φ)ᶜ) : Set (Metric.ball (0 : ℂ) 1)) :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hgclosed
    (fun w _ => by
      have hset : (toBall hmaps) ⁻¹' {w} = Φ ⁻¹' {(w : ℂ)} := by
        ext x; rw [mem_preimage, mem_preimage, mem_singleton_iff, mem_singleton_iff,
          Subtype.ext_iff]; rfl
      rw [hset]
      exact (hcompact (w : ℂ)).finite (isDiscrete_fiber hhol hnlc (w : ℂ)))
    (isLocalHomeomorphOn_toBall_off_critVal hmaps hhol hnlc)

private lemma natCard_fiber_eq_one_off_critVal
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hgclosed : IsClosedMap (toBall hmaps))
    (hcompact : ∀ w : ℂ, IsCompact (Φ ⁻¹' {w}))
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) (h0 : (0 : ℂ) ∉ critVal Φ)
    (hcard0 : Nat.card ((toBall hmaps) ⁻¹' {zeroBall}) = 1)
    {w : Metric.ball (0 : ℂ) 1} (hw : (w : ℂ) ∉ critVal Φ) :
    Nat.card ((toBall hmaps) ⁻¹' {w}) = 1 := by
  have h := Commons.Topology.Covering.natCard_fiber_eq_of_preconnected
    (isCoveringMapOn_toBall_off_critVal hmaps hgclosed hcompact hhol hnlc)
    (critVal_compl_preconnected hhol hnlc) (a := zeroBall) (b := w)
    (by simp only [mem_preimage, mem_compl_iff, zeroBall_coe]; exact h0)
    (by simp only [mem_preimage, mem_compl_iff]; exact hw)
  rw [hcard0] at h
  exact h.symm

/-- Any critical value is an isolated point of the set of critical values. -/
private lemma critVal_isolated
    (hmaps : ∀ x, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hgclosed : IsClosedMap (toBall hmaps))
    (hhol : ∀ x, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hnlc : ∀ y, ¬ LocallyConstantAt Φ y) {w : Metric.ball (0 : ℂ) 1}
    (hw : (w : ℂ) ∈ critVal Φ) :
    ∃ N ∈ 𝓝 w, ∀ w' ∈ N, (w' : ℂ) ∈ critVal Φ → w' = w := by
  classical
  have hN : ∀ p : Φ ⁻¹' {(w : ℂ)}, ∃ N : Set X, IsOpen N ∧ (p : X) ∈ N ∧
      N ∩ Crit Φ ⊆ {(p : X)} := by
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
  let N : Φ ⁻¹' {(w : ℂ)} → Set X := fun p => (hN p).choose
  have hNspec : ∀ p, IsOpen (N p) ∧ (p : X) ∈ N p ∧ N p ∩ Crit Φ ⊆ {(p : X)} :=
    fun p => (hN p).choose_spec
  let U : Set X := ⋃ p : Φ ⁻¹' {(w : ℂ)}, N p
  have hUopen : IsOpen U := isOpen_iUnion fun p => (hNspec p).1
  have hfibsub : Φ ⁻¹' {(w : ℂ)} ⊆ U :=
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (hNspec ⟨x, hx⟩).2.1⟩
  have hclosed : IsClosed ((toBall hmaps) '' Uᶜ) := hgclosed Uᶜ hUopen.isClosed_compl
  have hwnot : w ∉ (toBall hmaps) '' Uᶜ := by
    rintro ⟨x, hxU, hxw⟩
    have hxw' : Φ x = (w : ℂ) := Subtype.ext_iff.mp hxw
    exact hxU (hfibsub (by simpa only [mem_preimage, mem_singleton_iff] using hxw'))
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hwnot)
  refine ⟨Metric.ball w ε, Metric.ball_mem_nhds w hεpos, ?_⟩
  intro w' hw'ball hw'crit
  by_contra hw'ne
  obtain ⟨c', hc'crit, hc'w'⟩ := hw'crit
  have hc'U : c' ∈ U := by
    by_contra hc'notU
    refine (hε hw'ball) ⟨c', hc'notU, ?_⟩
    exact Subtype.ext (by simpa only [toBall] using hc'w')
  obtain ⟨p, hc'Np⟩ := mem_iUnion.mp hc'U
  have hpw : Φ (p : X) = (w : ℂ) := Set.mem_singleton_iff.mp p.2
  have hcp : c' = (p : X) := by
    have := (hNspec p).2.2 ⟨hc'Np, hc'crit⟩
    simpa using this
  exact hw'ne (Subtype.ext (by rw [← hc'w', hcp, hpw]))

end Covering
section Final

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [LindelofSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
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

private lemma bijective_of_natCard_fiber_eq_one {X Y : Type*} {f : X → Y}
    (h : ∀ w, Nat.card (f ⁻¹' {w}) = 1) : Function.Bijective f := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · haveI : Subsingleton (f ⁻¹' {f a}) := (Nat.card_eq_one_iff_unique.mp (h (f a))).1
    exact Subtype.ext_iff.mp (Subsingleton.elim (⟨a, rfl⟩ : f ⁻¹' {f a}) ⟨b, hab.symm⟩)
  · have hpos : 0 < Nat.card (f ⁻¹' {w}) := by rw [h w]; norm_num
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x.1, x.2⟩

end Final

/-- **Main lemma.** A proper holomorphic map `Φ : X → ℂ` from a connected Riemann surface into the
unit ball, whose only zero is a simple one, is a bijection onto the ball. -/
theorem bijective_of_isProperMap_into_ball_single_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Φ : X → ℂ} {z₀ : X}
    (hmaps : ∀ x : X, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (Φ ⁻¹' K))
    (hΦ : ∀ x : X, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Function.Bijective (fun x : X => (⟨Φ x, hmaps x⟩ : Metric.ball (0 : ℂ) 1)) := by
  classical
  -- The proper map into the ball makes `X` σ-compact, hence Lindelöf.
  haveI : SigmaCompactSpace X := by
    rw [← isSigmaCompact_univ_iff]
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) (1 - 1 / ((n : ℝ) + 1)))
        = Metric.ball (0 : ℂ) 1 := by
      ext z; constructor
      · intro hz
        rw [Set.mem_iUnion] at hz
        obtain ⟨n, hn⟩ := hz
        rw [Metric.mem_closedBall, dist_zero_right] at hn
        rw [Metric.mem_ball, dist_zero_right]
        have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        rw [Set.mem_iUnion]
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < 1 - ‖z‖ by linarith)
        exact ⟨n, by rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
    refine ⟨fun n => Φ ⁻¹' Metric.closedBall (0 : ℂ) (1 - 1 / ((n : ℝ) + 1)), ?_, ?_⟩
    · intro n
      refine hprop _ (isCompact_closedBall _ _) ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · ext x
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
      have hmem : Φ x ∈ ⋃ n : ℕ, Metric.closedBall (0 : ℂ) (1 - 1 / ((n : ℝ) + 1)) := by
        rw [hcover]; exact hmaps x
      simpa only [Set.mem_iUnion] using hmem
  have hhol : ∀ x : X, AnalyticAt ℂ (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hΦ
  have hnlc : ∀ y, ¬ LocallyConstantAt Φ y :=
    not_locallyConstantAt_of_deriv_ne_zero (Φ := Φ) hhol hloc
  have hcont : Continuous Φ := continuous_of_analyticAt_charts hhol
  have hgclosed : IsClosedMap (toBall hmaps) := isClosedMap_toBall hcont hmaps hprop
  have hcompact : ∀ w : ℂ, IsCompact (Φ ⁻¹' {w}) := fun w => isCompact_fiber hmaps hprop w
  have h0notmem : (0 : ℂ) ∉ critVal Φ := by
    rintro ⟨x, hxc, hx0⟩
    have hxz : x = z₀ := by
      have hx : x ∈ Φ ⁻¹' {(0 : ℂ)} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hx0
      rw [hfib] at hx
      simpa using hx
    rw [hxz] at hxc
    exact hloc (deriv_eq_zero_of_not_isLocalHomeoAt (Φ := Φ) (hhol z₀) hxc)
  have hcard0 : Nat.card ((toBall hmaps) ⁻¹' {zeroBall}) = 1 := by
    have hset : (toBall hmaps) ⁻¹' {zeroBall} = Φ ⁻¹' {(0 : ℂ)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, toBall, zeroBall]
    rw [hset, hfib]; exact Nat.card_unique
  have hcritEmpty : Crit Φ = ∅ := by
    by_contra hne
    obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    set w₀B : Metric.ball (0 : ℂ) 1 := ⟨Φ c₀, hmaps c₀⟩ with hw₀B
    have hw₀ : (w₀B : ℂ) ∈ critVal Φ := by
      rw [hw₀B]; exact ⟨c₀, hc₀, rfl⟩
    obtain ⟨N₀, hN₀mem, hN₀⟩ := critVal_isolated hmaps hgclosed hhol hnlc hw₀
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
    set w'B : Metric.ball (0 : ℂ) 1 := ⟨w', by rw [← hfa]; exact hmaps _⟩ with hw'B
    have hma : (chartAt ℂ c₀).symm a' ∈ (toBall hmaps) ⁻¹' {w'B} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext (by simpa only [Function.comp_apply, toBall, hw'B] using hfa)
    have hmb : (chartAt ℂ c₀).symm b' ∈ (toBall hmaps) ⁻¹' {w'B} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext (by simpa only [Function.comp_apply, toBall, hw'B] using hfb)
    by_cases hw'crit : w' ∈ critVal Φ
    · have hkey : w'B = w₀B :=
        hN₀ w'B (hε₀ (Metric.mem_ball.mpr (by simp only [hw'B, hw₀B, Subtype.dist_eq]; exact hw'close)))
          (by rw [hw'B]; exact hw'crit)
      exact hw'ne (Subtype.ext_iff.mp hkey)
    · have hcard := natCard_fiber_eq_one_off_critVal hmaps hgclosed hcompact hhol hnlc
        h0notmem hcard0 (w := w'B) (by rw [hw'B]; exact hw'crit)
      haveI : Subsingleton ((toBall hmaps) ⁻¹' {w'B}) := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact hinj (Subtype.ext_iff.mp (Subsingleton.elim ⟨_, hma⟩ ⟨_, hmb⟩))
  have hcritValEmpty : critVal Φ = ∅ := by
    rw [critVal, hcritEmpty, Set.image_empty]
  show Function.Bijective (toBall hmaps)
  refine bijective_of_natCard_fiber_eq_one (fun w => ?_)
  refine natCard_fiber_eq_one_off_critVal hmaps hgclosed hcompact hhol hnlc h0notmem hcard0 ?_
  simp [hcritValEmpty]

end Commons.Analysis.Complex.ProperIntoBall
