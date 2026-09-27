import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.cluster_points_atTop_injective
import Submission.Work.OneDim.local_diffeo_congr
import Submission.Work.OneDim.end_behavior_injective
import Submission.Work.OneDim.exists_maximal_arc_param
import Submission.Work.OneDim.arc_image_shape

/-!
# The dichotomy for connected smooth 1-manifolds

We record here the topological core of the classification of connected smooth 1-manifolds: the
*end behaviour of an injective curve*.

Let `γ : ℝ → C` be injective and continuous into a Hausdorff 1-manifold.  Then as `t → +∞`, either
`γ` converges to a point of `C`, or `γ` leaves every compact subset of `C`.  The proof is the
"crossing" argument: a small chart ball `N` around a hypothetical cluster point `x` has a boundary
consisting of at most two points, so an injective curve crosses it at most twice; after the last
crossing the curve stays either inside the closed ball or outside it, and since it meets `N`
arbitrarily late it stays inside.  Hence `γ` is eventually in every neighbourhood of `x`.

If there is no cluster point at all, then the curve must meet every compact set only for bounded
times — otherwise the compactness of the set produces a cluster point.
-/

open scoped Manifold Topology
open Set Function Filter

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [T2Space C]

/-- **Nice chart balls.**  Every neighbourhood `V` of `x` in a 1-manifold contains the closure of
an open chart ball `N` around `x` whose boundary `closure N \ N` consists of at most two points. -/
lemma exists_nice_ball {x : C} {V : Set C} (hV : V ∈ 𝓝 x) :
    ∃ N : Set C, IsOpen N ∧ x ∈ N ∧ closure N ⊆ V ∧
      ∃ p q : C, closure N \ N ⊆ ({p, q} : Set C) := by
  classical
  set φ := chartAt E1 x with hφ
  have hxsrc : x ∈ φ.source := mem_chart_source _ _
  have hmem : φ '' (V ∩ φ.source) ∈ 𝓝 (φ x) :=
    φ.image_mem_nhds hxsrc (Filter.inter_mem hV (φ.open_source.mem_nhds hxsrc))
  have htarget : φ.target ∈ 𝓝 (φ x) := φ.open_target.mem_nhds (φ.map_source hxsrc)
  obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp htarget
  obtain ⟨ε', hε', hε'sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  set r : ℝ := min ε ε' with hr
  have hrpos : 0 < r := lt_min hε hε'
  have hrsub : Metric.closedBall (φ x) r ⊆ φ.target :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hεsub
  have hrsub' : Metric.closedBall (φ x) r ⊆ φ '' (V ∩ φ.source) :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hε'sub
  have hKeq : φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r
      = φ.symm '' Metric.closedBall (φ x) r :=
    (φ.symm_image_eq_source_inter_preimage hrsub).symm
  have hKcompact : IsCompact (φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r) := by
    rw [hKeq]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      (φ.symm.continuousOn_toFun.mono hrsub)
  have hsub : φ.source ∩ φ ⁻¹' Metric.ball (φ x) r
      ⊆ φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r :=
    Set.inter_subset_inter le_rfl (preimage_mono Metric.ball_subset_closedBall)
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ x) r, φ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hxsrc, Metric.mem_ball_self hrpos⟩, ?_, ?_⟩
  · refine (closure_minimal hsub hKcompact.isClosed).trans ?_
    rw [hKeq]
    rintro y ⟨y', hy', rfl⟩
    obtain ⟨z, hz, hzy⟩ := hrsub' hy'
    rw [← hzy, φ.left_inv hz.2]
    exact hz.1
  · refine ⟨φ.symm (φ x + r • EuclideanSpace.single (𝕜 := ℝ) 0 1),
      φ.symm (φ x - r • EuclideanSpace.single (𝕜 := ℝ) 0 1), ?_⟩
    rintro z ⟨hzcl, hzN⟩
    have hzK : z ∈ φ.source ∩ φ ⁻¹' Metric.closedBall (φ x) r :=
      closure_minimal hsub hKcompact.isClosed hzcl
    have hzsource : z ∈ φ.source := hzK.1
    have hzcb : φ z ∈ Metric.closedBall (φ x) r := hzK.2
    have hznb : φ z ∉ Metric.ball (φ x) r := fun hb => hzN ⟨hzsource, hb⟩
    have hzsphere : φ z ∈ Metric.sphere (φ x) r := by
      rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hzcb)
        (le_of_not_gt fun hh => hznb (Metric.mem_ball.mpr hh))
    rcases sphere_fin_one_subset (φ x) r hzsphere with h | h
    · left; rw [← φ.left_inv hzsource, h]
    · right; rw [← φ.left_inv hzsource, h]; simp

/-- **The crossing argument.**  If `x` is a cluster point at `+∞` of an injective curve, then for
every nice chart ball `N` around `x` (with a two-point boundary) the curve is eventually inside
`closure N`. -/
lemma eventually_mem_closure_of_clusterPt {γ : ℝ → C} (hγ : Continuous γ) (hinj : Injective γ)
    {x : C} (hx : ClusterPt x (Filter.map γ Filter.atTop)) {N : Set C} (hN : IsOpen N) (hxN : x ∈ N)
    {p q : C} (hbd : closure N \ N ⊆ ({p, q} : Set C)) :
    ∃ T : ℝ, ∀ t ≥ T, γ t ∈ closure N := by
  classical
  have hbd' : (closure N \ N).Finite :=
    ((Set.finite_singleton q).insert p).subset fun z hz => hbd hz
  have hfin : (γ ⁻¹' (closure N \ N)).Finite := Set.Finite.preimage (f := γ) hinj.injOn hbd'
  obtain ⟨T, hT⟩ := hfin.bddAbove
  refine ⟨T + 1, fun t ht => ?_⟩
  by_contra hcon
  have hpre : IsPreconnected (γ '' Ioi T) := isPreconnected_Ioi.image γ hγ.continuousOn
  have hdisj : Disjoint N (closure N)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2 (subset_closure hz1)
  have hsub : γ '' Ioi T ⊆ N ∪ (closure N)ᶜ := by
    rintro z ⟨s, hs, rfl⟩
    by_cases hz : γ s ∈ N
    · exact Or.inl hz
    · exact Or.inr fun hzcl =>
        absurd (hT ⟨hzcl, hz⟩) (not_le.mpr hs)
  have hcover : γ '' Ioi T ⊆ closure N := by
    rcases hpre.subset_or_subset hN isClosed_closure.isOpen_compl hdisj hsub with h | h
    · exact h.trans subset_closure
    · exfalso
      have hfreq : ∃ᶠ y in Filter.map γ Filter.atTop, y ∈ N :=
        hx.frequently (hN.mem_nhds hxN)
      have hfreq' : ∃ᶠ s in Filter.atTop, γ s ∈ N := hfreq
      obtain ⟨s, hs, hsN⟩ := (Filter.frequently_atTop.mp hfreq') (T + 1)
      exact h ⟨s, lt_of_lt_of_le (lt_add_one T) hs, rfl⟩ (subset_closure hsN)
  exact hcon (hcover ⟨t, lt_of_lt_of_le (lt_add_one T) ht, rfl⟩)

/-- **End behaviour of an injective curve in a Hausdorff 1-manifold.**  At `+∞` the curve either
converges to a point, or leaves every compact set. -/
theorem tendsto_or_leaves_compact_atTop (γ : ℝ → C) (hγ : Continuous γ) (hinj : Injective γ) :
    (∃ x : C, Tendsto γ atTop (𝓝 x)) ∨
      (∀ K : Set C, IsCompact K → ∃ T : ℝ, ∀ t ≥ T, γ t ∉ K) := by
  classical
  by_cases h : ∃ x : C, ClusterPt x (Filter.map γ Filter.atTop)
  · left
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    intro V hV
    rw [Filter.mem_map]
    obtain ⟨N, hN, hxN, hNV, p, q, hbd⟩ := exists_nice_ball (x := x) hV
    obtain ⟨T, hT⟩ := eventually_mem_closure_of_clusterPt hγ hinj hx hN hxN hbd
    have hsub : Ici T ⊆ γ ⁻¹' V := fun t ht => hNV (hT t ht)
    exact Filter.mem_of_superset (Ici_mem_atTop T) hsub
  · right
    intro K hK
    by_contra hbad
    have hbad' : ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ γ t ∈ K := by
      intro T
      by_contra hcon
      apply hbad
      refine ⟨T, fun t ht => ?_⟩
      by_contra hmem
      exact hcon ⟨t, ht, hmem⟩
    have hne : (Filter.map γ Filter.atTop ⊓ Filter.principal K).NeBot := by
      rw [Filter.neBot_iff]
      intro hbot
      have hemp : (∅ : Set C) ∈ Filter.map γ Filter.atTop ⊓ Filter.principal K := by
        rw [hbot]; exact Filter.mem_bot
      rw [Filter.mem_inf_iff] at hemp
      obtain ⟨s₁, hs₁, s₂, hs₂, heq⟩ := hemp
      rw [Filter.mem_map] at hs₁
      rw [Filter.mem_atTop_sets] at hs₁
      obtain ⟨T, hT⟩ := hs₁
      obtain ⟨t, htT, htK⟩ := hbad' T
      have h1 : γ t ∈ s₁ := hT t htT
      have h2 : γ t ∈ s₂ := hs₂ htK
      have h3 : γ t ∈ s₁ ∩ s₂ := ⟨h1, h2⟩
      rw [← heq] at h3
      exact h3
    haveI := hne
    obtain ⟨y, hyK, hy⟩ := hK.exists_clusterPt
      (f := Filter.map γ Filter.atTop ⊓ Filter.principal K) inf_le_right
    exact h ⟨y, hy.of_inf_left⟩

/-- End behaviour at `-∞`, by symmetry. -/
theorem tendsto_or_leaves_compact_atBot (γ : ℝ → C) (hγ : Continuous γ) (hinj : Injective γ) :
    (∃ x : C, Tendsto γ atBot (𝓝 x)) ∨
      (∀ K : Set C, IsCompact K → ∃ T : ℝ, ∀ t ≤ T, γ t ∉ K) := by
  have hcomp : Continuous fun s : ℝ => γ (-s) := hγ.comp continuous_neg
  have hinj' : Injective fun s : ℝ => γ (-s) := fun a b hab => by
    have h := hinj hab
    simpa using h
  obtain h | h := tendsto_or_leaves_compact_atTop (fun s : ℝ => γ (-s)) hcomp hinj'
  · left
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    rw [show (fun s : ℝ => γ (-s)) = γ ∘ fun s : ℝ => -s from rfl,
      ← Filter.tendsto_map'_iff, Filter.map_neg_atTop] at hx
    exact hx
  · right
    intro K hK
    obtain ⟨T, hT⟩ := h K hK
    refine ⟨-T, fun t ht => ?_⟩
    have h1 : (-t : ℝ) ≥ T := by linarith
    have := hT (-t) h1
    simpa using this

section Assembly

variable [IsManifold I1 sm C]

/-- **A bijective local diffeomorphism `ℝ → C` is a diffeomorphism.** -/
theorem nonempty_diffeomorph_of_bijective_localDiffeomorph (φ : ℝ → C)
    (hbij : Function.Bijective φ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ C sm) := by
  classical
  have hcont : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm φ := fun x => (hld x).contMDiffAt
  have hinv : ContMDiff I1 (modelWithCornersSelf ℝ ℝ) sm (Function.invFun φ) := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    have h := (hld x).localInverse_contMDiffAt
    rw [hx] at h
    refine h.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem (s := (hld x).localInverse.source) ?_ ?_
    · exact hx ▸ ((hld x).localInverse_open_source.mem_nhds (hld x).localInverse_mem_source)
    · intro y' hy'
      have h1 : φ (Function.invFun φ y') = y' := Function.invFun_eq (hbij.2 y')
      have h2 : φ ((hld x).localInverse y') = y' := (hld x).localInverse_right_inv hy'
      exact hbij.1 (h1.trans h2.symm)
  refine ⟨Diffeomorph.mk ⟨φ, Function.invFun φ,
    Function.leftInverse_invFun hbij.1, Function.rightInverse_invFun hbij.2⟩ hcont ?_⟩
  simpa using hinv

/-- **An injective local diffeomorphism `ℝ → C` with range an open subset `U`.**  Then `ℝ` is
diffeomorphic to `U`. -/
theorem nonempty_diffeomorph_of_injective_localDiffeomorph_subtype (U : TopologicalSpace.Opens C)
    (φ : ℝ → C) (hinj : Function.Injective φ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ)
    (hrange : Set.range φ = (U : Set C)) :
    Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ ↥U sm) := by
  classical
  have hcont : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm φ := fun x => (hld x).contMDiffAt
  have hmem : ∀ t : ℝ, φ t ∈ (U : Set C) := fun t => by
    rw [← hrange]; exact ⟨t, rfl⟩
  set F : ℝ → ↥U := fun t => ⟨φ t, hmem t⟩ with hF
  have hbijF : Function.Bijective F := by
    constructor
    · intro a b hab
      exact hinj (Subtype.ext_iff.mp hab)
    · intro y
      have hy : (y : C) ∈ Set.range φ := by rw [hrange]; exact y.2
      obtain ⟨t, ht⟩ := hy
      exact ⟨t, Subtype.ext ht⟩
  have hcontF : ContMDiff (modelWithCornersSelf ℝ ℝ) I1 sm F := by
    intro t
    have : ContMDiffAt (modelWithCornersSelf ℝ ℝ) I1 sm
        ((Subtype.val : ↥U → C) ∘ F) t := by
      simpa [hF, Function.comp_def] using (hld t).contMDiffAt
    simpa using this
  set G : ↥U → ℝ := fun y => Function.invFun φ (y : C) with hG
  have hleft : Function.LeftInverse G F := by
    intro t
    show Function.invFun φ (φ t) = t
    exact Function.leftInverse_invFun hinj t
  have hright : Function.RightInverse G F := by
    intro y
    have h1 : φ (Function.invFun φ (y : C)) = (y : C) :=
      Function.invFun_eq (Set.mem_range.mp (by rw [hrange]; exact y.2))
    exact Subtype.ext h1
  have hcontG : ContMDiff I1 (modelWithCornersSelf ℝ ℝ) sm G := by
    intro y
    have hy : (y : C) ∈ Set.range φ := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := hy
    have h := (hld x).localInverse_contMDiffAt
    rw [hx] at h
    have hcomp : ContMDiffAt I1 (modelWithCornersSelf ℝ ℝ) sm
        ((fun z : C => (hld x).localInverse z) ∘ (Subtype.val : ↥U → C)) y :=
      ContMDiffAt.comp_of_eq h
        (((contMDiff_subtype_val :
          ContMDiff I1 I1 sm (Subtype.val : ↥U → C))).contMDiffAt) rfl
    refine hcomp.congr_of_eventuallyEq ?_
    refine Filter.eventuallyEq_of_mem
      (s := (Subtype.val : ↥U → C) ⁻¹' (hld x).localInverse.source) ?_ ?_
    · refine ((hld x).localInverse_open_source.preimage continuous_subtype_val).mem_nhds ?_
      show (y : C) ∈ (hld x).localInverse.source
      exact hx ▸ (hld x).localInverse_mem_source
    · intro y' hy'
      have h1 : φ (Function.invFun φ (y' : C)) = (y' : C) :=
        Function.invFun_eq (Set.mem_range.mp (by rw [hrange]; exact y'.2))
      have h2 : φ ((hld x).localInverse (y' : C)) = (y' : C) :=
        (hld x).localInverse_right_inv hy'
      exact hinj (h1.trans h2.symm)
  refine ⟨Diffeomorph.mk ⟨F, G, hleft, hright⟩ hcontF ?_⟩
  simpa using hcontG

end Assembly

/-! ## Status and plan for the dichotomy

What is proved in this file:

* `exists_nice_ball`, `eventually_mem_closure_of_clusterPt`, `tendsto_or_leaves_compact_atTop` and
  `tendsto_or_leaves_compact_atBot` — the topological end behaviour of an injective curve in a
  Hausdorff 1-manifold (the "crossing" argument);
* `nonempty_diffeomorph_of_bijective_localDiffeomorph` and
  `nonempty_diffeomorph_of_injective_localDiffeomorphism_subtype` — the two assembly steps turning
  parametrisation data into the `Diffeomorph`s appearing in the dichotomy.

What remains is exactly the structure-theorem data: a bijective local diffeomorphism `ℝ → C`, or a
point `q` and an injective local diffeomorphism `ℝ → C` with range `{q}ᶜ`.  This is isolated as
`Work.OneDim.exists_dichotomy_data` (delegated, file `Submission/Work/OneDim/exists_dichotomy_data.lean`);
the endgame proof in the present file has been verified conditional on that datum (see the scratch
file `_assembly_check.lean`).  The maximal arc (`Work.OneDim.exists_maximal_arc_param`) and the
parametrisation of an interval by `ℝ` (`Work.OneDim.real_interval_parametrization`) are already
proved in the workspace and feed into that datum. -/

/-- **Dichotomy for connected 1-manifolds.**  A connected (nonempty), Hausdorff, second countable
smooth 1-manifold is either diffeomorphic to `ℝ`, or it has a point whose complement is
diffeomorphic to `ℝ` (the latter is the circle case: `Circle \ {pt}` is an open interval).  This is
the classification of connected 1-manifolds *minus* the smoothing statement
`Work.OneDim.closing_diffeomorph_circle` that upgrades the second case to the circle. -/
theorem one_manifold_dichotomy {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    [T2Space C] [SecondCountableTopology C] [ConnectedSpace C] :
    (Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ C ((⊤ : ℕ∞) : WithTop ℕ∞))) ∨
    (∃ z : C, Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ
          ↥(⟨{y : C | y ≠ z}, isOpen_compl_singleton⟩ : TopologicalSpace.Opens C)
        ((⊤ : ℕ∞) : WithTop ℕ∞))) := by
  classical
  -- the structure-theorem datum, from the maximal arc and the end behaviour
  have hdata : (∃ φ : ℝ → C, Function.Bijective φ ∧
        IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ) ∨
      (∃ (q : C) (φ : ℝ → C), Function.Injective φ ∧
        IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ ∧
        Set.range φ = ({q} : Set C)ᶜ) := by
    obtain ⟨p⟩ : Nonempty C := inferInstance
    obtain ⟨s, γ, harc, hmax⟩ := exists_maximal_arc_param (C := C) p
    rcases arc_image_shape (C := C)
      (fun γ hγ hinj x hx => end_behavior_injective hγ hinj hx) harc hmax with
      ⟨φ, hbij, hld⟩ | ⟨q, φ, hinj, hld, hrange, -, -⟩
    · exact Or.inl ⟨φ, hbij, hld⟩
    · exact Or.inr ⟨q, φ, hinj, hld, hrange⟩
  -- assembly
  rcases hdata with h | ⟨q, φ, hinj, hld, hrange⟩
  · obtain ⟨φ, hbij, hld⟩ := h
    exact Or.inl (nonempty_diffeomorph_of_bijective_localDiffeomorph φ hbij hld)
  · refine Or.inr ⟨q, ?_⟩
    have hmain := nonempty_diffeomorph_of_injective_localDiffeomorph_subtype
      (⟨{y : C | y ≠ q}, isOpen_compl_singleton⟩ : TopologicalSpace.Opens C) φ hinj hld ?_
    · simpa using hmain
    · have hU : ((⟨{y : C | y ≠ q}, isOpen_compl_singleton⟩ : TopologicalSpace.Opens C) : Set C)
          = ({q} : Set C)ᶜ := by
        show {y : C | y ≠ q} = ({q} : Set C)ᶜ
        ext y
        simp [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [hU]
      exact hrange

end Work.OneDim
