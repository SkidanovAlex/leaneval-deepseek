import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.ArcDefs
import Submission.Work.OneDim.ArcSet
import Submission.Work.OneDim.interval_surj
import Submission.Work.OneDim.reparam_arc
import Submission.Work.OneDim.cluster_points_atTop_injective
import Submission.Work.OneDim.end_behavior_injective
import Submission.Work.OneDim.extend_arc
import Submission.Work.OneDim.chain_union

/-!
# Tools for the shape of a maximal arc in a connected smooth `1`-manifold

This file develops the geometry needed for `Work.OneDim.maximal_arc_shape`: a maximal open arc in a
connected smooth `1`-manifold is everything, or everything minus one point.

Main ingredients:

* `chartPD0`, `chartPD0neg`: the chart at a point, recentred at `0`, in the two orientations;
* `pdiBall`, `pdiClosed`: the (open/closed) "coordinate interval" of such a chart;
* `no_bounded_component`: the *crossing lemma* for the recentred chart — the preimage under an
  injective curve of a chart ball with a two point boundary has no bounded connected component;
* `extend_contra`: the contrapositive of `Work.OneDim.extend_arc`, in the form needed below;
* `frontier_subset_cluster`, `frontier_subsingleton`: the frontier of a maximal open arc is a single
  point, itself a cluster point of the parametrisation at `+∞` or at `-∞`.
-/

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-! ## Chart coordinates -/

/-- The coordinate of a chart, `C → E1 → ℝ`. -/
noncomputable def coordE : E1 ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

lemma coordE_apply (v : E1) : coordE v = v 0 := by
  have h1 : (LinearEquiv.funUnique (Fin 1) ℝ ℝ) v = v default :=
    congrFun (LinearEquiv.funUnique_apply (ι := Fin 1) (R := ℝ) (M := ℝ)) v
  have h2 : v default = v 0 := by
    rw [show (default : Fin 1) = 0 from Subsingleton.elim _ _]
  rw [show coordE v = (LinearEquiv.funUnique (Fin 1) ℝ ℝ) v from rfl, h1, h2]

lemma norm_eq_abs_coord (v : E1) : ‖v‖ = |v 0| := by
  simpa using norm_sub_eq_abs_coord v 0

/-- The coordinate chart at `q`, as a partial diffeomorphism `C → ℝ`. -/
noncomputable def chartPD (q : C) :
    PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun x => coordE ((chartAt E1 q) x)
        invFun := fun s => (chartAt E1 q).symm (coordE.symm s)
        source := (chartAt E1 q).source
        target := coordE '' (chartAt E1 q).target
        map_source' := fun x hx => ⟨(chartAt E1 q) x,
          (chartAt E1 q).map_source hx, rfl⟩
        map_target' := by
          rintro s ⟨v, hv, rfl⟩
          show (chartAt E1 q).symm (coordE.symm (coordE v)) ∈ (chartAt E1 q).source
          rw [ContinuousLinearEquiv.symm_apply_apply]
          exact (chartAt E1 q).map_target hv
        left_inv' := by
          intro x hx
          show (chartAt E1 q).symm (coordE.symm (coordE ((chartAt E1 q) x))) = x
          rw [ContinuousLinearEquiv.symm_apply_apply]
          exact (chartAt E1 q).left_inv hx
        right_inv' := by
          rintro s ⟨v, hv, rfl⟩
          show coordE ((chartAt E1 q) ((chartAt E1 q).symm (coordE.symm (coordE v)))) = coordE v
          rw [ContinuousLinearEquiv.symm_apply_apply]
          rw [(chartAt E1 q).right_inv hv] }
    open_source := (chartAt E1 q).open_source
    open_target := coordE.toHomeomorph.isOpenMap _ (chartAt E1 q).open_target
    contMDiffOn_toFun := by
      refine (ContinuousLinearMap.contMDiff (coordE : E1 →L[ℝ] ℝ)).comp_contMDiffOn ?_
      exact contMDiffOn_chart
    contMDiffOn_invFun := by
      have h : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I1 sm
          (fun s : ℝ => coordE.symm s) (coordE '' (chartAt E1 q).target) :=
        (ContinuousLinearMap.contMDiff (coordE.symm : ℝ →L[ℝ] E1)).contMDiffOn
      refine (contMDiffOn_chart_symm (x := q)).comp h ?_
      rintro s ⟨v, hv, rfl⟩
      show coordE.symm (coordE v) ∈ (chartAt E1 q).target
      rwa [ContinuousLinearEquiv.symm_apply_apply] }

lemma chartPD_apply (q x : C) : chartPD q x = coordE ((chartAt E1 q) x) := rfl

/-- The chart at `q`, recentred so that it maps `q` to `0`. -/
noncomputable def chartPD0 (q : C) :
    PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun x => chartPD q x - chartPD q q
        invFun := fun s => (chartPD q).toPartialEquiv.invFun (s + chartPD q q)
        source := (chartPD q).source
        target := (fun v : ℝ => v - chartPD q q) '' (chartPD q).target
        map_source' := fun x hx => ⟨chartPD q x, (chartPD q).map_source hx, rfl⟩
        map_target' := by
          rintro s ⟨v, hv, rfl⟩
          show (chartPD q).toPartialEquiv.invFun (v - chartPD q q + chartPD q q) ∈ (chartPD q).source
          rw [sub_add_cancel]
          exact (chartPD q).map_target hv
        left_inv' := by
          intro x hx
          show (chartPD q).toPartialEquiv.invFun (chartPD q x - chartPD q q + chartPD q q) = x
          rw [sub_add_cancel]
          exact (chartPD q).left_inv hx
        right_inv' := by
          rintro s ⟨v, hv, rfl⟩
          show chartPD q ((chartPD q).toPartialEquiv.invFun (v - chartPD q q + chartPD q q))
            - chartPD q q = v - chartPD q q
          rw [sub_add_cancel]
          congr 1
          exact (chartPD q).right_inv hv }
    open_source := (chartPD q).open_source
    open_target := by
      have h2 : (fun v : ℝ => v - chartPD q q) = ⇑(Homeomorph.addRight (-(chartPD q q))) := by
        funext v; simp [sub_eq_add_neg]
      rw [h2]
      exact (Homeomorph.addRight (-(chartPD q q))).isOpenMap _ (chartPD q).open_target
    contMDiffOn_toFun := (chartPD q).contMDiffOn_toFun.sub contMDiffOn_const
    contMDiffOn_invFun := by
      refine (chartPD q).contMDiffOn_invFun.comp ?_ ?_
      · exact contMDiffOn_id.add contMDiffOn_const
      · rintro s ⟨v, hv, rfl⟩
        show v - chartPD q q + chartPD q q ∈ (chartPD q).target
        rwa [sub_add_cancel] }

lemma chartPD0_apply (q x : C) : chartPD0 q x = chartPD q x - chartPD q q := rfl
lemma chartPD0_self (q : C) : chartPD0 q q = 0 := sub_self _
lemma chartPD0_mem_source (q : C) : q ∈ (chartPD0 q).source := mem_chart_source E1 q

/-- The chart at `q`, recentred and reflected so that it maps `q` to `0`. -/
noncomputable def chartPD0neg (q : C) :
    PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm :=
  { toPartialEquiv :=
      { toFun := fun x => chartPD q q - chartPD q x
        invFun := fun s => (chartPD q).toPartialEquiv.invFun (chartPD q q - s)
        source := (chartPD q).source
        target := (fun v : ℝ => chartPD q q - v) '' (chartPD q).target
        map_source' := fun x hx => ⟨chartPD q x, (chartPD q).map_source hx, rfl⟩
        map_target' := by
          rintro s ⟨v, hv, rfl⟩
          show (chartPD q).toPartialEquiv.invFun (chartPD q q - (chartPD q q - v)) ∈ (chartPD q).source
          rw [sub_sub_cancel]
          exact (chartPD q).map_target hv
        left_inv' := by
          intro x hx
          show (chartPD q).toPartialEquiv.invFun (chartPD q q - (chartPD q q - chartPD q x)) = x
          rw [sub_sub_cancel]
          exact (chartPD q).left_inv hx
        right_inv' := by
          rintro s ⟨v, hv, rfl⟩
          show chartPD q q - chartPD q ((chartPD q).toPartialEquiv.invFun (chartPD q q - (chartPD q q - v)))
            = chartPD q q - v
          rw [sub_sub_cancel]
          congr 1
          exact (chartPD q).right_inv hv }
    open_source := (chartPD q).open_source
    open_target := by
      have h2 : (fun v : ℝ => chartPD q q - v) '' (chartPD q).target
          = (fun v : ℝ => chartPD q q - v) ⁻¹' (chartPD q).target := by
        ext w
        constructor
        · rintro ⟨v, hv, rfl⟩
          simpa using hv
        · intro hw
          exact ⟨chartPD q q - w, hw, by ring⟩
      rw [h2]
      exact (continuous_const.sub continuous_id).isOpen_preimage _ (chartPD q).open_target
    contMDiffOn_toFun := contMDiffOn_const.sub (chartPD q).contMDiffOn_toFun
    contMDiffOn_invFun := by
      refine (chartPD q).contMDiffOn_invFun.comp (contMDiffOn_const.sub contMDiffOn_id) ?_
      rintro s ⟨v, hv, rfl⟩
      show chartPD q q - (chartPD q q - v) ∈ (chartPD q).target
      rwa [sub_sub_cancel] }

lemma chartPD0neg_apply (q : C) : chartPD0neg q = fun x => chartPD q q - chartPD q x := rfl

lemma chartPD0neg_self (q : C) : chartPD0neg q q = 0 := by
  show chartPD q q - chartPD q q = 0
  ring

lemma chartPD0neg_mem_source (q : C) : q ∈ (chartPD0neg q).source := mem_chart_source E1 q



/-- Chart ball around `x` whose boundary is the (two point) sphere in the chart. -/
def cBall (x : C) (ρ : ℝ) : Set C :=
  (chartAt E1 x).source ∩ (chartAt E1 x) ⁻¹' Metric.ball ((chartAt E1 x) x) ρ

def cClosed (x : C) (ρ : ℝ) : Set C :=
  (chartAt E1 x).source ∩ (chartAt E1 x) ⁻¹' Metric.closedBall ((chartAt E1 x) x) ρ

private lemma coord_chartPD0 (x z : C) :
    ((chartAt E1 x) z - (chartAt E1 x) x) 0 = chartPD0 x z := by
  rw [← coordE_apply ((chartAt E1 x) z - (chartAt E1 x) x), map_sub,
    chartPD0_apply, chartPD_apply, chartPD_apply]

lemma mem_cBall_iff (x : C) (ρ : ℝ) (z : C) :
    z ∈ cBall x ρ ↔ z ∈ (chartAt E1 x).source ∧ |chartPD0 x z| < ρ := by
  simp only [cBall, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hzsrc, hzball⟩
    refine ⟨hzsrc, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0] at hzball
    exact hzball
  · rintro ⟨hzsrc, hzval⟩
    refine ⟨hzsrc, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0]
    exact hzval

lemma mem_cClosed_iff (x : C) (ρ : ℝ) (z : C) :
    z ∈ cClosed x ρ ↔ z ∈ (chartAt E1 x).source ∧ |chartPD0 x z| ≤ ρ := by
  simp only [cClosed, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hzsrc, hzball⟩
    refine ⟨hzsrc, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0] at hzball
    exact hzball
  · rintro ⟨hzsrc, hzval⟩
    refine ⟨hzsrc, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0]
    exact hzval

lemma isCompact_cClosed {x : C} {ρ : ℝ}
    (htgt : Metric.closedBall ((chartAt E1 x) x) ρ ⊆ (chartAt E1 x).target) :
    IsCompact (cClosed x ρ) := by
  have hEq : cClosed x ρ = (chartAt E1 x).symm '' Metric.closedBall ((chartAt E1 x) x) ρ :=
    ((chartAt E1 x).symm_image_eq_source_inter_preimage htgt).symm
  rw [hEq]
  exact (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt E1 x).symm.continuousOn_toFun.mono htgt)

lemma closure_cBall_subset [T2Space C] {x : C} {ρ : ℝ}
    (htgt : Metric.closedBall ((chartAt E1 x) x) ρ ⊆ (chartAt E1 x).target) :
    closure (cBall x ρ) ⊆ cClosed x ρ :=
  closure_minimal (Set.inter_subset_inter le_rfl (preimage_mono Metric.ball_subset_closedBall))
    (isCompact_cClosed htgt).isClosed

/-- The left end of an interval is a limit point of the image of the interval. -/
lemma mem_closure_image_Ioo_left {γ : ℝ → C} (hcont : Continuous γ) {a b : ℝ} (hab : a < b) :
    γ a ∈ closure (γ '' Set.Ioo a b) := by
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hcont.continuousAt.preimage_mem_nhds hW)
  set m : ℝ := min (ε/2) ((b-a)/2) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hmε : m < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmb : a + m < b := by
    have h : m ≤ (b-a)/2 := min_le_right _ _
    linarith
  exact ⟨γ (a + m),
    hεsub (by rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hm0]; exact hmε),
    a + m, ⟨by linarith, hmb⟩, rfl⟩

lemma mem_closure_image_Ioo_right {γ : ℝ → C} (hcont : Continuous γ) {a b : ℝ} (hab : a < b) :
    γ b ∈ closure (γ '' Set.Ioo a b) := by
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hcont.continuousAt.preimage_mem_nhds hW)
  set m : ℝ := min (ε/2) ((b-a)/2) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hmε : m < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hmb : a < b - m := by
    have h : m ≤ (b-a)/2 := min_le_right _ _
    linarith
  exact ⟨γ (b - m),
    hεsub (by rw [Metric.mem_ball, Real.dist_eq, show b - m - b = -m from by ring, abs_neg,
      abs_of_pos hm0]; exact hmε),
    b - m, ⟨hmb, by linarith⟩, rfl⟩

/-- **Crossing lemma.**  An injective curve has no bounded component of the preimage of a chart
ball: on such a component the chart coordinate is one-signed and must take the value `±ρ` at both
ends, contradicting injectivity. -/
lemma no_bounded_component [T2Space C] {x : C} {ρ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.closedBall ((chartAt E1 x) x) ρ ⊆ (chartAt E1 x).target)
    {γ : ℝ → C} (hcont : Continuous γ) (hinj : Function.Injective γ)
    (hneq : ∀ t, γ t ≠ x)
    {a b : ℝ} (hab : a < b)
    (hsub : ∀ t ∈ Set.Ioo a b, γ t ∈ cBall x ρ)
    (ha : γ a ∉ cBall x ρ) (hb : γ b ∉ cBall x ρ) : False := by
  have hcl := closure_cBall_subset htgt
  have hsub' : γ '' Set.Ioo a b ⊆ cBall x ρ := by
    rintro y ⟨t, ht, rfl⟩; exact hsub t ht
  have hKa : γ a ∈ cClosed x ρ := hcl (closure_mono hsub' (mem_closure_image_Ioo_left hcont hab))
  have hKb : γ b ∈ cClosed x ρ := hcl (closure_mono hsub' (mem_closure_image_Ioo_right hcont hab))
  obtain ⟨hasrc, haabs⟩ := (mem_cClosed_iff x ρ (γ a)).mp hKa
  obtain ⟨hbsrc, hbabs⟩ := (mem_cClosed_iff x ρ (γ b)).mp hKb
  have haabs : |chartPD0 x (γ a)| = ρ := by
    refine le_antisymm haabs ?_
    by_contra hcon
    rw [not_le] at hcon
    exact ha ((mem_cBall_iff x ρ (γ a)).mpr ⟨hasrc, hcon⟩)
  have hbabs : |chartPD0 x (γ b)| = ρ := by
    refine le_antisymm hbabs ?_
    by_contra hcon
    rw [not_le] at hcon
    exact hb ((mem_cBall_iff x ρ (γ b)).mpr ⟨hbsrc, hcon⟩)
  -- one-signedness
  have hcontOn : ContinuousOn (fun t => chartPD0 x (γ t)) (Set.Ioo a b) :=
    ((chartPD0 x).contMDiffOn_toFun.continuousOn).comp hcont.continuousOn
      (fun t ht => (hsub t ht).1)
  have hne : ∀ t ∈ Set.Ioo a b, chartPD0 x (γ t) ≠ 0 := by
    intro t ht h0
    have h1 : γ t ∈ (chartPD0 x).source := (hsub t ht).1
    exact hneq t ((chartPD0 x).toPartialEquiv.injOn h1 (chartPD0_mem_source x)
      (by rw [h0, chartPD0_self]))
  have hsign : (∀ t ∈ Set.Ioo a b, 0 < chartPD0 x (γ t)) ∨
      (∀ t ∈ Set.Ioo a b, chartPD0 x (γ t) < 0) := by
    have hsub0 : (fun t => chartPD0 x (γ t)) '' Set.Ioo a b ⊆ Set.Ioi (0:ℝ) ∪ Set.Iio 0 := by
      rintro z ⟨t, ht, rfl⟩
      rcases lt_or_gt_of_ne (hne t ht) with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases (isPreconnected_Ioo.image (fun t => chartPD0 x (γ t)) hcontOn).subset_or_subset
      isOpen_Ioi isOpen_Iio (Set.disjoint_left.mpr fun z h1 h2 => absurd h2 (not_lt.mpr h1.le))
      hsub0 with h | h
    · left; intro t ht; exact h ⟨t, ht, rfl⟩
    · right; intro t ht; exact h ⟨t, ht, rfl⟩
  -- limits at the two ends
  have hlima : Tendsto (fun t => chartPD0 x (γ t)) (𝓝[>] a) (𝓝 (chartPD0 x (γ a))) := by
    have hc : ContinuousAt (fun z : C => chartPD0 x z) (γ a) :=
      (chartPD0 x).contMDiffOn_toFun.continuousOn.continuousAt
        ((chartPD0 x).open_source.mem_nhds hasrc)
    exact (hc.tendsto.comp hcont.continuousAt).mono_left nhdsWithin_le_nhds
  have hlimb : Tendsto (fun t => chartPD0 x (γ t)) (𝓝[<] b) (𝓝 (chartPD0 x (γ b))) := by
    have hc : ContinuousAt (fun z : C => chartPD0 x z) (γ b) :=
      (chartPD0 x).contMDiffOn_toFun.continuousOn.continuousAt
        ((chartPD0 x).open_source.mem_nhds hbsrc)
    exact (hc.tendsto.comp hcont.continuousAt).mono_left nhdsWithin_le_nhds
  have hmem : Set.Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  have hmem' : Set.Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
  rcases hsign with hpos | hneg
  · have hpos' : ∀ t ∈ Set.Ioo a b, 0 ≤ chartPD0 x (γ t) := fun t ht => (hpos t ht).le
    have h1 : chartPD0 x (γ a) = ρ := by
      have hle : 0 ≤ chartPD0 x (γ a) := ge_of_tendsto hlima (Filter.mem_of_superset hmem hpos')
      rcases (abs_eq hρ.le).mp haabs with h | h
      · exact h
      · exact absurd (by rw [h] at hle; linarith) not_false
    have h2 : chartPD0 x (γ b) = ρ := by
      have hle : 0 ≤ chartPD0 x (γ b) :=
        ge_of_tendsto hlimb (Filter.mem_of_superset hmem' hpos')
      rcases (abs_eq hρ.le).mp hbabs with h | h
      · exact h
      · exact absurd (by rw [h] at hle; linarith) not_false
    exact absurd (hinj ((chartPD0 x).toPartialEquiv.injOn hasrc hbsrc (by rw [h1, h2])))
      (ne_of_lt hab)
  · have hneg' : ∀ t ∈ Set.Ioo a b, chartPD0 x (γ t) ≤ 0 := fun t ht => (hneg t ht).le
    have h1 : chartPD0 x (γ a) = -ρ := by
      have hle : chartPD0 x (γ a) ≤ 0 :=
        le_of_tendsto hlima (Filter.mem_of_superset hmem hneg')
      rcases (abs_eq hρ.le).mp haabs with h | h
      · exact absurd (by rw [h] at hle; linarith) not_false
      · exact h
    have h2 : chartPD0 x (γ b) = -ρ := by
      have hle : chartPD0 x (γ b) ≤ 0 :=
        le_of_tendsto hlimb (Filter.mem_of_superset hmem' hneg')
      rcases (abs_eq hρ.le).mp hbabs with h | h
      · exact absurd (by rw [h] at hle; linarith) not_false
      · exact h
    exact absurd (hinj ((chartPD0 x).toPartialEquiv.injOn hasrc hbsrc (by rw [h1, h2])))
      (ne_of_lt hab)

/-- **Chart data.**  For any neighbourhood `V` of `x` there is a radius `ρ > 0` such that the
coordinate interval `(-ρ,ρ)` lies in the target of the recentred chart at `x`, and the chart ball
of radius `ρ` is contained in `V`. -/
lemma exists_chart_ball (x : C) (V : Set C) (hV : V ∈ 𝓝 x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Set.Icc (-ρ) ρ ⊆ (chartPD0 x).target ∧ cBall x ρ ⊆ V ∧
      cClosed x ρ ⊆ V ∧
      Metric.closedBall ((chartAt E1 x) x) ρ ⊆ (chartAt E1 x).target := by
  have hxsrc : x ∈ (chartAt E1 x).source := mem_chart_source E1 x
  have hV' : V ∩ (chartAt E1 x).source ∈ 𝓝 x :=
    Filter.inter_mem hV ((chartAt E1 x).open_source.mem_nhds hxsrc)
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((chartAt E1 x).image_mem_nhds hxsrc hV')
  have h0tgt : (0:ℝ) ∈ (chartPD0 x).target := by
    rw [← chartPD0_self x]; exact (chartPD0 x).map_source (chartPD0_mem_source x)
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((chartPD0 x).open_target.mem_nhds h0tgt)
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Set.mem_Icc] at hz
    refine hρ₂sub ?_
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith [hz.1, min_le_right ρ₁ ρ₂], by linarith [hz.2, min_le_right ρ₁ ρ₂]⟩
  · intro z hz
    obtain ⟨hzsrc, hzval⟩ := (mem_cBall_iff x _ z).mp hz
    have h2 : (chartAt E1 x) z ∈ Metric.closedBall ((chartAt E1 x) x) (min ρ₁ ρ₂) := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0]
      exact le_of_lt hzval
    obtain ⟨w, hw, hwz⟩ := hρ₁sub (Metric.closedBall_subset_closedBall (min_le_left ρ₁ ρ₂) h2)
    rw [Set.mem_inter_iff] at hw
    have hw_eq : w = z := by
      rw [← (chartAt E1 x).left_inv hzsrc, ← hwz, (chartAt E1 x).left_inv hw.2]
    rw [hw_eq] at hw
    exact hw.1
  · intro z hz
    obtain ⟨hzsrc, hzval⟩ := (mem_cClosed_iff x _ z).mp hz
    have h2 : (chartAt E1 x) z ∈ Metric.closedBall ((chartAt E1 x) x) ρ₁ := by
      rw [Metric.mem_closedBall, dist_eq_norm, norm_eq_abs_coord, coord_chartPD0]
      exact le_trans hzval (min_le_left ρ₁ ρ₂)
    obtain ⟨w, hw, hwz⟩ := hρ₁sub h2
    rw [Set.mem_inter_iff] at hw
    have hw_eq : w = z := by
      rw [← (chartAt E1 x).left_inv hzsrc, ← hwz, (chartAt E1 x).left_inv hw.2]
    rw [hw_eq] at hw
    exact hw.1
  · intro z hz
    exact hρ₁sub.trans (by rintro y ⟨w, hw, rfl⟩; exact (chartAt E1 x).map_source hw.2)
      (Metric.closedBall_subset_closedBall (min_le_left ρ₁ ρ₂) hz)

/-- The contrapositive of `Work.OneDim.extend_arc`, in the form used below. -/
theorem extend_contra {A : Set C} (hA : IsOpenArc A)
    (hAmax : ∀ B : Set C, IsOpenArc B → A ⊆ B → B ⊆ A)
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ)
    (hrange : Set.range γ = A)
    {q : C} (hq : q ∉ Set.range γ) (hconv : Filter.Tendsto γ Filter.atTop (nhds q))
    (φ : PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm)
    (hqsrc : q ∈ φ.source) (hq0 : φ q = 0) {δ : ℝ} (hδ : 0 < δ)
    (htgt : Set.Ioo (-δ) δ ⊆ φ.target)
    (hpos : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ φ.source ∧ 0 < φ (γ t) ∧ φ (γ t) < δ)
    (hfree : ∀ t : ℝ, γ t ∈ φ.source → φ (γ t) ∈ Set.Ioo (-δ) δ → 0 ≤ φ (γ t)) : False := by
  obtain ⟨A', hA', hsub, hnotsub⟩ :=
    extend_arc hinj hld hq hconv φ hqsrc hq0 hδ htgt hpos hfree
  have hsub' : A ⊆ A' := by rw [← hrange]; exact hsub
  exact hnotsub (by rw [hrange]; exact hAmax A' hA' hsub')

/-- Every point of the frontier of an open arc is a cluster point of the parametrisation at `+∞` or
at `-∞`. -/
lemma frontier_subset_cluster [T2Space C] {A : Set C} (hAopen : IsOpen A)
    {γ : ℝ → C} (hcont : Continuous γ) (hrange : Set.range γ = A) {x : C}
    (hx : x ∈ frontier A) :
    ClusterPt x (Filter.map γ Filter.atTop) ∨ ClusterPt x (Filter.map γ Filter.atBot) := by
  have hxA : x ∉ A := by
    have h := hx.2
    rwa [hAopen.interior_eq] at h
  have hxcl : x ∈ closure (Set.range γ) := by rw [hrange]; exact hx.1
  by_contra hcon
  have htopeq : 𝓝 x ⊓ Filter.map γ Filter.atTop = ⊥ := by
    have h : ¬ ClusterPt x (Filter.map γ Filter.atTop) := fun hc => hcon (Or.inl hc)
    rw [ClusterPt, Filter.not_neBot] at h
    exact h
  have hboteq : 𝓝 x ⊓ Filter.map γ Filter.atBot = ⊥ := by
    have h : ¬ ClusterPt x (Filter.map γ Filter.atBot) := fun hc => hcon (Or.inr hc)
    rw [ClusterPt, Filter.not_neBot] at h
    exact h
  obtain ⟨V₁, hV₁, T₁, hT₁⟩ : ∃ V₁ ∈ 𝓝 x, ∃ T₁, ∀ t ≥ T₁, γ t ∉ V₁ := by
    have hmem : (∅ : Set C) ∈ 𝓝 x ⊓ Filter.map γ Filter.atTop := by
      rw [htopeq]; exact Filter.mem_bot
    rw [Filter.mem_inf_iff] at hmem
    obtain ⟨V, hV, s, hs, heq⟩ := hmem
    rw [Filter.mem_map, Filter.mem_atTop_sets] at hs
    obtain ⟨T, hT⟩ := hs
    refine ⟨V, hV, T, fun t ht hvt => ?_⟩
    have hz : γ t ∈ V ∩ s := ⟨hvt, hT t ht⟩
    rw [← heq] at hz
    exact absurd hz (by simp)
  obtain ⟨V₂, hV₂, T₂, hT₂⟩ : ∃ V₂ ∈ 𝓝 x, ∃ T₂, ∀ t ≤ T₂, γ t ∉ V₂ := by
    have hmem : (∅ : Set C) ∈ 𝓝 x ⊓ Filter.map γ Filter.atBot := by
      rw [hboteq]; exact Filter.mem_bot
    rw [Filter.mem_inf_iff] at hmem
    obtain ⟨V, hV, s, hs, heq⟩ := hmem
    rw [Filter.mem_map, Filter.mem_atBot_sets] at hs
    obtain ⟨T, hT⟩ := hs
    refine ⟨V, hV, T, fun t ht hvt => ?_⟩
    have hz : γ t ∈ V ∩ s := ⟨hvt, hT t ht⟩
    rw [← heq] at hz
    exact absurd hz (by simp)
  obtain ⟨t₀, ht₀⟩ : ∃ t, γ t ∈ V₁ ∩ V₂ := by
    rw [mem_closure_iff_nhds] at hxcl
    obtain ⟨y, hyW, hyr⟩ := hxcl (V₁ ∩ V₂) (Filter.inter_mem hV₁ hV₂)
    obtain ⟨t, ht⟩ := hyr
    exact ⟨t, ht ▸ hyW⟩
  have ht₁ : ¬ (t₀ ≥ T₁) := fun h => hT₁ t₀ h ht₀.1
  have ht₂ : ¬ (t₀ ≤ T₂) := fun h => hT₂ t₀ h ht₀.2
  push_neg at ht₁ ht₂
  have hlt : T₂ < T₁ := by linarith
  have hcl2 : x ∈ closure (γ '' Set.Icc T₂ T₁) := by
    rw [mem_closure_iff_nhds]
    intro W hW
    rw [mem_closure_iff_nhds] at hxcl
    obtain ⟨y, hyW, hyr⟩ := hxcl (W ∩ (V₁ ∩ V₂))
      (Filter.inter_mem hW (Filter.inter_mem hV₁ hV₂))
    obtain ⟨t, ht⟩ := hyr
    refine ⟨γ t, ht ▸ hyW.1, t, ⟨?_, ?_⟩, rfl⟩
    · exact le_of_lt (not_le.mp (fun h => hT₂ t h (ht ▸ hyW.2.2)))
    · exact le_of_lt (not_le.mp (fun h => hT₁ t h (ht ▸ hyW.2.1)))
  have hcomp : IsCompact (γ '' Set.Icc T₂ T₁) := isCompact_Icc.image hcont
  obtain ⟨t, htmem, htq⟩ := hcomp.isClosed.closure_subset hcl2
  have : x ∈ Set.range γ := ⟨t, htq⟩
  rw [hrange] at this
  exact hxA this

/-- The chart ball, described by the recentred coordinate `chartPD0`. -/
lemma cBall_iff_chartPD0 (q : C) (ρ : ℝ) (z : C) :
    z ∈ cBall q ρ ↔ z ∈ (chartPD0 q).source ∧ chartPD0 q z ∈ Set.Ioo (-ρ) ρ := by
  rw [mem_cBall_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, abs_lt.mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, abs_lt.mpr h2⟩

/-- The chart ball, described by the reflected recentred coordinate `chartPD0neg`. -/
lemma cBall_iff_chartPD0neg (q : C) (ρ : ℝ) (z : C) :
    z ∈ cBall q ρ ↔ z ∈ (chartPD0neg q).source ∧ chartPD0neg q z ∈ Set.Ioo (-ρ) ρ := by
  rw [mem_cBall_iff]
  have hneg : chartPD0neg q z = -(chartPD0 q z) := by
    show chartPD q q - chartPD q z = -(chartPD q z - chartPD q q)
    ring
  have hiff : -(chartPD0 q z) ∈ Set.Ioo (-ρ) ρ ↔ |chartPD0 q z| < ρ := by
    rw [Set.mem_Ioo, abs_lt]
    exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
      fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  rw [hneg, hiff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A curve which converges to a point along `atBot` does not attain that point. -/
lemma not_mem_range_of_tendsto_atBot {γ : ℝ → C}
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ)
    (hinj : Function.Injective γ) {x : C}
    (hx : Filter.Tendsto γ Filter.atBot (𝓝 x)) : x ∉ Set.range γ := by
  rintro ⟨t₀, rfl⟩
  set ρ := (hld t₀).localInverse with hρ
  have hsrc : γ t₀ ∈ ρ.source := (hld t₀).localInverse_mem_source
  have hcont : ContinuousAt (fun z : C => ρ z) (γ t₀) :=
    ρ.contMDiffOn_toFun.continuousOn.continuousAt (ρ.open_source.mem_nhds hsrc)
  have hev : ∀ᶠ t in Filter.atBot, ρ (γ t) = t := by
    filter_upwards [hx.eventually (ρ.open_source.mem_nhds hsrc)] with t ht
    have h2 : γ (ρ (γ t)) = γ t := (hld t₀).localInverse_right_inv ht
    exact hinj h2
  have h3 : Filter.Tendsto (fun t : ℝ => ρ (γ t)) Filter.atBot (𝓝 (ρ (γ t₀))) :=
    hcont.tendsto.comp hx
  rw [Filter.tendsto_congr' hev] at h3
  obtain ⟨t, ht1, ht2⟩ := ((h3.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1))).and
    (eventually_lt_atBot (ρ (γ t₀) - 1))).exists
  simp only [Real.dist_eq, abs_lt] at ht1
  linarith [ht1.1, ht2]

/-- An open subset of `ℝ` which is bounded below and has no "bounded component" (in the sense of
the hypothesis `hnbc`) is a half line. -/
theorem eq_Ioi_of_no_bounded_component {S : Set ℝ} (hopen : IsOpen S) (hne : S.Nonempty)
    (hbdd : BddBelow S)
    (hnbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S → a ∉ S → b ∉ S → False) :
    ∃ u : ℝ, S = Set.Ioi u := by
  refine ⟨sInf S, ?_⟩
  ext t
  constructor
  · intro ht
    have h1 : sInf S ≤ t := csInf_le hbdd ht
    refine lt_of_le_of_ne h1 ?_
    intro hEq
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds (hEq ▸ ht))
    have h2 : t - ε/2 ∈ S := hεsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩)
    have h3 : sInf S ≤ t - ε/2 := csInf_le hbdd h2
    linarith
  · intro ht
    by_contra htS
    obtain ⟨s, hsS, hst⟩ := exists_lt_of_csInf_lt hne ht
    set B : Set ℝ := {w : ℝ | Set.Ioo s w ⊆ S} with hB
    have hsB : s ∈ B := by
      rw [hB]
      intro y hy
      exact absurd hy.1 (not_lt.mpr hy.2.le)
    have hBup : BddAbove B := by
      refine ⟨t, fun w hw => ?_⟩
      by_contra hcon
      push_neg at hcon
      exact htS (hw ⟨hst, hcon⟩)
    set lam : ℝ := sSup B with hlam
    have hslt : s < lam := by
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hsS)
      have hmem : s + ε/2 ∈ B := by
        rw [hB]
        rintro y ⟨hy1, hy2⟩
        exact hεsub (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith, by linarith⟩)
      have := le_csSup hBup hmem
      linarith
    have hsub : Set.Ioo s lam ⊆ S := by
      rintro y ⟨hy1, hy2⟩
      obtain ⟨w, hwB, hyw⟩ := exists_lt_of_lt_csSup ⟨s, hsB⟩ hy2
      exact hwB ⟨hy1, hyw⟩
    have hlamS : lam ∉ S := by
      intro hlin
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hlin)
      have hmem : lam + ε ∈ B := by
        rw [hB]
        rintro y ⟨hy1, hy2⟩
        rcases lt_or_ge y lam with h | h
        · exact hsub ⟨hy1, h⟩
        · exact hεsub (by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith, by linarith⟩)
      have : lam + ε ≤ lam := le_csSup hBup hmem
      linarith
    set C : Set ℝ := {w : ℝ | Set.Ioo w lam ⊆ S} with hC
    have hsC : s ∈ C := by rw [hC]; exact hsub
    have hCbdd : BddBelow C := by
      by_contra hcon
      obtain ⟨w, hwC, hwlow⟩ := not_bddBelow_iff.mp hcon (sInf S)
      have hmid : (w + sInf S)/2 < lam := by
        have h1 : sInf S ≤ s := csInf_le hbdd hsS
        linarith
      have hwmid : w < (w + sInf S)/2 := by linarith
      have : (w + sInf S)/2 ∈ S := hwC ⟨hwmid, hmid⟩
      have h4 : sInf S ≤ (w + sInf S)/2 := csInf_le hbdd this
      linarith
    set a : ℝ := sInf C with ha
    have hasub : Set.Ioo a lam ⊆ S := by
      rintro y ⟨hy1, hy2⟩
      obtain ⟨w, hwC, hwy⟩ := exists_lt_of_csInf_lt ⟨s, hsC⟩ hy1
      exact hwC ⟨hwy, hy2⟩
    have haS : a ∉ S := by
      intro hain
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hain)
      have hmem : a - ε ∈ C := by
        rw [hC]
        rintro y ⟨hy1, hy2⟩
        rcases lt_or_ge y a with h | h
        · exact hεsub (by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith, by linarith⟩)
        · rcases lt_or_eq_of_le h with h2 | h2
          · exact hasub ⟨h2, hy2⟩
          · rw [← h2]; exact hain
      have : a ≤ a - ε := csInf_le hCbdd hmem
      linarith
    have halt : a < lam := by
      have h1 : a ≤ s := csInf_le hCbdd hsC
      linarith
    exact hnbc a lam halt hasub haS hlamS

/-- The mirror image of `eq_Ioi_of_no_bounded_component`. -/
theorem eq_Iio_of_no_bounded_component {S : Set ℝ} (hopen : IsOpen S) (hne : S.Nonempty)
    (hbdd : BddAbove S)
    (hnbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S → a ∉ S → b ∉ S → False) :
    ∃ v : ℝ, S = Set.Iio v := by
  have hS'open : IsOpen (Neg.neg ⁻¹' S) := continuous_neg.isOpen_preimage _ hopen
  have hS'ne : (Neg.neg ⁻¹' S).Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨-s, by simpa using hs⟩
  have hS'bdd : BddBelow (Neg.neg ⁻¹' S) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hbdd
    refine ⟨-c, ?_⟩
    intro y hy
    have hy' : -y ∈ S := hy
    have h1 : -y ≤ c := hc (-y) hy'
    linarith
  have hS'nbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ Neg.neg ⁻¹' S →
      a ∉ Neg.neg ⁻¹' S → b ∉ Neg.neg ⁻¹' S → False := by
    intro a b hab hsub ha hb
    have h1 : Set.Ioo (-b) (-a) ⊆ S := by
      rintro y ⟨hy1, hy2⟩
      have hy : -y ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
      simpa using hsub hy
    have h2 : (-a) ∉ S := fun h => ha (by simpa using h)
    have h3 : (-b) ∉ S := fun h => hb (by simpa using h)
    exact hnbc (-b) (-a) (by linarith) h1 h3 h2
  obtain ⟨u, hu⟩ := eq_Ioi_of_no_bounded_component hS'open hS'ne hS'bdd hS'nbc
  refine ⟨-u, ?_⟩
  ext x
  have hx : x ∈ S ↔ -x ∈ Neg.neg ⁻¹' S := by simp
  rw [hx, hu, Set.mem_Ioi, Set.mem_Iio]
  constructor <;> intro h <;> linarith

/-- An open subset of `ℝ` which is unbounded above and has no bounded component consists of at most
two half lines. -/
theorem structure_of_no_bounded_component {S : Set ℝ} (hopen : IsOpen S)
    (hnbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S → a ∉ S → b ∉ S → False)
    (hup : ∃ T : ℝ, ∀ t ≥ T, t ∈ S) :
    S = Set.univ ∨ (∃ u : ℝ, S = Set.Ioi u) ∨
      (∃ v u : ℝ, v ≤ u ∧ S = Set.Iio v ∪ Set.Ioi u) := by
  by_cases huniv : S = Set.univ
  · exact Or.inl huniv
  obtain ⟨a₀, ha₀⟩ : ∃ a : ℝ, a ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact huniv (Set.eq_univ_iff_forall.mpr hcon)
  set A : Set ℝ := {w : ℝ | ∀ y : ℝ, w < y → y ∈ S} with hA
  obtain ⟨T, hT⟩ := hup
  have hAne : A.Nonempty := ⟨T, fun y hy => hT y hy.le⟩
  have hAbdd : BddBelow A := by
    refine ⟨a₀, fun w hw => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact ha₀ (hw a₀ hcon)
  set u : ℝ := sInf A with hu
  have husub : Set.Ioi u ⊆ S := by
    intro y hy
    obtain ⟨w, hwA, hwy⟩ := exists_lt_of_csInf_lt hAne hy
    exact hwA y hwy
  have huS : u ∉ S := by
    intro huS'
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds huS')
    have hmem : u - ε ∈ A := by
      intro y hy
      rcases lt_or_ge y u with h | h
      · exact hεsub (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith, by linarith⟩)
      · rcases lt_or_eq_of_le h with h2 | h2
        · exact husub h2
        · rw [← h2]; exact huS'
    have : u ≤ u - ε := csInf_le hAbdd hmem
    linarith
  by_cases hlow : (S ∩ Set.Iio u).Nonempty
  · right; right
    have hS'open : IsOpen (S ∩ Set.Iio u) := hopen.inter isOpen_Iio
    have hS'bdd : BddAbove (S ∩ Set.Iio u) := ⟨u, fun w hw => hw.2.le⟩
    have hS'nbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S ∩ Set.Iio u →
        a ∉ S ∩ Set.Iio u → b ∉ S ∩ Set.Iio u → False := by
      intro a b hab hsub ha hb
      have hbu : b ≤ u := by
        by_contra hcon
        push_neg at hcon
        have hy : (max a u + b)/2 ∈ Set.Ioo a b :=
          ⟨by linarith [le_max_left a u], by linarith [max_lt hab hcon]⟩
        have hmem := hsub hy
        obtain ⟨-, hlt⟩ := hmem
        have hlt' : (max a u + b)/2 < u := hlt
        have hgt : u < (max a u + b)/2 := by linarith [le_max_right a u]
        linarith
      have hbS : b ∉ S := by
        rcases lt_or_eq_of_le hbu with h | h
        · exact fun hbs => hb ⟨hbs, h⟩
        · rw [h]; exact huS
      have haS : a ∉ S := by
        have hau : a < u := lt_of_lt_of_le hab hbu
        exact fun has => ha ⟨has, hau⟩
      exact hnbc a b hab (fun y hy => (hsub hy).1) haS hbS
    obtain ⟨v, hv⟩ := eq_Iio_of_no_bounded_component hS'open hlow hS'bdd hS'nbc
    have hvu : v ≤ u := by
      by_contra hcon
      push_neg at hcon
      have : u ∈ S ∩ Set.Iio u := by rw [hv]; exact hcon
      exact huS this.1
    refine ⟨v, u, hvu, ?_⟩
    ext t
    constructor
    · intro ht
      rcases lt_trichotomy t u with h | h | h
      · exact Or.inl (by rw [← hv]; exact ⟨ht, h⟩)
      · exact absurd (h ▸ ht) huS
      · exact Or.inr h
    · rintro (h | h)
      · exact (hv.symm ▸ h).1
      · exact husub h
  · right; left
    have hlow' : ∀ x : ℝ, x ∉ S ∩ Set.Iio u := fun x hx => hlow ⟨x, hx⟩
    refine ⟨u, ?_⟩
    ext t
    constructor
    · intro ht
      rcases lt_trichotomy t u with h | h | h
      · exact absurd ⟨ht, h⟩ (hlow' t)
      · exact absurd (h ▸ ht) huS
      · exact h
    · intro ht; exact husub ht

lemma isOpen_cBall (x : C) (ρ : ℝ) : IsOpen (cBall x ρ) :=
  (chartAt E1 x).isOpen_inter_preimage Metric.isOpen_ball

lemma cBall_subset_cClosed (x : C) (ρ : ℝ) : cBall x ρ ⊆ cClosed x ρ :=
  Set.inter_subset_inter le_rfl (preimage_mono Metric.ball_subset_closedBall)

/-- The reflected chart has the same symmetric intervals in its target. -/
lemma Ioo_subset_chartPD0neg_target {x : C} {δ : ℝ}
    (h : Set.Ioo (-δ) δ ⊆ (chartPD0 x).target) :
    Set.Ioo (-δ) δ ⊆ (chartPD0neg x).target := by
  intro v hv
  have hv' : -v ∈ Set.Ioo (-δ) δ := ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hmem : -v ∈ (fun u : ℝ => u - chartPD x x) '' (chartPD x).target := h hv'
  obtain ⟨u, hu, hueq⟩ := hmem
  refine ⟨u, hu, ?_⟩
  show chartPD x x - u = v
  linarith

/-- Convergence at `+∞` from the "frequently in every neighbourhood" hypothesis. -/
lemma tendsto_atTop_of_frequently [T2Space C] [SecondCountableTopology C] {γ : ℝ → C}
    (hcont : Continuous γ) (hinj : Function.Injective γ) {x : C}
    (hx : ∀ U : Set C, IsOpen U → x ∈ U →
      Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atTop) :
    Filter.Tendsto γ Filter.atTop (nhds x) :=
  end_behavior_injective hcont hinj hx

/-- Convergence at `-∞` from the "frequently in every neighbourhood" hypothesis. -/
lemma tendsto_atBot_of_frequently [T2Space C] [SecondCountableTopology C] {γ : ℝ → C}
    (hcont : Continuous γ) (hinj : Function.Injective γ) {x : C}
    (hx : ∀ U : Set C, IsOpen U → x ∈ U →
      Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atBot) :
    Filter.Tendsto γ Filter.atBot (nhds x) := by
  have hfreq : ∀ U : Set C, IsOpen U → x ∈ U →
      Filter.Frequently (fun s : ℝ => γ (-s) ∈ U) Filter.atTop := by
    intro U hUo hxU
    have h1 : ∃ᶠ t in Filter.atBot, γ t ∈ U := hx U hUo hxU
    rw [Filter.frequently_atBot] at h1
    rw [Filter.frequently_atTop]
    intro T
    obtain ⟨t, ht, hmem⟩ := h1 (-T)
    exact ⟨-t, by linarith, by simpa using hmem⟩
  have h3 := end_behavior_injective (hcont.comp continuous_neg)
    (fun a b hab => by simpa using hinj hab) hfreq
  have h3' : Filter.Tendsto γ (Filter.map (fun a : ℝ => -a) Filter.atTop) (nhds x) := h3
  rw [Filter.map_neg_atTop] at h3'
  exact h3'

/-- If a continuous nowhere vanishing function is positive at one point of a preconnected set,
it is positive everywhere on it. -/
lemma pos_of_preconnected {f : ℝ → ℝ} {K : Set ℝ} (hK : IsPreconnected K)
    (hcont : ContinuousOn f K) (hne : ∀ t ∈ K, f t ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ K) (hpos : 0 < f t₀) : ∀ t ∈ K, 0 < f t := by
  have hsub0 : f '' K ⊆ Set.Ioi (0:ℝ) ∪ Set.Iio 0 := by
    rintro z ⟨t, ht, rfl⟩
    rcases lt_or_gt_of_ne (hne t ht) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases (hK.image f hcont).subset_or_subset isOpen_Ioi isOpen_Iio
    (Set.disjoint_left.mpr fun z h1 h2 => absurd h2 (not_lt.mpr h1.le)) hsub0 with h | h
  · intro t ht; exact h ⟨t, ht, rfl⟩
  · exact absurd (h ⟨t₀, ht₀, rfl⟩) (not_lt.mpr hpos.le)

/-- If a continuous nowhere vanishing function is negative at one point of a preconnected set,
it is negative everywhere on it. -/
lemma neg_of_preconnected {f : ℝ → ℝ} {K : Set ℝ} (hK : IsPreconnected K)
    (hcont : ContinuousOn f K) (hne : ∀ t ∈ K, f t ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ K) (hneg : f t₀ < 0) : ∀ t ∈ K, f t < 0 := by
  have hsub0 : f '' K ⊆ Set.Ioi (0:ℝ) ∪ Set.Iio 0 := by
    rintro z ⟨t, ht, rfl⟩
    rcases lt_or_gt_of_ne (hne t ht) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases (hK.image f hcont).subset_or_subset isOpen_Ioi isOpen_Iio
    (Set.disjoint_left.mpr fun z h1 h2 => absurd h2 (not_lt.mpr h1.le)) hsub0 with h | h
  · exact absurd (h ⟨t₀, ht₀, rfl⟩) (not_lt.mpr hneg.le)
  · intro t ht; exact h ⟨t, ht, rfl⟩

/-- The unique cluster point at `+∞` of an injective continuous curve is its limit. -/
lemma tendsto_atTop_of_clusterPt [T2Space C] [SecondCountableTopology C]
    {γ : ℝ → C} (hcont : Continuous γ)
    (hinj : Function.Injective γ) {x : C}
    (hx : ClusterPt x (Filter.map γ Filter.atTop)) :
    Filter.Tendsto γ Filter.atTop (nhds x) := by
  refine end_behavior_injective hcont hinj ?_
  intro U hUo hxU
  have h1 : ∃ᶠ u in Filter.map γ Filter.atTop, u ∈ U := hx.frequently (hUo.mem_nhds hxU)
  rwa [Filter.frequently_map] at h1

/-- The unique cluster point at `-∞` of an injective continuous curve is its limit. -/
lemma tendsto_atBot_of_clusterPt [T2Space C] [SecondCountableTopology C]
    {γ : ℝ → C} (hcont : Continuous γ)
    (hinj : Function.Injective γ) {x : C}
    (hx : ClusterPt x (Filter.map γ Filter.atBot)) :
    Filter.Tendsto γ Filter.atBot (nhds x) := by
  have hfreq : ∀ U : Set C, IsOpen U → x ∈ U →
      Filter.Frequently (fun s : ℝ => γ (-s) ∈ U) Filter.atTop := by
    intro U hUo hxU
    have h1 : ∃ᶠ t in Filter.atBot, γ t ∈ U := by
      have h2 : ∃ᶠ u in Filter.map γ Filter.atBot, u ∈ U := hx.frequently (hUo.mem_nhds hxU)
      rwa [Filter.frequently_map] at h2
    rw [Filter.frequently_atBot] at h1
    rw [Filter.frequently_atTop]
    intro T
    obtain ⟨t, ht, hmem⟩ := h1 (-T)
    exact ⟨-t, by linarith, by simpa using hmem⟩
  have h3 := end_behavior_injective (hcont.comp continuous_neg)
    (fun a b hab => by simpa using hinj hab) hfreq
  have h3' : Filter.Tendsto γ (Filter.map (fun a : ℝ => -a) Filter.atTop) (nhds x) := h3
  rw [Filter.map_neg_atTop] at h3'
  exact h3'

lemma mem_closure_image_Ioi {γ : ℝ → C} (hcont : Continuous γ) {a : ℝ} :
    γ a ∈ closure (γ '' Set.Ioi a) :=
  closure_mono (Set.image_mono Set.Ioo_subset_Ioi_self)
    (mem_closure_image_Ioo_left hcont (by linarith : a < a + 1))

lemma mem_closure_image_Iio {γ : ℝ → C} (hcont : Continuous γ) {a : ℝ} :
    γ a ∈ closure (γ '' Set.Iio a) :=
  closure_mono (Set.image_mono Set.Ioo_subset_Iio_self)
    (mem_closure_image_Ioo_right hcont (by linarith : a - 1 < a))

/-- **The frontier of a maximal open arc is a single point.** -/
theorem frontier_subsingleton [T2Space C] [SecondCountableTopology C]
    {A : Set C} (hA : IsOpenArc A)
    (hAmax : ∀ B : Set C, IsOpenArc B → A ⊆ B → B ⊆ A)
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ)
    (hrange : Set.range γ = A) (hU : A ≠ Set.univ) :
    (frontier A).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hγcont : Continuous γ := hld.contMDiff.continuous
  have hAopen : IsOpen A := hA.isOpen
  have hnotmem : ∀ z ∈ frontier A, z ∉ A := by
    intro z hz
    have h := hz.2
    rwa [hAopen.interior_eq] at h
  have hxA : x ∉ A := hnotmem x hx
  have hyA : y ∉ A := hnotmem y hy
  have hxc := frontier_subset_cluster hAopen hγcont hrange hx
  have hyc := frontier_subset_cluster hAopen hγcont hrange hy
  have convtop : ∀ z : C, ClusterPt z (Filter.map γ Filter.atTop) →
      Filter.Tendsto γ Filter.atTop (nhds z) := by
    intro z hz
    refine end_behavior_injective hγcont hinj ?_
    intro U hUo hzU
    have h1 : ∃ᶠ u in Filter.map γ Filter.atTop, u ∈ U := hz.frequently (hUo.mem_nhds hzU)
    rwa [Filter.frequently_map] at h1
  have convbot : ∀ z : C, ClusterPt z (Filter.map γ Filter.atBot) →
      Filter.Tendsto γ Filter.atBot (nhds z) := by
    intro z hz
    have hfreq : ∀ U : Set C, IsOpen U → z ∈ U →
        Filter.Frequently (fun s : ℝ => γ (-s) ∈ U) Filter.atTop := by
      intro U hUo hzU
      have h1 : ∃ᶠ t in Filter.atBot, γ t ∈ U := by
        have h2 : ∃ᶠ u in Filter.map γ Filter.atBot, u ∈ U := hz.frequently (hUo.mem_nhds hzU)
        rwa [Filter.frequently_map] at h2
      rw [Filter.frequently_atBot] at h1
      rw [Filter.frequently_atTop]
      intro T
      obtain ⟨t, ht, hmem⟩ := h1 (-T)
      exact ⟨-t, by linarith, by simpa using hmem⟩
    have h3 := end_behavior_injective (hγcont.comp continuous_neg)
      (fun a b hab => by simpa using hinj hab) hfreq
    have h3' : Filter.Tendsto γ (Filter.map (fun a : ℝ => -a) Filter.atTop) (nhds z) := h3
    rw [Filter.map_neg_atTop] at h3'
    exact h3'
  have main : ∀ p r : C, p ∈ frontier A → r ∈ frontier A → p ≠ r →
      ClusterPt p (Filter.map γ Filter.atTop) → ClusterPt r (Filter.map γ Filter.atBot) →
      False := by
    intro p r hp hr hpr hppos hrneg
    have hpA : p ∉ A := hnotmem p hp
    have hpne : ∀ t, γ t ≠ p := fun t ht => hpA (by rw [← hrange]; exact ⟨t, ht⟩)
    have hpnot : p ∉ Set.range γ := fun h => by
      obtain ⟨t, ht⟩ := Set.mem_range.mp h
      exact hpne t ht
    have hconvp : Filter.Tendsto γ Filter.atTop (nhds p) := convtop p hppos
    have hconvr : Filter.Tendsto γ Filter.atBot (nhds r) := convbot r hrneg
    have hV : ({r}ᶜ : Set C) ∈ 𝓝 p :=
      isOpen_compl_singleton.mem_nhds (by simpa using hpr)
    obtain ⟨δ, hδ, hIcc, hball, hclosedV, hclosed⟩ := exists_chart_ball p {r}ᶜ hV
    have hpball : p ∈ cBall p δ :=
      (mem_cBall_iff p δ p).mpr ⟨mem_chart_source E1 p, by rw [chartPD0_self]; simpa using hδ⟩
    have htail : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ cBall p δ :=
      Filter.eventually_atTop.mp (hconvp.eventually ((isOpen_cBall p δ).mem_nhds hpball))
    have hrclosed : r ∉ cClosed p δ := fun hmem => (hclosedV hmem) rfl
    have hfar : ∃ T : ℝ, ∀ t ≤ T, γ t ∉ cBall p δ := by
      have hmem : (cClosed p δ)ᶜ ∈ 𝓝 r :=
        ((isCompact_cClosed hclosed).isClosed.isOpen_compl).mem_nhds (by simpa using hrclosed)
      have h1 : ∀ᶠ t in Filter.atBot, γ t ∈ (cClosed p δ)ᶜ := hconvr.eventually hmem
      rw [Filter.eventually_atBot] at h1
      obtain ⟨T, hT⟩ := h1
      exact ⟨T, fun t ht htc => hT t ht (cBall_subset_cClosed p δ htc)⟩
    set S : Set ℝ := γ ⁻¹' cBall p δ with hSdef
    obtain ⟨T₁, hT₁⟩ := htail
    obtain ⟨T₂, hT₂⟩ := hfar
    have hSopen : IsOpen S := (isOpen_cBall p δ).preimage hγcont
    have hSne : S.Nonempty := ⟨max T₁ T₂ + 1, by
      rw [hSdef]
      exact hT₁ _ (le_trans (le_max_left _ _) (by linarith))⟩
    have hSbdd : BddBelow S := ⟨T₂, fun t ht => by
      by_contra hcon
      push_neg at hcon
      exact hT₂ t hcon.le (by rwa [hSdef] at ht)⟩
    have hnbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S → a ∉ S → b ∉ S → False := by
      intro a b hab hsub ha hb
      refine no_bounded_component hδ hclosed hγcont hinj hpne hab ?_ ?_ ?_
      · intro t ht
        have := hsub ht
        rwa [hSdef] at this
      · rwa [hSdef] at ha
      · rwa [hSdef] at hb
    obtain ⟨u, hSu⟩ := eq_Ioi_of_no_bounded_component hSopen hSne hSbdd hnbc
    have hSconn : IsPreconnected S := by rw [hSu]; exact isPreconnected_Ioi
    have hcontσ : ContinuousOn (fun t : ℝ => chartPD0 p (γ t)) S := by
      refine ((chartPD0 p).contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_
      intro t ht
      exact ((mem_cBall_iff p δ (γ t)).mp (by rwa [hSdef] at ht)).1
    have hσne : ∀ t ∈ S, chartPD0 p (γ t) ≠ 0 := by
      intro t ht h0
      have hsrc : γ t ∈ (chartPD0 p).source :=
        ((mem_cBall_iff p δ (γ t)).mp (by rwa [hSdef] at ht)).1
      exact hpne t ((chartPD0 p).toPartialEquiv.injOn hsrc (chartPD0_mem_source p)
        (by rw [h0, chartPD0_self]))
    have hsign : (∀ t ∈ S, 0 < chartPD0 p (γ t)) ∨ (∀ t ∈ S, chartPD0 p (γ t) < 0) := by
      have hsub0 : (fun t => chartPD0 p (γ t)) '' S ⊆ Set.Ioi (0:ℝ) ∪ Set.Iio 0 := by
        rintro z ⟨t, ht, rfl⟩
        rcases lt_or_gt_of_ne (hσne t ht) with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases (hSconn.image (fun t => chartPD0 p (γ t)) hcontσ).subset_or_subset
        isOpen_Ioi isOpen_Iio
        (Set.disjoint_left.mpr fun z h1 h2 => absurd h2 (not_lt.mpr h1.le)) hsub0 with h | h
      · left; intro t ht; exact h ⟨t, ht, rfl⟩
      · right; intro t ht; exact h ⟨t, ht, rfl⟩
    rcases hsign with hpos | hneg
    · refine extend_contra hA hAmax hinj hld hrange hpnot hconvp (chartPD0 p)
        (chartPD0_mem_source p) (chartPD0_self p) hδ ?_ ?_ ?_
      · intro v hv; exact hIcc ⟨hv.1.le, hv.2.le⟩
      · refine ⟨T₁, fun t ht => ?_⟩
        have htS : t ∈ S := by rw [hSdef]; exact hT₁ t ht
        have h2 := (mem_cBall_iff p δ (γ t)).mp (by rwa [hSdef] at htS)
        refine ⟨h2.1, hpos t (by rwa [hSdef] at htS), ?_⟩
        exact (abs_lt.mp h2.2).2
      · intro t ht htgt
        have hmem : γ t ∈ cBall p δ :=
          (mem_cBall_iff p δ (γ t)).mpr
            ⟨ht, abs_lt.mpr ⟨by linarith [htgt.1], by linarith [htgt.2]⟩⟩
        have htS : t ∈ S := by rw [hSdef]; exact hmem
        exact (hpos t htS).le
    · refine extend_contra hA hAmax hinj hld hrange hpnot hconvp (chartPD0neg p)
        (chartPD0neg_mem_source p) (chartPD0neg_self p) hδ
        (Ioo_subset_chartPD0neg_target (Set.Ioo_subset_Icc_self.trans hIcc)) ?_ ?_
      · refine ⟨T₁, fun t ht => ?_⟩
        have htS : t ∈ S := by rw [hSdef]; exact hT₁ t ht
        have h2 := (mem_cBall_iff p δ (γ t)).mp (by rwa [hSdef] at htS)
        have hneg' : chartPD p (γ t) - chartPD p p < 0 := hneg t (by rwa [hSdef] at htS)
        refine ⟨h2.1, ?_, ?_⟩
        · rw [chartPD0neg_apply]; linarith
        · rw [chartPD0neg_apply]
          have h3 : -δ < chartPD p (γ t) - chartPD p p := (abs_lt.mp h2.2).1
          linarith
      · intro t ht htgt
        have h4 : |chartPD0 p (γ t)| < δ := by
          rw [chartPD0neg_apply] at htgt
          rw [abs_lt, chartPD0_apply]
          exact ⟨by linarith [htgt.2], by linarith [htgt.1]⟩
        have hmem : γ t ∈ cBall p δ := (mem_cBall_iff p δ (γ t)).mpr ⟨ht, h4⟩
        have htS : t ∈ S := by rw [hSdef]; exact hmem
        have hneg' : chartPD p (γ t) - chartPD p p < 0 := hneg t htS
        rw [chartPD0neg_apply]
        linarith
  rcases hxc with hxpos | hxneg <;> rcases hyc with hypos | hyneg
  · exact hxy (tendsto_nhds_unique (convtop x hxpos) (convtop y hypos))
  · exact main x y hx hy hxy hxpos hyneg
  · exact main y x hy hx (fun h => hxy h.symm) hypos hxneg
  · exact hxy (tendsto_nhds_unique (convbot x hxneg) (convbot y hyneg))

/-- **The shape at a cluster point.**  If the frontier of a maximal open arc is the single point
`q`, and the parametrisation converges to `q` at `+∞` arriving in the positive half of a recentred
chart, then the arc is the complement of `q` and the parametrisation converges to `q` at both
ends. -/
theorem end_analysis [T2Space C] [SecondCountableTopology C] [ConnectedSpace C]
    {A : Set C} (hA : IsOpenArc A)
    (hAmax : ∀ B : Set C, IsOpenArc B → A ⊆ B → B ⊆ A)
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ)
    (hrange : Set.range γ = A)
    {q : C} (hq : q ∉ A) (hfront : frontier A = {q})
    (hconv : Filter.Tendsto γ Filter.atTop (nhds q))
    (ψ : PartialDiffeomorph I1 (modelWithCornersSelf ℝ ℝ) C ℝ sm)
    (hqsrc : q ∈ ψ.source) (hq0 : ψ q = 0) {δ : ℝ} (hδ : 0 < δ)
    (hballtgt : Metric.closedBall ((chartAt E1 q) q) δ ⊆ (chartAt E1 q).target)
    (htgt : Set.Ioo (-δ) δ ⊆ ψ.target)
    (hW : ∀ ρ : ℝ, ∀ z : C, z ∈ cBall q ρ ↔ z ∈ ψ.source ∧ ψ z ∈ Set.Ioo (-ρ) ρ)
    (hWc : ∀ ρ : ℝ, ∀ z : C, z ∈ cClosed q ρ → z ∈ ψ.source ∧ ψ z ∈ Set.Icc (-ρ) ρ)
    (hpos : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ ψ.source ∧ 0 < ψ (γ t) ∧ ψ (γ t) < δ) :
    A = {q}ᶜ ∧ Filter.Tendsto γ Filter.atTop (nhds q) ∧
      Filter.Tendsto γ Filter.atBot (nhds q) := by
  have hγcont : Continuous γ := hld.contMDiff.continuous
  have hqne : ∀ t, γ t ≠ q := fun t ht => hq (by rw [← hrange]; exact ⟨t, ht⟩)
  have hqnotmem : q ∉ Set.range γ := by rw [hrange]; exact hq
  have hqfront : ∀ z : C, z ∈ frontier A → z = q := fun z hz => by
    rw [hfront] at hz; simpa using hz
  have hposK : ∃ T : ℝ, ∀ t ≥ T, γ t ∈ ψ.source ∧ 0 < ψ (γ t) ∧ ψ (γ t) < δ := hpos
  obtain ⟨T₀, hT₀⟩ := hposK
  set S : Set ℝ := γ ⁻¹' cBall q δ with hSdef
  have hSopen : IsOpen S := (isOpen_cBall q δ).preimage hγcont
  have hS_tail : ∀ t ≥ T₀, t ∈ S := by
    intro t ht
    rw [hSdef]
    exact (hW δ (γ t)).mpr ⟨(hT₀ t ht).1, ⟨by linarith [(hT₀ t ht).2.1], (hT₀ t ht).2.2⟩⟩
  have hnbc : ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ S → a ∉ S → b ∉ S → False := by
    intro a b hab hsub ha hb
    refine no_bounded_component hδ hballtgt hγcont hinj hqne hab ?_ ?_ ?_
    · intro t ht
      have := hsub ht
      rwa [hSdef] at this
    · rwa [hSdef] at ha
    · rwa [hSdef] at hb
  have hSmem : ∀ t : ℝ, t ∈ S ↔ γ t ∈ cBall q δ := fun t => by
    rw [hSdef, Set.mem_preimage]
  have hσne : ∀ t ∈ S, ψ (γ t) ≠ 0 := by
    intro t ht h0
    have hsrc : γ t ∈ ψ.source := ((hW δ (γ t)).mp ((hSmem t).mp ht)).1
    exact hqne t (ψ.toPartialEquiv.injOn hsrc hqsrc (by rw [h0, hq0]))
  have hsigntop : ∀ u : ℝ, (∀ t ∈ Set.Ioi u, t ∈ S) → ∀ t ∈ Set.Ioi u, 0 < ψ (γ t) := by
    intro u hu
    have hcont : ContinuousOn (fun t : ℝ => ψ (γ t)) (Set.Ioi u) := by
      refine ((ψ.contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_)
      intro t ht
      exact ((hW δ (γ t)).mp ((hSmem t).mp (hu t ht))).1
    exact pos_of_preconnected isPreconnected_Ioi hcont (fun t ht => hσne t (hu t ht))
      (lt_of_lt_of_le (by linarith) (le_max_right T₀ (u + 1)))
      (hT₀ _ (le_max_left T₀ (u + 1))).2.1
  rcases structure_of_no_bounded_component hSopen hnbc ⟨T₀, hS_tail⟩ with
    huniv | ⟨u, hSu⟩ | ⟨v, u, hvu, hSv⟩
  · exfalso
    have hposS : ∀ t : ℝ, 0 < ψ (γ t) := by
      have hcont : ContinuousOn (fun t : ℝ => ψ (γ t)) Set.univ := by
        refine ((ψ.contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_)
        intro t _
        exact ((hW δ (γ t)).mp ((hSmem t).mp (by rw [huniv]; exact trivial))).1
      intro t
      exact pos_of_preconnected isPreconnected_univ hcont
        (fun u _ => hσne u (by rw [huniv]; exact trivial)) (mem_univ T₀) (hT₀ T₀ le_rfl).2.1
        t (mem_univ t)
    exact extend_contra hA hAmax hinj hld hrange hqnotmem hconv ψ hqsrc hq0 hδ htgt hpos
      (fun t _ _ => (hposS t).le)
  · exfalso
    have hposS : ∀ t ∈ Set.Ioi u, 0 < ψ (γ t) :=
      hsigntop u (fun t ht => by rw [hSu]; exact ht)
    exact extend_contra hA hAmax hinj hld hrange hqnotmem hconv ψ hqsrc hq0 hδ htgt hpos
      (fun t ht hmem => by
        have hmemS : γ t ∈ cBall q δ := (hW δ (γ t)).mpr ⟨ht, hmem⟩
        have htS : t ∈ S := (hSmem t).mpr hmemS
        rw [hSu] at htS
        exact (hposS t htS).le)
  · have hposS : ∀ t ∈ Set.Ioi u, 0 < ψ (γ t) :=
      hsigntop u (fun t ht => by rw [hSv]; exact Or.inr ht)
    have hnegS : ∀ t ∈ Set.Iio v, ψ (γ t) < 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨t₀, ht₀, hgt₀⟩ := hcon
      have hcont : ContinuousOn (fun t : ℝ => ψ (γ t)) (Set.Iio v) := by
        refine ((ψ.contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_)
        intro t ht
        exact ((hW δ (γ t)).mp ((hSmem t).mp (by rw [hSv]; exact Or.inl ht))).1
      have hne' : ∀ t ∈ Set.Iio v, ψ (γ t) ≠ 0 := fun t ht =>
        hσne t (by rw [hSv]; exact Or.inl ht)
      have hpos' : ∀ t ∈ Set.Iio v, 0 < ψ (γ t) :=
        pos_of_preconnected isPreconnected_Iio hcont hne' ht₀
          (lt_of_le_of_ne hgt₀ (Ne.symm (hne' t₀ ht₀)))
      refine (extend_contra hA hAmax hinj hld hrange hqnotmem hconv ψ hqsrc hq0 hδ htgt hpos
        (fun t ht hmem => ?_)).elim
      have hmemS : γ t ∈ cBall q δ := (hW δ (γ t)).mpr ⟨ht, hmem⟩
      have htS : t ∈ S := (hSmem t).mpr hmemS
      rw [hSv] at htS
      rcases htS with h | h
      · exact (hpos' t h).le
      · exact (hposS t h).le
    have hu_cl : γ u ∈ cClosed q δ := by
      refine closure_cBall_subset hballtgt (closure_mono ?_ (mem_closure_image_Ioi hγcont))
      rintro y ⟨t, ht, rfl⟩
      have htS : t ∈ S := by rw [hSv]; exact Or.inr ht
      have := htS
      rwa [hSdef] at this
    have hu_not : γ u ∉ cBall q δ := by
      intro hmem
      have hmemS : u ∈ S := (hSmem u).mpr hmem
      rw [hSv, Set.mem_union] at hmemS
      rcases hmemS with h | h
      · exact absurd h (not_lt.mpr hvu)
      · exact absurd h (lt_irrefl u)
    have hu_src : γ u ∈ ψ.source := (hWc δ (γ u) hu_cl).1
    have hlimu : Filter.Tendsto (fun t : ℝ => ψ (γ t)) (𝓝[>] u) (nhds (ψ (γ u))) := by
      have hc : ContinuousAt (fun z : C => ψ z) (γ u) :=
        ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hu_src)
      exact (hc.tendsto.comp hγcont.continuousAt).mono_left nhdsWithin_le_nhds
    have hψu : ψ (γ u) = δ := by
      have hIcc := (hWc δ (γ u) hu_cl).2
      have hnot : ψ (γ u) ∉ Set.Ioo (-δ) δ := fun h =>
        hu_not ((hW δ (γ u)).mpr ⟨hu_src, h⟩)
      have hge : 0 ≤ ψ (γ u) := by
        refine ge_of_tendsto hlimu ?_
        filter_upwards [Ioo_mem_nhdsGT (show u < u + 1 by linarith)] with t ht
        exact (hposS t ht.1).le
      rcases lt_trichotomy (ψ (γ u)) (-δ) with h | h | h
      · linarith [hIcc.1]
      · exact absurd ⟨by linarith, by linarith [hIcc.2]⟩ hnot
      · rcases lt_trichotomy (ψ (γ u)) δ with h2 | h2 | h2
        · exact absurd ⟨h, h2⟩ hnot
        · exact h2
        · linarith [hIcc.2]
    have hv_cl : γ v ∈ cClosed q δ := by
      refine closure_cBall_subset hballtgt (closure_mono ?_ (mem_closure_image_Iio hγcont))
      rintro y ⟨t, ht, rfl⟩
      have htS : t ∈ S := by rw [hSv]; exact Or.inl ht
      have := htS
      rwa [hSdef] at this
    have hv_not : γ v ∉ cBall q δ := by
      intro hmem
      have hmemS : v ∈ S := (hSmem v).mpr hmem
      rw [hSv, Set.mem_union] at hmemS
      rcases hmemS with h | h
      · exact absurd h (lt_irrefl v)
      · exact absurd h (not_lt.mpr hvu)
    have hv_src : γ v ∈ ψ.source := (hWc δ (γ v) hv_cl).1
    have hlimv : Filter.Tendsto (fun t : ℝ => ψ (γ t)) (𝓝[<] v) (nhds (ψ (γ v))) := by
      have hc : ContinuousAt (fun z : C => ψ z) (γ v) :=
        ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hv_src)
      exact (hc.tendsto.comp hγcont.continuousAt).mono_left nhdsWithin_le_nhds
    have hψv : ψ (γ v) = -δ := by
      have hIcc := (hWc δ (γ v) hv_cl).2
      have hnot : ψ (γ v) ∉ Set.Ioo (-δ) δ := fun h =>
        hv_not ((hW δ (γ v)).mpr ⟨hv_src, h⟩)
      have hle : ψ (γ v) ≤ 0 := by
        refine le_of_tendsto hlimv ?_
        filter_upwards [Ioo_mem_nhdsLT (show v - 1 < v by linarith)] with t ht
        exact (hnegS t ht.2).le
      rcases lt_trichotomy (ψ (γ v)) (-δ) with h | h | h
      · linarith [hIcc.1]
      · exact h
      · rcases lt_trichotomy (ψ (γ v)) δ with h2 | h2 | h2
        · exact absurd ⟨h, h2⟩ hnot
        · linarith
        · linarith [hIcc.2]
    have hfreq : ∀ U : Set C, IsOpen U → q ∈ U →
        Filter.Frequently (fun t : ℝ => γ t ∈ U) Filter.atBot := by
      intro U hUo hqU
      obtain ⟨ε, hε, -, hεball, -, -⟩ := exists_chart_ball q U (hUo.mem_nhds hqU)
      by_contra hcon
      rw [Filter.frequently_atBot] at hcon
      push_neg at hcon
      obtain ⟨T, hT⟩ := hcon
      set T' : ℝ := min T (v - 1) with hT'def
      have hTK : cClosed q δ ∈ Filter.map γ Filter.atBot := by
        rw [Filter.mem_map]
        refine Filter.mem_of_superset (show Set.Iio T' ∈ Filter.atBot from Iio_mem_atBot T') ?_
        intro t ht
        have h2 : t < v := by
          have h3 : t < min T (v - 1) := by rw [hT'def] at ht; exact ht
          have h4 := min_le_right T (v - 1); linarith
        have htS : t ∈ S := by rw [hSv]; exact Or.inl h2
        exact cBall_subset_cClosed q δ ((hSmem t).mp htS)
      obtain ⟨x, hxK, hxcl⟩ := (isCompact_cClosed hballtgt).exists_clusterPt
        (f := Filter.map γ Filter.atBot) (fun s hs => Filter.mem_of_superset hTK hs)
      have hxconv : Filter.Tendsto γ Filter.atBot (nhds x) :=
        tendsto_atBot_of_clusterPt hγcont hinj hxcl
      have hxnot : x ∉ Set.range γ := not_mem_range_of_tendsto_atBot hld hinj hxconv
      have hxsrc : x ∈ ψ.source := (hWc δ x hxK).1
      have hxlim : Filter.Tendsto (fun t : ℝ => ψ (γ t)) Filter.atBot (nhds (ψ x)) := by
        have hc : ContinuousAt (fun z : C => ψ z) x :=
          ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hxsrc)
        exact hc.tendsto.comp hxconv
      have hle : ∀ t ≤ T', ψ (γ t) ≤ -ε := by
        intro t ht
        have htv : t < v := by
          have h1 : t ≤ min T (v - 1) := by rw [hT'def] at ht; exact ht
          have h2 := min_le_right T (v - 1); linarith
        have htS : t ∈ S := by rw [hSv]; exact Or.inl htv
        have hmem : ψ (γ t) ∈ Set.Ioo (-δ) δ := ((hW δ (γ t)).mp ((hSmem t).mp htS)).2
        have hneg := hnegS t htv
        have hnotin : ψ (γ t) ∉ Set.Ioo (-ε) ε := by
          intro hmem'
          exact (hT t (le_trans ht (min_le_left _ _)))
            (hεball ((hW ε (γ t)).mpr ⟨((hW δ (γ t)).mp ((hSmem t).mp htS)).1, hmem'⟩))
        by_contra hcon2
        rw [not_le] at hcon2
        exact hnotin ⟨by linarith, by linarith [hneg]⟩
      have hxle : ψ x ≤ -ε := le_of_tendsto hxlim (Filter.eventually_atBot.mpr ⟨T', hle⟩)
      have hxclA : x ∈ closure A := by
        rw [← hrange, mem_closure_iff_nhds]
        intro V hV
        obtain ⟨t, ht⟩ := (hxconv.eventually hV).exists
        exact ⟨γ t, ht, ⟨t, rfl⟩⟩
      have hxfr : x ∈ frontier A := by
        rw [frontier, Set.mem_sdiff]
        refine ⟨hxclA, ?_⟩
        rw [hA.isOpen.interior_eq, ← hrange]
        exact hxnot
      have hxeq : x = q := hqfront x hxfr
      have : ψ x = 0 := by rw [hxeq, hq0]
      linarith
    have hconvbot : Filter.Tendsto γ Filter.atBot (nhds q) :=
      tendsto_atBot_of_frequently hγcont hinj hfreq
    have cover_pos : ∀ w ∈ Set.Ioo (0:ℝ) δ, ∃ t : ℝ, u < t ∧ ψ (γ t) = w := by
      intro w hw
      have hc : ContinuousAt (fun t : ℝ => ψ (γ t)) u := by
        have hc' : ContinuousAt (fun z : C => ψ z) (γ u) :=
          ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hu_src)
        exact hc'.tendsto.comp hγcont.continuousAt
      have hmem : (fun t : ℝ => ψ (γ t)) ⁻¹' Set.Ioi w ∈ 𝓝 u :=
        hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hψu]; exact hw.2))
      obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hmem
      have h1 : w < ψ (γ (u + ε₁/2)) := hε₁sub (by
        rw [Metric.mem_ball, Real.dist_eq, show u + ε₁/2 - u = ε₁/2 from by ring]
        rw [abs_of_pos (by linarith : (0:ℝ) < ε₁/2)]
        linarith)
      have hlim0 : Filter.Tendsto (fun t : ℝ => ψ (γ t)) Filter.atTop (nhds 0) := by
        have hc' : ContinuousAt (fun z : C => ψ z) q :=
          ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hqsrc)
        have h1 := hc'.tendsto.comp hconv
        rw [hq0] at h1
        exact h1
      obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
        (hlim0.eventually (isOpen_Iio.mem_nhds hw.1))
      set t₂ : ℝ := max T₂ (u + ε₁) with ht₂def
      have h2 : ψ (γ t₂) < w := hT₂ t₂ (le_max_left _ _)
      have hle : u + ε₁/2 ≤ t₂ := by
        have := le_max_right T₂ (u + ε₁); linarith
      have hcontOn : ContinuousOn (fun t : ℝ => ψ (γ t)) (Set.Icc (u + ε₁/2) t₂) := by
        refine ((ψ.contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_)
        intro t ht
        have htu : u < t := by have h1 := ht.1; linarith
        have htS : t ∈ S := by rw [hSv]; exact Or.inr htu
        exact ((hW δ (γ t)).mp ((hSmem t).mp htS)).1
      have hmemw : w ∈ Set.Icc (ψ (γ t₂)) (ψ (γ (u + ε₁/2))) := ⟨h2.le, h1.le⟩
      obtain ⟨t, htI, htw⟩ := intermediate_value_Icc' hle hcontOn hmemw
      exact ⟨t, lt_of_lt_of_le (by linarith) htI.1, htw⟩
    have cover_neg : ∀ w ∈ Set.Ioo (-δ) 0, ∃ t : ℝ, t < v ∧ ψ (γ t) = w := by
      intro w hw
      have hc : ContinuousAt (fun t : ℝ => ψ (γ t)) v := by
        have hc' : ContinuousAt (fun z : C => ψ z) (γ v) :=
          ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hv_src)
        exact hc'.tendsto.comp hγcont.continuousAt
      have hmem : (fun t : ℝ => ψ (γ t)) ⁻¹' Set.Iio w ∈ 𝓝 v :=
        hc.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rw [hψv]; exact hw.1))
      obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp hmem
      have h1 : ψ (γ (v - ε₁/2)) < w := hε₁sub (by
        rw [Metric.mem_ball, Real.dist_eq, show v - ε₁/2 - v = -ε₁/2 from by ring]
        rw [abs_of_neg (by linarith : (-ε₁/2 : ℝ) < 0)]
        linarith)
      have hlim0 : Filter.Tendsto (fun t : ℝ => ψ (γ t)) Filter.atBot (nhds 0) := by
        have hc' : ContinuousAt (fun z : C => ψ z) q :=
          ψ.contMDiffOn_toFun.continuousOn.continuousAt (ψ.open_source.mem_nhds hqsrc)
        have h1 := hc'.tendsto.comp hconvbot
        rw [hq0] at h1
        exact h1
      obtain ⟨T₂, hT₂⟩ := Filter.eventually_atBot.mp
        (hlim0.eventually (isOpen_Ioi.mem_nhds hw.2))
      set t₂ : ℝ := min T₂ (v - ε₁) with ht₂def
      have h2 : w < ψ (γ t₂) := hT₂ t₂ (min_le_left _ _)
      have hle : t₂ ≤ v - ε₁/2 := by
        have := min_le_right T₂ (v - ε₁); linarith
      have hcontOn : ContinuousOn (fun t : ℝ => ψ (γ t)) (Set.Icc t₂ (v - ε₁/2)) := by
        refine ((ψ.contMDiffOn_toFun.continuousOn).comp hγcont.continuousOn ?_)
        intro t ht
        have htv : t < v := by have h1 := ht.2; linarith
        have htS : t ∈ S := by rw [hSv]; exact Or.inl htv
        exact ((hW δ (γ t)).mp ((hSmem t).mp htS)).1
      have hmemw : w ∈ Set.Icc (ψ (γ (v - ε₁/2))) (ψ (γ t₂)) := ⟨h1.le, h2.le⟩
      obtain ⟨t, htI, htw⟩ := intermediate_value_Icc' hle hcontOn hmemw
      exact ⟨t, lt_of_le_of_lt htI.2 (by linarith), htw⟩
    have hsub : cBall q δ ⊆ A ∪ {q} := by
      intro z hz
      obtain ⟨hzsrc, hzmem⟩ := (hW δ z).mp hz
      rcases lt_trichotomy (ψ z) 0 with h | h | h
      · obtain ⟨t, ht, htw⟩ := cover_neg (ψ z) ⟨hzmem.1, h⟩
        have htS : t ∈ S := by rw [hSv]; exact Or.inl ht
        have htsrc : γ t ∈ ψ.source := ((hW δ (γ t)).mp ((hSmem t).mp htS)).1
        exact Or.inl (by rw [← hrange]; exact ⟨t, ψ.toPartialEquiv.injOn htsrc hzsrc htw⟩)
      · exact Or.inr (by
          rw [Set.mem_singleton_iff]
          exact ψ.toPartialEquiv.injOn hzsrc hqsrc (by rw [h, hq0]))
      · obtain ⟨t, ht, htw⟩ := cover_pos (ψ z) ⟨h, hzmem.2⟩
        have htS : t ∈ S := by rw [hSv]; exact Or.inr ht
        have htsrc : γ t ∈ ψ.source := ((hW δ (γ t)).mp ((hSmem t).mp htS)).1
        exact Or.inl (by rw [← hrange]; exact ⟨t, ψ.toPartialEquiv.injOn htsrc hzsrc htw⟩)
    have hqball : q ∈ cBall q δ :=
      (hW δ q).mpr ⟨hqsrc, by rw [hq0]; exact ⟨by linarith, hδ⟩⟩
    have hclopen : A ∪ {q} = Set.univ := by
      have hopen : IsOpen (A ∪ {q}) := by
        rw [isOpen_iff_mem_nhds]
        intro z hz
        rcases hz with hzA | hzq
        · exact Filter.mem_of_superset (hA.isOpen.mem_nhds hzA) Set.subset_union_left
        · rw [Set.mem_singleton_iff] at hzq
          rw [hzq]
          exact Filter.mem_of_superset ((isOpen_cBall q δ).mem_nhds hqball) hsub
      have hclosed : IsClosed (A ∪ {q}) := by
        have h1 : A ∪ {q} = closure A := by
          rw [← hfront]
          exact (closure_eq_self_union_frontier (s := A)).symm
        rw [h1]; exact isClosed_closure
      rcases IsPreconnected.subset_or_subset hopen (isOpen_compl_iff.mpr hclosed)
        disjoint_compl_right (le_of_eq (Set.union_compl_self (A ∪ {q})).symm)
        isPreconnected_univ with h | h
      · exact eq_univ_of_univ_subset h
      · exfalso
        exact h (Set.mem_univ q) (Or.inr rfl)
    have hAeq : A = {q}ᶜ := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun hzq => hq (hzq ▸ hz)
      · intro hz
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have h2 : z ∈ A ∪ {q} := by rw [hclopen]; exact trivial
        rcases h2 with h | h
        · exact h
        · exact absurd h hz
    exact ⟨hAeq, hconv, hconvbot⟩

lemma cClosed_of_chartPD0 (q : C) (ρ : ℝ) (z : C) :
    z ∈ cClosed q ρ → z ∈ (chartPD0 q).source ∧ chartPD0 q z ∈ Set.Icc (-ρ) ρ := by
  intro hz
  obtain ⟨h1, h2⟩ := (mem_cClosed_iff q ρ z).mp hz
  exact ⟨h1, abs_le.mp h2⟩

lemma cClosed_of_chartPD0neg (q : C) (ρ : ℝ) (z : C) :
    z ∈ cClosed q ρ → z ∈ (chartPD0neg q).source ∧ chartPD0neg q z ∈ Set.Icc (-ρ) ρ := by
  intro hz
  obtain ⟨h1, h2⟩ := (mem_cClosed_iff q ρ z).mp hz
  have h3 : chartPD0neg q z = -(chartPD0 q z) := by
    show chartPD q q - chartPD q z = -(chartPD q z - chartPD q q)
    ring
  rw [h3]
  refine ⟨h1, ?_⟩
  obtain ⟨h4, h5⟩ := abs_le.mp h2
  exact ⟨by linarith, by linarith⟩

lemma isLocalDiffeomorph_neg :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
      (fun t : ℝ => -t) :=
  ift_real (by fun_prop) (by intro x; simp)

/-- **Shape of a maximal arc.** -/
theorem maximal_arc_shape [T2Space C] [SecondCountableTopology C] [ConnectedSpace C]
    {A : Set C} (hA : IsOpenArc A)
    (hAmax : ∀ B : Set C, IsOpenArc B → A ⊆ B → B ⊆ A)
    {γ : ℝ → C} (hinj : Function.Injective γ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm γ)
    (hrange : Set.range γ = A) :
    A = Set.univ ∨ ∃ q : C, A = {q}ᶜ ∧ Filter.Tendsto γ Filter.atTop (nhds q) ∧
      Filter.Tendsto γ Filter.atBot (nhds q) := by
  by_cases hU : A = Set.univ
  · exact Or.inl hU
  right
  have hγcont : Continuous γ := hld.contMDiff.continuous
  have hAopen : IsOpen A := hA.isOpen
  have hsub : (frontier A).Subsingleton :=
    frontier_subsingleton hA hAmax hinj hld hrange hU
  have hfne : (frontier A).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hcl : IsClosed A := by
      rw [← closure_subset_iff_isClosed]
      intro z hz
      by_contra hzA
      have hzf : z ∈ frontier A := by
        rw [frontier, Set.mem_sdiff]
        exact ⟨hz, by rw [hAopen.interior_eq]; exact hzA⟩
      rw [hempty] at hzf
      exact hzf
    rcases IsPreconnected.subset_or_subset hAopen (isOpen_compl_iff.mpr hcl)
      disjoint_compl_right (le_of_eq (Set.union_compl_self A).symm) isPreconnected_univ with h | h
    · exact hU (eq_univ_of_univ_subset h)
    · exact hA.nonempty.ne_empty (eq_empty_of_subset_empty fun x hx => h (mem_univ x) hx)
  obtain ⟨q, hq⟩ := hfne
  have hfront : frontier A = {q} := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff]
      exact hsub hz hq
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hq
  have hqA : q ∉ A := by
    have h := hq.2
    rwa [hAopen.interior_eq] at h
  have hqne : ∀ t, γ t ≠ q := fun t ht => hqA (by rw [← hrange]; exact ⟨t, ht⟩)
  -- the main step for a curve whose cluster point is at `+∞`
  have hmain : ∀ (η : ℝ → C), Function.Injective η →
      IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm η → Set.range η = A →
      Filter.Tendsto η Filter.atTop (nhds q) →
      A = {q}ᶜ ∧ Filter.Tendsto η Filter.atTop (nhds q) ∧
        Filter.Tendsto η Filter.atBot (nhds q) := by
    intro η hηinj hηld hηrange hηconv
    have hηcont : Continuous η := hηld.contMDiff.continuous
    have hηne : ∀ t, η t ≠ q := fun t ht => hqA (by rw [← hηrange]; exact ⟨t, ht⟩)
    have hqball' : ∃ ρ : ℝ, 0 < ρ ∧ Set.Icc (-ρ) ρ ⊆ (chartPD0 q).target ∧
        cBall q ρ ⊆ Set.univ ∧ cClosed q ρ ⊆ Set.univ ∧
        Metric.closedBall ((chartAt E1 q) q) ρ ⊆ (chartAt E1 q).target :=
      exists_chart_ball q Set.univ Filter.univ_mem
    obtain ⟨δ, hδ, hIcc, -, -, hclosed⟩ := hqball'
    have hqball : q ∈ cBall q δ :=
      (mem_cBall_iff q δ q).mpr ⟨mem_chart_source E1 q, by rw [chartPD0_self]; simpa using hδ⟩
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
      (hηconv.eventually ((isOpen_cBall q δ).mem_nhds hqball))
    have hne : ∀ t ≥ T₀, chartPD0 q (η t) ≠ 0 := by
      intro t ht h0
      have hsrc : η t ∈ (chartPD0 q).source :=
        ((mem_cBall_iff q δ (η t)).mp (hT₀ t ht)).1
      exact hηne t ((chartPD0 q).toPartialEquiv.injOn hsrc (chartPD0_mem_source q)
        (by rw [h0, chartPD0_self]))
    have hsign : (∀ t, T₀ < t → 0 < chartPD0 q (η t)) ∨
        (∀ t, T₀ < t → chartPD0 q (η t) < 0) := by
      have hcont : ContinuousOn (fun t : ℝ => chartPD0 q (η t)) (Set.Ioi T₀) := by
        refine ((chartPD0 q).contMDiffOn_toFun.continuousOn).comp hηcont.continuousOn ?_
        intro t ht
        exact ((mem_cBall_iff q δ (η t)).mp (hT₀ t (le_of_lt ht))).1
      have hsub0 : (fun t : ℝ => chartPD0 q (η t)) '' Set.Ioi T₀ ⊆
          Set.Ioi (0:ℝ) ∪ Set.Iio 0 := by
        rintro z ⟨t, ht, rfl⟩
        rcases lt_or_gt_of_ne (hne t (le_of_lt ht)) with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases ((isPreconnected_Ioi (a := T₀)).image (fun t : ℝ => chartPD0 q (η t))
        hcont).subset_or_subset isOpen_Ioi isOpen_Iio
        (Set.disjoint_left.mpr fun z h1 h2 => absurd h2 (not_lt.mpr h1.le)) hsub0 with h | h
      · left
        intro t ht
        simpa using h ⟨t, ht, rfl⟩
      · right
        intro t ht
        simpa using h ⟨t, ht, rfl⟩
    rcases hsign with hsign | hsign
    · refine end_analysis hA hAmax hηinj hηld hηrange hqA hfront hηconv (chartPD0 q)
        (chartPD0_mem_source q) (chartPD0_self q) hδ hclosed
        (Set.Ioo_subset_Icc_self.trans hIcc)
        (fun ρ z => by rw [cBall_iff_chartPD0])
        (fun ρ z hz => cClosed_of_chartPD0 q ρ z hz) ?_
      refine ⟨T₀ + 1, fun t ht => ?_⟩
      have hmem := (mem_cBall_iff q δ (η t)).mp (hT₀ t (by linarith))
      exact ⟨hmem.1, ⟨hsign t (by linarith), (abs_lt.mp hmem.2).2⟩⟩
    · refine end_analysis hA hAmax hηinj hηld hηrange hqA hfront hηconv (chartPD0neg q)
        (chartPD0neg_mem_source q) (chartPD0neg_self q) hδ hclosed
        (Ioo_subset_chartPD0neg_target (Set.Ioo_subset_Icc_self.trans hIcc))
        (fun ρ z => by rw [cBall_iff_chartPD0neg])
        (fun ρ z hz => cClosed_of_chartPD0neg q ρ z hz) ?_
      refine ⟨T₀ + 1, fun t ht => ?_⟩
      have hmem := (mem_cBall_iff q δ (η t)).mp (hT₀ t (by linarith))
      have hneg : chartPD q (η t) - chartPD q q < 0 := hsign t (by linarith)
      have h3 : -δ < chartPD q (η t) - chartPD q q := (abs_lt.mp hmem.2).1
      refine ⟨hmem.1, ?_, ?_⟩
      · rw [chartPD0neg_apply]; linarith
      · rw [chartPD0neg_apply]; linarith
  have hcluster : ClusterPt q (Filter.map γ Filter.atTop) ∨
      ClusterPt q (Filter.map γ Filter.atBot) :=
    frontier_subset_cluster hAopen hγcont hrange hq
  rcases hcluster with htop | hbot
  · obtain ⟨h1, h2, h3⟩ := hmain γ hinj hld hrange (tendsto_atTop_of_clusterPt hγcont hinj htop)
    exact ⟨q, h1, h2, h3⟩
  · have hηinj : Function.Injective (fun t : ℝ => γ (-t)) := fun a b hab => by
      have := hinj hab
      simpa using this
    have hηld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm (fun t : ℝ => γ (-t)) := by
      intro t
      exact IsLocalDiffeomorphAt.comp (K := I1) (P := C) (isLocalDiffeomorph_neg t) (hld (-t))
    have hηrange : Set.range (fun t : ℝ => γ (-t)) = A := by
      rw [← hrange]
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨-t, by simp⟩
      · rintro ⟨t, rfl⟩
        exact ⟨-t, by simp⟩
    have hηconv : Filter.Tendsto (fun t : ℝ => γ (-t)) Filter.atTop (nhds q) :=
      (tendsto_atBot_of_clusterPt hγcont hinj hbot).comp tendsto_neg_atTop_atBot
    obtain ⟨h1, h2, h3⟩ := hmain (fun t : ℝ => γ (-t)) hηinj hηld hηrange hηconv
    refine ⟨q, h1, ?_, ?_⟩
    · have h3' : Filter.Tendsto γ (Filter.map (fun t : ℝ => -t) Filter.atBot) (nhds q) := h3
      rwa [Filter.map_neg_atBot] at h3'
    · have h2' : Filter.Tendsto γ (Filter.map (fun t : ℝ => -t) Filter.atTop) (nhds q) := h2
      rwa [Filter.map_neg_atTop] at h2'

end Work.OneDim
