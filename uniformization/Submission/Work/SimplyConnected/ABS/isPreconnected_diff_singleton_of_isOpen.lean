import Mathlib
import Submission.Work.SimplyConnected.Defs
import Submission.Work.Modulus.puncturedConnected

namespace Work.SimplyConnected.ABS

open Set Metric

/-- **A chart ball inside an open set.**  For an open set `U` of a charted space over `ℂ` and a
point `x ∈ U`, there is an open neighbourhood `V ⊆ U` of `x` whose punctured version `V ∖ {x}` is
preconnected: take a small ball around `chartAt ℂ x x` inside the image of `U` under the chart, and
transport the preconnectedness of the punctured ball (`Work.Modulus.isPreconnected_ball_diff_center`). -/
theorem exists_isOpen_subset_isPreconnected_diff_singleton {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ V ⊆ U ∧ x ∈ V ∧ IsPreconnected (V \ {x}) := by
  have hsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hcA : (chartAt ℂ x) x ∈ (chartAt ℂ x) '' ((chartAt ℂ x).source ∩ U) :=
    ⟨x, ⟨hsrc, hx⟩, rfl⟩
  have hAopen : IsOpen ((chartAt ℂ x) '' ((chartAt ℂ x).source ∩ U)) :=
    (chartAt ℂ x).isOpen_image_source_inter hU
  have hct : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.isOpen_iff.mp (hAopen.inter (chartAt ℂ x).open_target) ((chartAt ℂ x) x)
      ⟨hcA, hct⟩
  have hbt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target :=
    fun y hy => (hball hy).2
  refine ⟨(chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ, ?_, ?_, ?_, ?_⟩
  · exact (chartAt ℂ x).isOpen_image_symm_of_subset_target Metric.isOpen_ball hbt
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨u, ⟨husrc, huU⟩, huw⟩ := (hball hw).1
    rw [← huw, (chartAt ℂ x).left_inv husrc]
    exact huU
  · exact ⟨(chartAt ℂ x) x, mem_ball_self hρ, (chartAt ℂ x).left_inv hsrc⟩
  · have hset : (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) ρ \ {x}
        = (chartAt ℂ x).symm '' (Metric.ball ((chartAt ℂ x) x) ρ \ {(chartAt ℂ x) x}) := by
      ext y
      constructor
      · rintro ⟨hy, hyne⟩
        obtain ⟨w, hw, rfl⟩ := hy
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        intro hwc
        have h1 : (chartAt ℂ x).symm w = x := by rw [hwc, (chartAt ℂ x).left_inv hsrc]
        exact hyne (by simpa using h1)
      · rintro ⟨w, ⟨hw, hwc⟩, rfl⟩
        refine ⟨⟨w, hw, rfl⟩, ?_⟩
        intro hys
        have hys' : (chartAt ℂ x).symm w = x := by simpa using hys
        have h2 : (chartAt ℂ x) ((chartAt ℂ x).symm w) = (chartAt ℂ x) x := by rw [hys']
        rw [(chartAt ℂ x).right_inv (hbt hw)] at h2
        exact hwc h2
    rw [hset]
    exact (Work.Modulus.isPreconnected_ball_diff_center (c := (chartAt ℂ x) x) hρ).image
      (chartAt ℂ x).symm ((chartAt ℂ x).continuousOn_symm.mono fun y hy => hbt hy.1)

/-- **Auxiliary topological step, relative version.**  Let `U` be a preconnected set of a `T₁` space
containing `x`, and let `V ∋ x` be an open neighbourhood.  Suppose the punctured set `U ∖ {x}` is
covered by two open sets `u`, `v` that are disjoint on `U ∖ {x}`, and suppose `u` meets `U ∖ {x}`.
Then `u` meets the *punctured* neighbourhood `V ∖ {x}`.

This is the point where preconnectedness of `U` is used (in place of preconnectedness of the whole
space in `Work.Modulus.isPreconnected_compl_singleton_aux`): if `V ∩ u ⊆ {x}`, then either `{x}` is
open (when `x ∈ u`), or `u` and `V ∪ v` are two disjoint open sets covering `U`, one containing `x`
and one meeting `U ∖ {x}`. -/
theorem isPreconnected_diff_singleton_aux {X : Type*} [TopologicalSpace X] [T1Space X]
    {U : Set X} (hUc : IsPreconnected U) {x : X} (hxU : x ∈ U) {V u v : Set X}
    (hVo : IsOpen V) (hxV : x ∈ V)
    (hu : IsOpen u) (hv : IsOpen v)
    (huv : U \ {x} ⊆ u ∪ v) (hdisj : (U \ {x}) ∩ (u ∩ v) = ∅)
    (hune : ((U \ {x}) ∩ u).Nonempty) : ((V \ {x}) ∩ u).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hVu : V ∩ u ⊆ {x} := by
    intro y hy
    by_contra hy'
    exact (Set.eq_empty_iff_forall_notMem.mp h) y ⟨⟨hy.1, hy'⟩, hy.2⟩
  by_cases hxu : x ∈ u
  · have hEq : V ∩ u = {x} := by
      refine Subset.antisymm hVu fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ⟨hxV, hxu⟩
    have hopen : IsOpen ({x} : Set X) := hEq ▸ hVo.inter hu
    have hne1 : (U ∩ ({x} : Set X)).Nonempty := ⟨x, hxU, rfl⟩
    have hne2 : (U ∩ ({x}ᶜ : Set X)).Nonempty := hune.mono fun y hy => ⟨hy.1.1, hy.1.2⟩
    have hsub : U ⊆ ({x} : Set X) ∪ {x}ᶜ := by
      intro y _
      by_cases hyx : y = x
      · exact Or.inl (by simpa using hyx)
      · exact Or.inr (by simpa using hyx)
    obtain ⟨y, hy⟩ :=
      hUc ({x} : Set X) ({x}ᶜ : Set X) hopen isOpen_compl_singleton hsub hne1 hne2
    exact hy.2.2 hy.2.1
  · have hVue : V ∩ u = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hyx : y = x := by simpa using hVu hy
      exact hxu (hyx ▸ hy.2)
    have hsub : U ⊆ u ∪ (V ∪ v) := by
      intro y hy
      by_cases hyx : y = x
      · exact Or.inr (Or.inl (hyx ▸ hxV))
      · rcases huv ⟨hy, hyx⟩ with hu' | hv'
        · exact Or.inl hu'
        · exact Or.inr (Or.inr hv')
    have hne1 : (U ∩ u).Nonempty := hune.mono fun y hy => ⟨hy.1.1, hy.2⟩
    have hne2 : (U ∩ (V ∪ v)).Nonempty := ⟨x, hxU, Or.inl hxV⟩
    have hdisj' : U ∩ (u ∩ (V ∪ v)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      rcases hy.2.2 with hyV | hyv
      · exact (Set.eq_empty_iff_forall_notMem.mp hVue) y ⟨hyV, hy.2.1⟩
      · by_cases hyx : y = x
        · exact hxu (hyx ▸ hy.2.1)
        · exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨⟨hy.1, hyx⟩, hy.2.1, hyv⟩
    obtain ⟨y, hy⟩ := hUc u (V ∪ v) hu (hVo.union hv) hsub hne1 hne2
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj') y hy

/-- Removing a point from an open preconnected set of a complex one-manifold leaves it
preconnected: in real dimension 2 a point has a neighbourhood whose punctured version is connected
(a punctured disc), so puncturing cannot separate a preconnected open set. -/
theorem isPreconnected_diff_singleton_of_isOpen {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hUo : IsOpen U) (hUc : IsPreconnected U) {x : X} (hx : x ∈ U) :
    IsPreconnected (U \ {x}) := by
  obtain ⟨V, hVo, hVU, hxV, hVpc⟩ := exists_isOpen_subset_isPreconnected_diff_singleton hUo hx
  intro u v hu hv huv hune hvne
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have h1 : ((V \ {x}) ∩ u).Nonempty :=
    isPreconnected_diff_singleton_aux hUc hx hVo hxV hu hv huv hemp hune
  have hdisj' : (U \ {x}) ∩ (v ∩ u) = ∅ := by
    rw [Set.inter_comm v u]; exact hemp
  have hsub2 : U \ {x} ⊆ v ∪ u := fun y hy => (huv hy).elim Or.inr Or.inl
  have h2 : ((V \ {x}) ∩ v).Nonempty :=
    isPreconnected_diff_singleton_aux hUc hx hVo hxV hv hu hsub2 hdisj' hvne
  have hsub : V \ {x} ⊆ u ∪ v := fun y hy => huv ⟨hVU hy.1, hy.2⟩
  obtain ⟨y, hy⟩ := hVpc u v hu hv hsub h1 h2
  exact (Set.eq_empty_iff_forall_notMem.mp hemp) y ⟨⟨hVU hy.1.1, hy.1.2⟩, hy.2⟩

end Work.SimplyConnected.ABS
