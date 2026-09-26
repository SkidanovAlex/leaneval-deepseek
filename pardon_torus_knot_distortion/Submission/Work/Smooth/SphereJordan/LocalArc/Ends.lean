import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen
import Submission.Work.Smooth.SphereJordan.LocalArc.germCoveredBoth
import Submission.Work.Smooth.SphereJordan.LocalArc.Param

/-!
# The two ends of an embedded arc

For an injective continuous arc `α : ℝ → X` in a Hausdorff space whose tails converge to points
`p` (at `+∞`) and `q` (at `-∞`):

* `isOpenMap_of_injective_continuous`: if `X` is locally an arc then `α` is an open map
  (hence a homeomorphism onto its range);
* `closure_image_Ici_union`, `closure_image_Iic_union`: the closure of a tail is the tail together
  with its limit point;
* `closure_range_eq_ends`: the closure of the range is the range together with the two ends;
* `frontier_range_subset_ends`: the frontier of the range is contained in the two ends;
* `exists_circle_param_of_ends_eq`: if both ends coincide, `X` is a circle.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **A chart interval around a point of an embedded arc maps into any prescribed open set of
parameters.** -/
theorem chart_interval_subset_image {X : Type*} [TopologicalSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α) {s : ℝ} {W : Set ℝ} (hW : IsOpen W) (hsW : s ∈ W) :
    ∃ ε > 0, (Work.Smooth.SphereJordan.chartOf H (α s)).map '' Set.Ioo (-ε) ε ⊆ α '' W := by
  classical
  set c : Work.Smooth.SphereJordan.ArcChart X (α s) :=
    Work.Smooth.SphereJordan.chartOf H (α s) with hc
  have hV : ∀ᶠ u in 𝓝 s, α u ∈ c.V := hcont.continuousAt (c.isOpen_V.mem_nhds c.mem_V)
  have hWn : ∀ᶠ u in 𝓝 s, u ∈ W := hW.mem_nhds hsW
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp (hV.and hWn)
  have hball : ∀ u : ℝ, u ∈ Metric.ball s η → α u ∈ c.V ∧ u ∈ W := hηsub
  have hsub : Set.Ioo (s - η) (s + η) ⊆ α ⁻¹' c.V := fun u hu =>
    (hball u (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)).1
  have hsubW : Set.Ioo (s - η) (s + η) ⊆ W := fun u hu =>
    (hball u (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)).2
  let ξ : ℝ → ℝ := fun u => if h : α u ∈ c.V then c.coord ⟨α u, h⟩ else 0
  have hξ_eq : ∀ (u : ℝ) (hu : u ∈ Set.Ioo (s - η) (s + η)),
      ξ u = c.coord ⟨α u, hsub hu⟩ := by
    intro u hu
    change (if h : α u ∈ c.V then c.coord ⟨α u, h⟩ else 0) = c.coord ⟨α u, hsub hu⟩
    rw [dif_pos (show α u ∈ c.V from hsub hu)]
  have hξ_cont : ContinuousOn ξ (Set.Ioo (s - η) (s + η)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Set.domRestrict (Set.Ioo (s - η) (s + η)) ξ =
        fun z : Set.Ioo (s - η) (s + η) => c.coord ⟨α z.1, hsub z.2⟩ := by
      funext z
      change (if h : α z.1 ∈ c.V then c.coord ⟨α z.1, h⟩ else 0) = c.coord ⟨α z.1, hsub z.2⟩
      rw [dif_pos (show α z.1 ∈ c.V from hsub z.2)]
    rw [hfun]
    exact c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      fun z => hsub z.2)
  have hξ_map : ∀ (u : ℝ) (hu : u ∈ Set.Ioo (s - η) (s + η)),
      c.map (ξ u) = α u := by
    intro u hu
    rw [hξ_eq u hu]
    exact c.map_coord ⟨α u, hsub hu⟩
  have hξ_inj : InjOn ξ (Set.Ioo (s - η) (s + η)) := by
    intro u hu v hv huv
    exact hinj (by rw [← hξ_map u hu, ← hξ_map v hv, huv])
  have hsI : s ∈ Set.Ioo (s - η) (s + η) := ⟨by linarith, by linarith⟩
  have hξs : ξ s = 0 := by
    rw [hξ_eq s hsI]
    have : c.map (c.coord ⟨α s, hsub hsI⟩) = c.map 0 := by
      rw [c.map_coord ⟨α s, hsub hsI⟩, c.map_zero]
    exact c.injective_map this
  have hsub2 : Set.Icc (s - η / 2) (s + η / 2) ⊆ Set.Ioo (s - η) (s + η) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hξ_cont2 : ContinuousOn ξ (Set.Icc (s - η / 2) (s + η / 2)) := hξ_cont.mono hsub2
  have hξ_inj2 : InjOn ξ (Set.Icc (s - η / 2) (s + η / 2)) := hξ_inj.mono hsub2
  have hab2 : s - η / 2 ≤ s + η / 2 := by linarith
  have hmemA : s - η / 2 ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨le_refl _, by linarith⟩
  have hmemS : s ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨by linarith, by linarith⟩
  have hmemB : s + η / 2 ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨by linarith, le_refl _⟩
  have hsub2W : Set.Ioo (s - η / 2) (s + η / 2) ⊆ W :=
    fun u hu => hsubW (hsub2 ⟨hu.1.le, hu.2.le⟩)
  obtain hmono | hanti := ContinuousOn.strictMonoOn_of_injOn_Icc' hab2 hξ_cont2 hξ_inj2
  · have h1 : ξ (s - η / 2) < 0 := by
      have hlt : s - η / 2 < s := by linarith
      have := hmono hmemA hmemS hlt
      rwa [hξs] at this
    have h2 : 0 < ξ (s + η / 2) := by
      have hlt : s < s + η / 2 := by linarith
      have := hmono hmemS hmemB hlt
      rwa [hξs] at this
    have himg := ContinuousOn.image_Ioo_of_strictMonoOn (a := s - η / 2) (b := s + η / 2)
      hab2 hξ_cont2 hmono
    set ε : ℝ := min (-(ξ (s - η / 2))) (ξ (s + η / 2)) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; exact lt_min (by linarith) (by linarith)
    have hA : ξ (s - η / 2) ≤ -ε := by
      rw [hεdef]
      have := min_le_left (-(ξ (s - η / 2))) (ξ (s + η / 2))
      linarith
    have hB : ε ≤ ξ (s + η / 2) := by
      rw [hεdef]; exact min_le_right _ _
    refine ⟨ε, hεpos, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    have hw' : w ∈ Set.Ioo (ξ (s - η / 2)) (ξ (s + η / 2)) :=
      ⟨by linarith [hw.1, hA], by linarith [hw.2, hB]⟩
    rw [← himg] at hw'
    obtain ⟨u, hu, hueq⟩ := hw'
    exact ⟨u, hsub2W ⟨hu.1, hu.2⟩, by rw [← hueq, hξ_map u (hsub2 ⟨hu.1.le, hu.2.le⟩)]⟩
  · have h1 : ξ (s + η / 2) < 0 := by
      have hlt : s < s + η / 2 := by linarith
      have := hanti hmemS hmemB hlt
      rwa [hξs] at this
    have h2 : 0 < ξ (s - η / 2) := by
      have hlt : s - η / 2 < s := by linarith
      have := hanti hmemA hmemS hlt
      rwa [hξs] at this
    have himg := ContinuousOn.image_Ioo_of_strictAntiOn (a := s - η / 2) (b := s + η / 2)
      hab2 hξ_cont2 hanti
    set ε : ℝ := min (-(ξ (s + η / 2))) (ξ (s - η / 2)) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; exact lt_min (by linarith) (by linarith)
    have hA : ξ (s + η / 2) ≤ -ε := by
      rw [hεdef]
      have := min_le_left (-(ξ (s + η / 2))) (ξ (s - η / 2))
      linarith
    have hB : ε ≤ ξ (s - η / 2) := by
      rw [hεdef]; exact min_le_right _ _
    refine ⟨ε, hεpos, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    have hw' : w ∈ Set.Ioo (ξ (s + η / 2)) (ξ (s - η / 2)) :=
      ⟨by linarith [hw.1, hB], by linarith [hw.2, hA]⟩
    rw [← himg] at hw'
    obtain ⟨u, hu, hueq⟩ := hw'
    exact ⟨u, hsub2W ⟨hu.1, hu.2⟩, by rw [← hueq, hξ_map u (hsub2 ⟨hu.1.le, hu.2.le⟩)]⟩

/-- **An embedded arc in a locally-arc space is an open map.** -/
theorem isOpenMap_of_injective_continuous [T2Space X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α) : IsOpenMap α := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨s, hsW, rfl⟩
  obtain ⟨ε, hε, hsub⟩ := chart_interval_subset_image H hcont hinj hW hsW
  refine Filter.mem_of_superset ?_ hsub
  refine (isOpen_chartMap_Ioo (Work.Smooth.SphereJordan.chartOf H (α s)) ε).mem_nhds ?_
  exact ⟨0, ⟨by linarith, by linarith⟩, (Work.Smooth.SphereJordan.chartOf H (α s)).map_zero⟩

/-- **The closure of a half-line tail: the tail plus its limit.** -/
theorem closure_image_Ici_union [T2Space X] {α : ℝ → X} {p : X} (hcont : Continuous α)
    (htop : Filter.Tendsto α Filter.atTop (nhds p)) (t : ℝ) :
    closure (α '' Set.Ici t) = α '' Set.Ici t ∪ {p} := by
  refine subset_antisymm ?_ (by
    intro x hx
    rcases hx with hx | rfl
    · exact subset_closure hx
    · rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (htop.eventually hO)
      exact ⟨α (max T t), hT _ (le_max_left T t), ⟨max T t, le_max_right T t, rfl⟩⟩)
  intro x hx
  by_cases hx' : x ∈ α '' Set.Ici t
  · exact Or.inl hx'
  · refine Or.inr ?_
    by_contra hxp
    have hxne : x ≠ p := by simpa [Set.mem_singleton_iff] using hxp
    obtain ⟨u, v, hu, hv, hxu, hpv, hdisj⟩ := T2Space.t2 hxne
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (htop.eventually (hv.mem_nhds hpv))
    have hTt : T ≤ max T t := le_max_left T t
    have htt : t ≤ max T t := le_max_right T t
    have hsub : α '' Set.Ici (max T t) ⊆ v := fun y ⟨s, hs, hys⟩ =>
      hys ▸ hT s (le_trans hTt hs)
    have hcl : closure (α '' Set.Ici (max T t)) ⊆ closure v :=
      closure_mono hsub
    have hxclv : x ∉ closure v := by
      intro hxv'
      obtain ⟨z, hzu, hzv⟩ := mem_closure_iff_nhds.mp hxv' u (hu.mem_nhds hxu)
      exact (Set.disjoint_left.mp hdisj hzu) hzv
    have hIcc : IsClosed (α '' Set.Icc t (max T t)) := (isCompact_Icc.image hcont).isClosed
    have h1 : Set.Ici t = Set.Ici (max T t) ∪ Set.Icc t (max T t) := by
      ext s
      simp only [Set.mem_union, Set.mem_Ici, Set.mem_Icc]
      constructor
      · intro hs
        rcases lt_or_ge s (max T t) with h | h
        · exact Or.inr ⟨hs, h.le⟩
        · exact Or.inl h
      · rintro (h | h)
        · exact le_trans htt h
        · exact h.1
    have hdecomp : α '' Set.Ici t = α '' Set.Ici (max T t) ∪ α '' Set.Icc t (max T t) := by
      rw [h1, Set.image_union]
    rw [hdecomp, closure_union] at hx
    rcases hx with hx | hx
    · exact hxclv (hcl hx)
    · have hxIcc : x ∈ α '' Set.Icc t (max T t) :=
        hIcc.closure_subset_iff.mpr (subset_refl _) hx
      exact hx' (by rw [hdecomp]; exact Or.inr hxIcc)

/-- **The closure of a half-line tail: the tail plus its limit** (mirror image). -/
theorem closure_image_Iic_union [T2Space X] {α : ℝ → X} {q : X} (hcont : Continuous α)
    (hbot : Filter.Tendsto α Filter.atBot (nhds q)) (t : ℝ) :
    closure (α '' Set.Iic t) = α '' Set.Iic t ∪ {q} := by
  have hβ : Filter.Tendsto (fun s : ℝ => α (-s)) Filter.atTop (nhds q) :=
    hbot.comp tendsto_neg_atTop_atBot
  have h := closure_image_Ici_union (α := fun s : ℝ => α (-s)) (p := q)
    (hcont.comp continuous_neg) hβ (-t)
  have hset : (fun s : ℝ => α (-s)) '' Set.Ici (-t) = α '' Set.Iic t := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨-s, by simp only [Set.mem_Ici] at hs; simp only [Set.mem_Iic]; linarith, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨-s, by simp only [Set.mem_Iic] at hs; simp only [Set.mem_Ici]; linarith, by simp⟩
  rw [hset] at h
  exact h

/-- **The closure of the range of an arc is the range together with the two ends.** -/
theorem closure_range_eq_ends [T2Space X] {α : ℝ → X} {p q : X} (hcont : Continuous α)
    (htop : Filter.Tendsto α Filter.atTop (nhds p)) (hbot : Filter.Tendsto α Filter.atBot (nhds q)) :
    closure (Set.range α) = Set.range α ∪ {p, q} := by
  have hset : Set.range α = α '' Set.Ici 0 ∪ α '' Set.Iic 0 := by
    rw [← Set.image_union, Set.Ici_union_Iic, Set.image_univ]
  rw [hset, closure_union, closure_image_Ici_union hcont htop 0,
    closure_image_Iic_union hcont hbot 0]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

/-- **The frontier of the range of an arc lies in its two ends.** -/
theorem frontier_range_subset_ends [T2Space X] (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {α : ℝ → X} {p q : X} (hcont : Continuous α) (hinj : Function.Injective α)
    (htop : Filter.Tendsto α Filter.atTop (nhds p)) (hbot : Filter.Tendsto α Filter.atBot (nhds q)) :
    frontier (Set.range α) ⊆ {p, q} := by
  have hopen : IsOpen (Set.range α) := isOpen_range_of_injective_continuous H hcont hinj
  intro x hx
  have hxc : x ∈ closure (Set.range α) := hx.1
  rw [closure_range_eq_ends hcont htop hbot] at hxc
  have hxnot : x ∉ Set.range α := by
    intro hxr
    exact hx.2 (by rwa [hopen.interior_eq])
  rcases hxc with hxr | hxr
  · exact absurd hxr hxnot
  · exact hxr

/-- **If both ends of an embedded arc coincide, the space is a circle.** -/
theorem exists_circle_param_of_ends_eq [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {α : ℝ → X} {p : X} (hcont : Continuous α) (hinj : Function.Injective α)
    (hp : p ∉ Set.range α) (htop : Filter.Tendsto α Filter.atTop (nhds p))
    (hbot : Filter.Tendsto α Filter.atBot (nhds p)) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ := by
  have hUopen : IsOpen (Set.range α) := isOpen_range_of_injective_continuous H hcont hinj
  have hclosed : IsClosed (Set.range α ∪ {p}) := isClosed_range_union_of_tendsto hcont htop hbot
  have hpint : p ∈ interior (Set.range α ∪ {p}) := by
    obtain ⟨hIoi, hIio⟩ :=
      germCoveredBoth (Work.Smooth.SphereJordan.chartOf H p) hcont hinj hp htop hbot
    have hVsub : (Work.Smooth.SphereJordan.chartOf H p).V ⊆ Set.range α ∪ {p} := by
      intro y hy
      have hy' : y ∈ Set.range (Work.Smooth.SphereJordan.chartOf H p).map := by
        rw [Work.Smooth.SphereJordan.ArcChart.range_map]; exact hy
      obtain ⟨v, hv⟩ := hy'
      rcases lt_trichotomy v 0 with h | h | h
      · obtain ⟨s, hs⟩ := hIio ⟨v, h, rfl⟩
        exact Or.inl ⟨s, by rw [hs, hv]⟩
      · refine Or.inr ?_
        simp only [Set.mem_singleton_iff]
        rw [← hv, h, Work.Smooth.SphereJordan.ArcChart.map_zero]
      · obtain ⟨s, hs⟩ := hIoi ⟨v, h, rfl⟩
        exact Or.inl ⟨s, by rw [hs, hv]⟩
    exact interior_maximal hVsub (Work.Smooth.SphereJordan.ArcChart.isOpen_V _)
      (Work.Smooth.SphereJordan.ArcChart.mem_V _)
  have hopen : IsOpen (Set.range α ∪ {p}) := by
    have hEq : Set.range α ∪ {p} = Set.range α ∪ interior (Set.range α ∪ {p}) := by
      ext x
      constructor
      · rintro (h | rfl)
        · exact Or.inl h
        · exact Or.inr hpint
      · rintro (h | h)
        · exact Or.inl h
        · exact interior_subset h
    rw [hEq]
    exact hUopen.union isOpen_interior
  have hne : (Set.range α ∪ {p}).Nonempty := ⟨α 0, Or.inl ⟨0, rfl⟩⟩
  have huniv : Set.range α ∪ {p} = Set.univ :=
    (isClopen_iff.mp (⟨hclosed, hopen⟩ : IsClopen (Set.range α ∪ {p}))).resolve_left hne.ne_empty
  exact localArcExistsCircleParamOfTendsto hcont hinj htop hbot hp huniv

end

end Work.Smooth.SphereJordan.LocalArc
