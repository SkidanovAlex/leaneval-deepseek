import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Limit

/-!
# The local branch of an embedded arc

For an injective continuous arc `α : ℝ → X` and an arc chart `c` at a point `α s` of its range,
the chart coordinate `c.coord ∘ α` is strictly monotone near `s`; consequently the chart
neighbourhood of `α s` is *covered* by the arc, and `α` admits a local inverse there.  This is
the local form of "an embedded arc fills a neighbourhood of each of its points".

The main outputs are `local_branch` (a quantitative neighbourhood statement) and
`no_self_limit` (an embedded arc in a locally-arc Hausdorff space cannot have a point of its own
range as a limit point of its tail).
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The image of an open interval under an arc chart is open. -/
lemma isOpen_chartMap_Ioo {y : X} (c : ArcChart X y) (δ : ℝ) : IsOpen (c.map '' Set.Ioo (-δ) δ) := by
  have h1 : c.map '' Set.Ioo (-δ) δ = (Subtype.val : c.V → X) '' (c.homeo '' Set.Ioo (-δ) δ) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨c.homeo t, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [h1]
  exact c.isOpen_V.isOpenMap_subtype_val _ (c.homeo.isOpenMap _ isOpen_Ioo)

/-- **The local branch of an embedded arc.**  Let `α : ℝ → X` be injective and continuous and let
`c` be an arc chart at `α s`.  Then there are `η, ε > 0` such that

* every point of `c.map '' Ioo (-ε) ε` lies in the range of `α`, and
* if `α t` lies in `c.map '' Ioo (-ε) ε`, then `t ∈ Ioo (s - η) (s + η)`.

In particular the chart parametrisation restricts to a homeomorphism onto its image. -/
theorem local_branch {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α)
    (s : ℝ) (c : ArcChart X (α s)) :
    ∃ (η : ℝ) (ε : ℝ), 0 < η ∧ 0 < ε ∧
      (∀ v ∈ Set.Ioo (-ε) ε, c.map v ∈ Set.range α) ∧
      (∀ t : ℝ, α t ∈ c.map '' Set.Ioo (-ε) ε → t ∈ Set.Ioo (s - η) (s + η)) := by
  classical
  have hsV : α s ∈ c.V := c.mem_V
  have hV : ∀ᶠ u in 𝓝 s, α u ∈ c.V := hcont.continuousAt (c.isOpen_V.mem_nhds hsV)
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp hV
  have hsub : Set.Ioo (s - η) (s + η) ⊆ α ⁻¹' c.V := by
    intro u hu
    exact hηsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  let ξ : ℝ → ℝ := fun u => if h : α u ∈ c.V then c.coord ⟨α u, h⟩ else 0
  have hξ_eq : ∀ (u : ℝ) (hu : u ∈ Set.Ioo (s - η) (s + η)),
      ξ u = c.coord ⟨α u, hsub hu⟩ := by
    intro u hu
    change (if h : α u ∈ c.V then c.coord ⟨α u, h⟩ else 0) = c.coord ⟨α u, hsub hu⟩
    rw [dif_pos (show α u ∈ c.V from hsub hu)]
  have hsub2 : Set.Icc (s - η / 2) (s + η / 2) ⊆ Set.Ioo (s - η) (s + η) := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hξ_cont2 : ContinuousOn ξ (Set.Icc (s - η / 2) (s + η / 2)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Set.domRestrict (Set.Icc (s - η / 2) (s + η / 2)) ξ =
        fun z : Set.Icc (s - η / 2) (s + η / 2) =>
          c.coord ⟨α z.1, hsub (hsub2 z.2)⟩ := by
      funext z
      change (if h : α z.1 ∈ c.V then c.coord ⟨α z.1, h⟩ else 0) =
        c.coord ⟨α z.1, hsub (hsub2 z.2)⟩
      rw [dif_pos (show α z.1 ∈ c.V from hsub (hsub2 z.2))]
    rw [hfun]
    exact c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      fun z => hsub (hsub2 z.2))
  have hξ_map : ∀ (u : ℝ) (hu : u ∈ Set.Ioo (s - η) (s + η)),
      c.map (ξ u) = α u := by
    intro u hu
    rw [hξ_eq u hu]
    exact c.map_coord ⟨α u, hsub hu⟩
  have hξ_inj2 : Set.InjOn ξ (Set.Icc (s - η / 2) (s + η / 2)) := by
    intro u hu v hv huv
    exact hinj (by rw [← hξ_map u (hsub2 hu), ← hξ_map v (hsub2 hv), huv])
  have hab2 : s - η / 2 ≤ s + η / 2 := by linarith
  have hsI : s ∈ Set.Ioo (s - η) (s + η) := ⟨by linarith, by linarith⟩
  have hξs : ξ s = 0 := by
    rw [hξ_eq s hsI]
    have : c.map (c.coord ⟨α s, hsub hsI⟩) = c.map 0 := by
      rw [c.map_coord ⟨α s, hsub hsI⟩, c.map_zero]
    exact c.injective_map this
  have hmemA : s - η / 2 ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨le_refl _, by linarith⟩
  have hmemS : s ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨by linarith, by linarith⟩
  have hmemB : s + η / 2 ∈ Set.Icc (s - η / 2) (s + η / 2) := ⟨by linarith, le_refl _⟩
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
    refine ⟨η, ε, hηpos, hεpos, ?_, ?_⟩
    · rintro v hv
      have hv' : v ∈ Set.Ioo (ξ (s - η / 2)) (ξ (s + η / 2)) :=
        ⟨by linarith [hv.1, hA], by linarith [hv.2, hB]⟩
      rw [← himg] at hv'
      obtain ⟨u, hu, hueq⟩ := hv'
      exact ⟨u, by rw [← hueq, hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu))]⟩
    · intro t ht
      obtain ⟨v, hv, hveq⟩ := ht
      have hv' : v ∈ Set.Ioo (ξ (s - η / 2)) (ξ (s + η / 2)) :=
        ⟨by linarith [hv.1, hA], by linarith [hv.2, hB]⟩
      rw [← himg] at hv'
      obtain ⟨u, hu, hueq⟩ := hv'
      have hαu : α u = α t := by
        rw [← hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu)), hueq, hveq]
      have hut : u = t := hinj hαu
      rw [hut] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
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
    refine ⟨η, ε, hηpos, hεpos, ?_, ?_⟩
    · rintro v hv
      have hv' : v ∈ Set.Ioo (ξ (s + η / 2)) (ξ (s - η / 2)) :=
        ⟨by linarith [hv.1, hB], by linarith [hv.2, hA]⟩
      rw [← himg] at hv'
      obtain ⟨u, hu, hueq⟩ := hv'
      exact ⟨u, by rw [← hueq, hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu))]⟩
    · intro t ht
      obtain ⟨v, hv, hveq⟩ := ht
      have hv' : v ∈ Set.Ioo (ξ (s + η / 2)) (ξ (s - η / 2)) :=
        ⟨by linarith [hv.1, hB], by linarith [hv.2, hA]⟩
      rw [← himg] at hv'
      obtain ⟨u, hu, hueq⟩ := hv'
      have hαu : α u = α t := by
        rw [← hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu)), hueq, hveq]
      have hut : u = t := hinj hαu
      rw [hut] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- **An embedded arc has no self-limit.**  If `α : ℝ → X` is injective and continuous and a point
`α t₀` of its range is a limit point of every tail `α '' Ici s`, then we get a contradiction. -/
theorem no_self_limit [T2Space X] {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α)
    {t₀ : ℝ} (c : ArcChart X (α t₀)) (h : ∀ s : ℝ, α t₀ ∈ closure (α '' Set.Ici s)) : False := by
  obtain ⟨η, ε, hη, hε, hfill, hbound⟩ := local_branch hcont hinj t₀ c
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨T, hT⟩ := localArc_eventually_mem_chart_interval c hcont hinj h hε2
  set t : ℝ := max T (t₀ + η) with ht
  have htT : T ≤ t := le_max_left _ _
  have htη : t₀ + η ≤ t := le_max_right _ _
  have hmem : α t ∈ c.map '' Set.Ioo (-ε) ε :=
    Set.image_mono (Set.Ioo_subset_Ioo (by linarith) (by linarith)) (hT t htT)
  have := hbound t hmem
  linarith [this.2]

/-- **The range of an embedded arc is open**, in a locally-arc space. -/
theorem isOpen_range_of_injective_continuous (H : IsLocallyArc X) {α : ℝ → X}
    (hcont : Continuous α) (hinj : Function.Injective α) : IsOpen (Set.range α) := by
  choose! ε hε hsub using fun t : ℝ => localArc_fills_neighbourhood hcont hinj t (chartOf H (α t))
  have hrange : Set.range α = ⋃ t, (chartOf H (α t)).map '' Set.Ioo (-ε t) (ε t) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_iUnion.mpr ⟨t, ⟨0, ⟨by linarith [hε t], by linarith [hε t]⟩,
        (chartOf H (α t)).map_zero⟩⟩
    · intro hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      exact hsub t ht
  rw [hrange]
  exact isOpen_iUnion (fun t => isOpen_chartMap_Ioo (chartOf H (α t)) (ε t))

end

end Work.Smooth.SphereJordan.LocalArc
