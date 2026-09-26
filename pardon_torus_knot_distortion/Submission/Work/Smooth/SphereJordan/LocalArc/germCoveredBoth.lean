import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen

/-!
# An embedded arc whose two ends converge to a point fills both germs of a chart there

Let `X` be compact Hausdorff, `p : X`, `c : ArcChart X p` a chart at `p`, and `α : ℝ → X` an
injective continuous arc with `p ∉ range α` and `α t → p` as `t → ±∞`.  Then `α` covers *both*
halves of the chart at `p`: `c.map '' Ioi 0 ⊆ range α` and `c.map '' Iio 0 ⊆ range α`.

The proof: write `C` for the set of chart coordinates `w` with `c.map w ∈ range α`.

* `C` is open: if `c.map w = α s`, recentring the chart at `w` and applying `local_branch` shows
  that a whole chart interval around `w` is covered by `α`.
* `C ∪ {0}` is closed: it is the preimage under `c.map` of `range α ∪ {p}`, and the latter is
  compact — it is the image of the one-point compactification `OnePoint ℝ` under the extension of
  `α` given by `tendsto` at `±∞`.
* The two tails of `α` map into `C` and have opposite signs: if both lay on the same side of `0`,
  the two tail images would be two ord-connected subsets of `(0,∞)` (respectively `(-∞,0)`)
  accumulating at `0` and hence would meet, contradicting injectivity.
* Consequently `C ∩ Ioi 0` is a nonempty clopen subset of the connected space `Ioi 0`, so equals
  `Ioi 0`; likewise `C ∩ Iio 0 = Iio 0`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **`range α ∪ {p}` is closed.**  An injective continuous arc on `ℝ` whose two ends converge to
`p` extends continuously to the one-point compactification `OnePoint ℝ`; the image of that compact
space is the compact set `range α ∪ {p}`, which is therefore closed (in a Hausdorff space). -/
lemma isClosed_range_union_of_tendsto [CompactSpace X] {p : X} {α : ℝ → X}
    (hcont : Continuous α) (htop : Tendsto α atTop (𝓝 p)) (hbot : Tendsto α atBot (𝓝 p)) :
    IsClosed (Set.range α ∪ {p}) := by
  have hco : Tendsto α (coclosedCompact ℝ) (𝓝 p) := by
    have h1 : Tendsto α (cocompact ℝ) (𝓝 p) := by
      rw [cocompact_eq_atBot_atTop]
      exact hbot.sup htop
    rwa [coclosedCompact_eq_cocompact]
  let f : OnePoint ℝ → X := fun x => x.elim p α
  have hf : Continuous f := by
    rw [OnePoint.continuous_iff]
    exact ⟨hco, hcont⟩
  have hrange : Set.range f = Set.range α ∪ {p} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rcases z with - | t
      · exact Or.inr rfl
      · exact Or.inl ⟨t, rfl⟩
    · rintro (⟨t, rfl⟩ | rfl)
      · exact ⟨(t : OnePoint ℝ), rfl⟩
      · exact ⟨OnePoint.infty, rfl⟩
  rw [← hrange]
  exact (isCompact_range hf).isClosed

/-- Two ord-connected subsets of `(0,∞)`, respectively of `(-∞,0)`, whose closures both contain
`0`, must intersect. -/
lemma nonempty_inter_of_ordConnected_of_mem_closure_zero {A B : Set ℝ}
    (hA : A.OrdConnected) (hB : B.OrdConnected) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (h0A : (0 : ℝ) ∈ closure A) (h0B : (0 : ℝ) ∈ closure B)
    (hside : (A ⊆ Set.Ioi 0 ∧ B ⊆ Set.Ioi 0) ∨ (A ⊆ Set.Iio 0 ∧ B ⊆ Set.Iio 0)) :
    (A ∩ B).Nonempty := by
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  have key : ∀ {C : Set ℝ}, (0 : ℝ) ∈ closure C → ∀ c < 0, ∃ c' ∈ C, c < c' := by
    intro C hC c hc
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hC (Set.Ioi c) (Ioi_mem_nhds hc)
    exact ⟨y, hy2, hy1⟩
  have key' : ∀ {C : Set ℝ}, (0 : ℝ) ∈ closure C → ∀ c > 0, ∃ c' ∈ C, c' < c := by
    intro C hC c hc
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hC (Set.Iio c) (Iio_mem_nhds hc)
    exact ⟨y, hy2, hy1⟩
  rcases hside with ⟨hAp, hBp⟩ | ⟨hAn, hBn⟩
  · have ha0 : 0 < a := hAp ha
    have hb0 : 0 < b := hBp hb
    have hmin0 : 0 < min a b := lt_min ha0 hb0
    set t : ℝ := min a b / 2 with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have hta : t ≤ a := by rw [ht]; have := min_le_left a b; linarith
    have htb : t ≤ b := by rw [ht]; have := min_le_right a b; linarith
    obtain ⟨a', ha'A, ha't⟩ := key' h0A t ht0
    obtain ⟨b', hb'B, hb't⟩ := key' h0B t ht0
    exact ⟨t, hA.out ha'A ha ⟨ha't.le, hta⟩, hB.out hb'B hb ⟨hb't.le, htb⟩⟩
  · have ha0 : a < 0 := hAn ha
    have hb0 : b < 0 := hBn hb
    have hmax0 : max a b < 0 := max_lt ha0 hb0
    set t : ℝ := max a b / 2 with ht
    have ht0 : t < 0 := by rw [ht]; linarith
    have hta : a ≤ t := by rw [ht]; have := le_max_left a b; linarith
    have htb : b ≤ t := by rw [ht]; have := le_max_right a b; linarith
    obtain ⟨a', ha'A, ha't⟩ := key h0A t ht0
    obtain ⟨b', hb'B, hb't⟩ := key h0B t ht0
    exact ⟨t, hA.out ha ha'A ⟨hta, ha't.le⟩, hB.out hb hb'B ⟨htb, hb't.le⟩⟩

/-- If `C` is open and `C ∪ {0}` is closed, then either `C` misses `(0,∞)` entirely or contains
all of it. -/
lemma Ioi_subset_of_isOpen_of_isClosed_union_zero {C : Set ℝ} (hopen : IsOpen C)
    (hclosed : IsClosed (C ∪ {0})) (hne : (C ∩ Set.Ioi 0).Nonempty) : Set.Ioi (0:ℝ) ⊆ C := by
  have hpre : PreconnectedSpace ↥(Set.Ioi (0:ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioi
  have hcl : IsClopen {x : ↥(Set.Ioi (0:ℝ)) | (x:ℝ) ∈ C} := by
    refine ⟨?_, hopen.preimage continuous_subtype_val⟩
    rw [← isOpen_compl_iff]
    have hcompl : {x : ↥(Set.Ioi (0:ℝ)) | (x:ℝ) ∈ C}ᶜ = Subtype.val ⁻¹' (C ∪ {0})ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_union,
        Set.mem_singleton_iff, not_or]
      exact ⟨fun hx => ⟨hx, ne_of_gt x.2⟩, fun hx => hx.1⟩
    rw [hcompl]
    exact hclosed.isOpen_compl.preimage continuous_subtype_val
  have hne' : {x : ↥(Set.Ioi (0:ℝ)) | (x:ℝ) ∈ C}.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨⟨a, ha.2⟩, ha.1⟩
  have huniv : {x : ↥(Set.Ioi (0:ℝ)) | (x:ℝ) ∈ C} = Set.univ :=
    ((@isClopen_iff _ _ hpre _).mp hcl).resolve_left hne'.ne_empty
  intro w hw
  have h : (⟨w, hw⟩ : ↥(Set.Ioi (0:ℝ))) ∈ {x : ↥(Set.Ioi (0:ℝ)) | (x:ℝ) ∈ C} := by
    rw [huniv]
    exact Set.mem_univ _
  exact h

/-- The mirror image of `Ioi_subset_of_isOpen_of_isClosed_union_zero` for `(-∞,0)`. -/
lemma Iio_subset_of_isOpen_of_isClosed_union_zero {C : Set ℝ} (hopen : IsOpen C)
    (hclosed : IsClosed (C ∪ {0})) (hne : (C ∩ Set.Iio 0).Nonempty) : Set.Iio (0:ℝ) ⊆ C := by
  have hpre : PreconnectedSpace ↥(Set.Iio (0:ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Iio
  have hcl : IsClopen {x : ↥(Set.Iio (0:ℝ)) | (x:ℝ) ∈ C} := by
    refine ⟨?_, hopen.preimage continuous_subtype_val⟩
    rw [← isOpen_compl_iff]
    have hcompl : {x : ↥(Set.Iio (0:ℝ)) | (x:ℝ) ∈ C}ᶜ = Subtype.val ⁻¹' (C ∪ {0})ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_union,
        Set.mem_singleton_iff, not_or]
      exact ⟨fun hx => ⟨hx, ne_of_lt x.2⟩, fun hx => hx.1⟩
    rw [hcompl]
    exact hclosed.isOpen_compl.preimage continuous_subtype_val
  have hne' : {x : ↥(Set.Iio (0:ℝ)) | (x:ℝ) ∈ C}.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨⟨a, ha.2⟩, ha.1⟩
  have huniv : {x : ↥(Set.Iio (0:ℝ)) | (x:ℝ) ∈ C} = Set.univ :=
    ((@isClopen_iff _ _ hpre _).mp hcl).resolve_left hne'.ne_empty
  intro w hw
  have h : (⟨w, hw⟩ : ↥(Set.Iio (0:ℝ))) ∈ {x : ↥(Set.Iio (0:ℝ)) | (x:ℝ) ∈ C} := by
    rw [huniv]
    exact Set.mem_univ _
  exact h

theorem germCoveredBoth {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {p : X} (c : Work.Smooth.SphereJordan.ArcChart X p) {α : ℝ → X} (hcont : Continuous α)
    (hinj : Function.Injective α) (hp : p ∉ Set.range α)
    (htop : Filter.Tendsto α Filter.atTop (nhds p)) (hbot : Filter.Tendsto α Filter.atBot (nhds p)) :
    c.map '' Set.Ioi 0 ⊆ Set.range α ∧ c.map '' Set.Iio 0 ⊆ Set.range α := by
  classical
  have hKcl : IsClosed (Set.range α ∪ {p}) := isClosed_range_union_of_tendsto hcont htop hbot
  set C : Set ℝ := c.map ⁻¹' Set.range α with hCdef
  have hmap_open : IsOpenMap c.map := fun O hO => by
    have h1 : c.map '' O = (Subtype.val : c.V → X) '' (c.homeo '' O) := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨c.homeo t, ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, rfl⟩
    rw [h1]
    exact c.isOpen_V.isOpenMap_subtype_val _ (c.homeo.isOpenMap _ hO)
  -- ## `C` is open
  have hCopen : IsOpen C := by
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    obtain ⟨s, hs⟩ := hw
    have hsV : α s ∈ c.V := hs ▸ c.map_mem w
    let c' : Work.Smooth.SphereJordan.ArcChart X (α s) :=
      { V := c.V
        isOpen_V := c.isOpen_V
        mem_V := hsV
        homeo := (Homeomorph.addRight w).trans c.homeo
        homeo_zero := by
          apply Subtype.ext
          show (c.homeo ((Homeomorph.addRight w) 0) : X) = α s
          simp only [Homeomorph.coe_addRight, zero_add]
          exact hs.symm }
    obtain ⟨ε, hεpos, hεsub⟩ := localArc_fills_neighbourhood hcont hinj s c'
    have hcm : ∀ t : ℝ, c'.map t = c.map (t + w) := by
      intro t
      show ((Homeomorph.addRight w).trans c.homeo t : X) = c.map (t + w)
      rw [Homeomorph.trans_apply]
      rfl
    refine ⟨Set.Ioo (w - ε) (w + ε), ?_, isOpen_Ioo, ⟨by linarith, by linarith⟩⟩
    intro v hv
    have hv' : v - w ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo] at hv ⊢
      constructor <;> linarith [hv.1, hv.2]
    have h1 : c.map (v - w + w) ∈ Set.range α := by
      have h2 : c'.map (v - w) ∈ Set.range α := hεsub ⟨v - w, hv', rfl⟩
      rwa [hcm (v - w)] at h2
    rw [hCdef]
    simpa [sub_add_cancel] using h1
  -- ## `C ∪ {0}` is closed
  have hCclosed : IsClosed (C ∪ {0}) := by
    have h1 : C ∪ {0} = c.map ⁻¹' (Set.range α ∪ {p}) := by
      ext t
      rw [hCdef]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · refine Or.inr ?_
          rw [Set.mem_singleton_iff]
          rw [Set.mem_singleton_iff] at h
          rw [h, c.map_zero]
      · rintro (h | h)
        · exact Or.inl h
        · refine Or.inr ?_
          rw [Set.mem_singleton_iff]
          rw [Set.mem_singleton_iff] at h
          exact c.injective_map (by rw [h, c.map_zero])
    rw [h1]
    exact hKcl.preimage c.continuous_map
  -- ## the two tails of `α`
  obtain ⟨T₀, hT₀⟩ : ∃ T : ℝ, ∀ s ≥ T, α s ∈ c.V :=
    Filter.eventually_atTop.mp (htop.eventually (c.isOpen_V.mem_nhds c.mem_V))
  obtain ⟨S₀, hS₀⟩ : ∃ S : ℝ, ∀ s ≤ S, α s ∈ c.V :=
    Filter.eventually_atBot.mp (hbot.eventually (c.isOpen_V.mem_nhds c.mem_V))
  set T : ℝ := max T₀ 1 with hTdef
  set S : ℝ := max (-S₀) 1 with hSdef
  have hT1 : (1:ℝ) ≤ T := le_max_right T₀ 1
  have hS1 : (1:ℝ) ≤ S := le_max_right (-S₀) 1
  have hT : ∀ s ≥ T, α s ∈ c.V := fun s hs => hT₀ s (le_trans (le_max_left T₀ 1) hs)
  have hSp : ∀ s ≤ -S, α s ∈ c.V := fun s hs =>
    hS₀ s (le_trans hs (by have := le_max_left (-S₀) (1:ℝ); linarith))
  let φp : ↥(Set.Ici T) → ℝ := fun s => c.coord ⟨α s.1, hT s.1 s.2⟩
  let φm : ↥(Set.Iic (-S)) → ℝ := fun s => c.coord ⟨α s.1, hSp s.1 s.2⟩
  have hφp_cont : Continuous φp :=
    c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      (fun s => hT s.1 s.2))
  have hφm_cont : Continuous φm :=
    c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      (fun s => hSp s.1 s.2))
  have hφp_mem : ∀ s ∈ φp '' Set.univ, s ∈ C := by
    rintro s ⟨q, -, rfl⟩
    rw [hCdef]
    exact ⟨q.1, (c.map_coord ⟨α q.1, hT q.1 q.2⟩).symm⟩
  have hφm_mem : ∀ s ∈ φm '' Set.univ, s ∈ C := by
    rintro s ⟨q, -, rfl⟩
    rw [hCdef]
    exact ⟨q.1, (c.map_coord ⟨α q.1, hSp q.1 q.2⟩).symm⟩
  have hφp_ne : ∀ q, φp q ≠ 0 := by
    intro q hq
    have h2 : c.map (φp q) = α q.1 := c.map_coord _
    have h1 : α q.1 = p := by rw [← h2, hq, c.map_zero]
    exact hp ⟨q.1, h1⟩
  have hφm_ne : ∀ q, φm q ≠ 0 := by
    intro q hq
    have h2 : c.map (φm q) = α q.1 := c.map_coord _
    have h1 : α q.1 = p := by rw [← h2, hq, c.map_zero]
    exact hp ⟨q.1, h1⟩
  have hpreT : PreconnectedSpace ↥(Set.Ici T) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  have hpreS : PreconnectedSpace ↥(Set.Iic (-S)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Iic
  have hφp_pre : IsPreconnected (φp '' Set.univ) :=
    (@isPreconnected_univ ↥(Set.Ici T) _ hpreT).image φp hφp_cont.continuousOn
  have hφm_pre : IsPreconnected (φm '' Set.univ) :=
    (@isPreconnected_univ ↥(Set.Iic (-S)) _ hpreS).image φm hφm_cont.continuousOn
  have hφp_closure : (0:ℝ) ∈ closure (φp '' Set.univ) := by
    rw [mem_closure_iff_nhds]
    intro O hO
    have hmapO : c.map '' O ∈ nhds p := by
      have h1 : c.map '' O ∈ nhds (c.map 0) := hmap_open.image_mem_nhds hO
      rwa [c.map_zero] at h1
    obtain ⟨T', hT'⟩ := Filter.eventually_atTop.mp (htop.eventually hmapO)
    obtain ⟨u, huO, hueq⟩ := hT' (max T T') (le_max_right T T')
    have hu : u = φp ⟨max T T', le_max_left T T'⟩ := by
      show u = c.coord ⟨α (max T T'), hT (max T T') (le_max_left T T')⟩
      rw [← c.coord_apply_map u]
      congr 1
      exact Subtype.ext hueq
    exact ⟨u, huO, by rw [hu]; exact Set.mem_image_of_mem φp (Set.mem_univ _)⟩
  have hφm_closure : (0:ℝ) ∈ closure (φm '' Set.univ) := by
    rw [mem_closure_iff_nhds]
    intro O hO
    have hmapO : c.map '' O ∈ nhds p := by
      have h1 : c.map '' O ∈ nhds (c.map 0) := hmap_open.image_mem_nhds hO
      rwa [c.map_zero] at h1
    obtain ⟨S', hS'⟩ := Filter.eventually_atBot.mp (hbot.eventually hmapO)
    obtain ⟨u, huO, hueq⟩ := hS' (min (-S) S') (min_le_right (-S) S')
    have hu : u = φm ⟨min (-S) S', min_le_left (-S) S'⟩ := by
      show u = c.coord ⟨α (min (-S) S'), hSp (min (-S) S') (min_le_left (-S) S')⟩
      rw [← c.coord_apply_map u]
      congr 1
      exact Subtype.ext hueq
    exact ⟨u, huO, by rw [hu]; exact Set.mem_image_of_mem φm (Set.mem_univ _)⟩
  -- ## the tails lie on opposite sides of `0`
  have hφp_sign : (φp '' Set.univ) ⊆ Set.Ioi 0 ∨ (φp '' Set.univ) ⊆ Set.Iio 0 :=
    IsPreconnected.subset_or_subset isOpen_Ioi isOpen_Iio
      (Set.disjoint_left.mpr fun x hx hx' => by
        simp only [Set.mem_Ioi] at hx
        simp only [Set.mem_Iio] at hx'
        linarith)
      (fun x hx => by
        obtain ⟨q, -, rfl⟩ := hx
        rcases lt_or_gt_of_ne (hφp_ne q) with h | h
        · exact Or.inr h
        · exact Or.inl h)
      hφp_pre
  have hφm_sign : (φm '' Set.univ) ⊆ Set.Ioi 0 ∨ (φm '' Set.univ) ⊆ Set.Iio 0 :=
    IsPreconnected.subset_or_subset isOpen_Ioi isOpen_Iio
      (Set.disjoint_left.mpr fun x hx hx' => by
        simp only [Set.mem_Ioi] at hx
        simp only [Set.mem_Iio] at hx'
        linarith)
      (fun x hx => by
        obtain ⟨q, -, rfl⟩ := hx
        rcases lt_or_gt_of_ne (hφm_ne q) with h | h
        · exact Or.inr h
        · exact Or.inl h)
      hφm_pre
  have hnot_same : ∀ (h1 : (φp '' Set.univ) ⊆ Set.Ioi 0) (h2 : (φm '' Set.univ) ⊆ Set.Ioi 0),
      False := by
    intro h1 h2
    obtain ⟨x, hxA, hxB⟩ := nonempty_inter_of_ordConnected_of_mem_closure_zero
      hφp_pre.ordConnected hφm_pre.ordConnected
      ⟨φp ⟨T, le_refl T⟩, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
      ⟨φm ⟨-S, le_refl (-S)⟩, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
      hφp_closure hφm_closure (Or.inl ⟨h1, h2⟩)
    obtain ⟨q, -, hq⟩ := hxA
    obtain ⟨q', -, hq'⟩ := hxB
    have hqx : c.coord ⟨α q.1, hT q.1 q.2⟩ = x := hq
    have hqx' : c.coord ⟨α q'.1, hSp q'.1 q'.2⟩ = x := hq'
    have h3 : α q.1 = α q'.1 := by
      have hA : α q.1 = c.map (c.coord ⟨α q.1, hT q.1 q.2⟩) :=
        (c.map_coord ⟨α q.1, hT q.1 q.2⟩).symm
      have hB : c.map (c.coord ⟨α q'.1, hSp q'.1 q'.2⟩) = α q'.1 :=
        c.map_coord ⟨α q'.1, hSp q'.1 q'.2⟩
      rw [hA, hqx, ← hB, hqx']
    have h4 : q.1 = q'.1 := hinj h3
    have h5 : (1:ℝ) ≤ q.1 := le_trans hT1 q.2
    have h6 : q'.1 ≤ -1 := le_trans q'.2 (by linarith [hS1])
    linarith
  have hnot_same' : ∀ (h1 : (φp '' Set.univ) ⊆ Set.Iio 0) (h2 : (φm '' Set.univ) ⊆ Set.Iio 0),
      False := by
    intro h1 h2
    obtain ⟨x, hxA, hxB⟩ := nonempty_inter_of_ordConnected_of_mem_closure_zero
      hφp_pre.ordConnected hφm_pre.ordConnected
      ⟨φp ⟨T, le_refl T⟩, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
      ⟨φm ⟨-S, le_refl (-S)⟩, Set.mem_image_of_mem _ (Set.mem_univ _)⟩
      hφp_closure hφm_closure (Or.inr ⟨h1, h2⟩)
    obtain ⟨q, -, hq⟩ := hxA
    obtain ⟨q', -, hq'⟩ := hxB
    have hqx : c.coord ⟨α q.1, hT q.1 q.2⟩ = x := hq
    have hqx' : c.coord ⟨α q'.1, hSp q'.1 q'.2⟩ = x := hq'
    have h3 : α q.1 = α q'.1 := by
      have hA : α q.1 = c.map (c.coord ⟨α q.1, hT q.1 q.2⟩) :=
        (c.map_coord ⟨α q.1, hT q.1 q.2⟩).symm
      have hB : c.map (c.coord ⟨α q'.1, hSp q'.1 q'.2⟩) = α q'.1 :=
        c.map_coord ⟨α q'.1, hSp q'.1 q'.2⟩
      rw [hA, hqx, ← hB, hqx']
    have h4 : q.1 = q'.1 := hinj h3
    have h5 : (1:ℝ) ≤ q.1 := le_trans hT1 q.2
    have h6 : q'.1 ≤ -1 := le_trans q'.2 (by linarith [hS1])
    linarith
  have hcase : ((φp '' Set.univ) ⊆ Set.Ioi 0 ∧ (φm '' Set.univ) ⊆ Set.Iio 0) ∨
      ((φp '' Set.univ) ⊆ Set.Iio 0 ∧ (φm '' Set.univ) ⊆ Set.Ioi 0) := by
    rcases hφp_sign with h1 | h1 <;> rcases hφm_sign with h2 | h2
    · exact (hnot_same h1 h2).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact (hnot_same' h1 h2).elim
  have hCpos : (C ∩ Set.Ioi 0).Nonempty := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨φp ⟨T, le_refl T⟩, hφp_mem _ (Set.mem_image_of_mem _ (Set.mem_univ _)),
        h1 (Set.mem_image_of_mem _ (Set.mem_univ _))⟩
    · exact ⟨φm ⟨-S, le_refl (-S)⟩, hφm_mem _ (Set.mem_image_of_mem _ (Set.mem_univ _)),
        h2 (Set.mem_image_of_mem _ (Set.mem_univ _))⟩
  have hCneg : (C ∩ Set.Iio 0).Nonempty := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨φm ⟨-S, le_refl (-S)⟩, hφm_mem _ (Set.mem_image_of_mem _ (Set.mem_univ _)),
        h2 (Set.mem_image_of_mem _ (Set.mem_univ _))⟩
    · exact ⟨φp ⟨T, le_refl T⟩, hφp_mem _ (Set.mem_image_of_mem _ (Set.mem_univ _)),
        h1 (Set.mem_image_of_mem _ (Set.mem_univ _))⟩
  have hIoi : Set.Ioi (0:ℝ) ⊆ C := Ioi_subset_of_isOpen_of_isClosed_union_zero hCopen hCclosed hCpos
  have hIio : Set.Iio (0:ℝ) ⊆ C := Iio_subset_of_isOpen_of_isClosed_union_zero hCopen hCclosed hCneg
  constructor
  · rintro y ⟨t, ht, rfl⟩
    simpa [hCdef] using hIoi ht
  · rintro y ⟨t, ht, rfl⟩
    simpa [hCdef] using hIio ht

end

end Work.Smooth.SphereJordan.LocalArc
