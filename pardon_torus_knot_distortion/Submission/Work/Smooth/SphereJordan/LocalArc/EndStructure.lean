import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Ends
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen
import Submission.Work.Smooth.SphereJordan.LocalArc.Branch

/-!
# The germ of an embedded arc at its end

Let `α : ℝ → X` be an injective continuous arc in a locally-arc Hausdorff space whose tails
converge to `p` (at `+∞`) and `q ≠ p` (at `-∞`).  Then, in any chart at `p`, the arc enters from
exactly one side: there is an interval `(-ε, ε)` of chart coordinates around `p` such that
`q` is not in the corresponding chart neighbourhood `W`, and one of the two halves
`W ∩ {coord < 0}`, `W ∩ {coord > 0}` does not meet the range of `α` at all.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **One side of a chart at an end of an arc is missed by the arc.** -/
theorem exists_chart_side_subset_compl
    (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α) {p q : X} (hpq : p ≠ q)
    (htop : Filter.Tendsto α Filter.atTop (nhds p)) (hbot : Filter.Tendsto α Filter.atBot (nhds q))
    (c : Work.Smooth.SphereJordan.ArcChart X p) :
    ∃ (ε : ℝ), 0 < ε ∧ q ∉ c.map '' Set.Ioo (-ε) ε ∧
      (c.map '' Set.Ioo (-ε) 0 ⊆ (Set.range α)ᶜ ∨
       c.map '' Set.Ioo 0 ε ⊆ (Set.range α)ᶜ) := by
  classical
  have hp : p ∉ Set.range α := by
    rintro ⟨t₀, ht₀⟩
    refine no_self_limit hcont hinj (α := α) (t₀ := t₀) (ht₀.symm ▸ c) ?_
    intro s
    rw [ht₀]
    exact (closure_image_Ici_union hcont htop s).ge (Or.inr (Set.mem_singleton_iff.mpr rfl))
  obtain ⟨ε, hεpos, hqcl⟩ : ∃ ε : ℝ, 0 < ε ∧ q ∉ c.map '' Set.Icc (-ε) ε := by
    by_cases hqV : q ∈ c.V
    · have hqr : q ∈ Set.range c.map := by
        rwa [Work.Smooth.SphereJordan.ArcChart.range_map]
      obtain ⟨d, hd⟩ := hqr
      have hdne : d ≠ 0 := fun h => hpq (by rw [← hd, h, c.map_zero])
      refine ⟨|d| / 2, by positivity, ?_⟩
      rintro ⟨v, hv, hveq⟩
      have hvd : v = d := c.injective_map (by rw [hveq, hd])
      rw [hvd] at hv
      have hle : |d| ≤ |d| / 2 := abs_le.mpr hv
      linarith [abs_pos.mpr hdne]
    · refine ⟨1, one_pos, ?_⟩
      rintro ⟨v, hv, hveq⟩
      exact hqV (hveq ▸ c.map_mem v)
  set W : Set X := c.map '' Set.Ioo (-ε) ε with hWdef
  have hqW : q ∉ W := fun h => hqcl (Set.image_mono Set.Ioo_subset_Icc_self h)
  have hWclosure : closure W = c.map '' Set.Icc (-ε) ε := by
    rw [hWdef]
    refine subset_antisymm ?_ ?_
    · refine closure_minimal ?_ (isCompact_Icc.image c.continuous_map).isClosed
      rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    · rw [← closure_Ioo (a := -ε) (b := ε) (by linarith)]
      exact image_closure_subset_closure_image c.continuous_map
  have hpW : p ∈ W := ⟨0, ⟨by linarith, by linarith⟩, c.map_zero⟩
  have hWopen : IsOpen W := isOpen_chartMap_Ioo c ε
  have hWV : W ⊆ c.V := by
    rintro z ⟨t, ht, rfl⟩
    exact c.map_mem t
  haveI hWpre : PreconnectedSpace ↥W := by
    refine isPreconnected_iff_preconnectedSpace.mp ?_
    rw [hWdef]
    exact (isPreconnected_Ioo (a := -ε) (b := ε)).image c.map c.continuous_map.continuousOn
  set S : Set ℝ := α ⁻¹' W with hSdef
  have hSopen : IsOpen S := hWopen.preimage hcont
  have hmS : ∀ t : ℝ, t ∈ S ↔ α t ∈ W := fun t => Iff.rfl
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ∀ t ∈ S, m ≤ t := by
    have hqcl' : q ∈ (closure W)ᶜ := by
      rw [Set.mem_compl_iff, hWclosure]
      exact hqcl
    have h : ∀ᶠ t in Filter.atBot, α t ∉ W :=
      (hbot.eventually (isClosed_closure.isOpen_compl.mem_nhds hqcl')).mono
        (fun t ht hW => ht (subset_closure hW))
    obtain ⟨m, hm⟩ := Filter.eventually_atBot.mp h
    exact ⟨m, fun t ht => by
      by_contra hcon
      exact hm t (le_of_lt (lt_of_not_ge hcon)) ht⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → t ∈ S := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (htop.eventually (hWopen.mem_nhds hpW))
    exact ⟨T, fun t ht => hT t ht⟩
  -- Every component of `S` is unbounded above.
  have hcomp : ∀ u ∈ S, ∀ N : ℝ, ∃ t ∈ connectedComponentIn S u, N ≤ t := by
    intro u hu N
    by_contra hcon
    push_neg at hcon
    set C : Set ℝ := connectedComponentIn S u with hCdef
    have hCsub : C ⊆ S := hCdef.symm ▸ connectedComponentIn_subset S u
    have huC : u ∈ C := hCdef.symm ▸ mem_connectedComponentIn hu
    have hCne : C.Nonempty := ⟨u, huC⟩
    have hCpre : IsPreconnected C := hCdef.symm ▸ isPreconnected_connectedComponentIn
    have hCord : C.OrdConnected := hCpre.ordConnected
    have hCopen : IsOpen C := hCdef.symm ▸ hSopen.connectedComponentIn
    have hCbddA : BddAbove C := ⟨N, fun t ht => (hcon t ht).le⟩
    have hCbddB : BddBelow C := ⟨m, fun t ht => hm t (hCsub ht)⟩
    set a : ℝ := sInf C with hadef
    set b : ℝ := sSup C with hbdef
    have ha_le : ∀ y ∈ C, a ≤ y := fun y hy => hadef.symm ▸ csInf_le hCbddB hy
    have hb_le : ∀ y ∈ C, y ≤ b := fun y hy => hbdef.symm ▸ le_csSup hCbddA hy
    have haC : a ∉ C := by
      intro haCin
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds haCin)
      have hmem : a - δ / 2 ∈ C :=
        hδsub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
      have : a ≤ a - δ / 2 := ha_le _ hmem
      linarith
    have hbC : b ∉ C := by
      intro hbCin
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds hbCin)
      have hmem : b + δ / 2 ∈ C :=
        hδsub (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
      have : b + δ / 2 ≤ b := hb_le _ hmem
      linarith
    have ha_closure : a ∈ closure C := by
      rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨δ, hδpos, hδO⟩ := Metric.mem_nhds_iff.mp hO
      have hex : ∃ y ∈ C, y < a + δ / 2 := by
        by_contra h
        push_neg at h
        have : a + δ / 2 ≤ a := hadef.symm ▸ le_csInf hCne (fun y hy => h y hy)
        linarith
      obtain ⟨y, hyC, hya⟩ := hex
      have hay : a ≤ y := ha_le y hyC
      have hyne : y ≠ a := fun h => haC (h ▸ hyC)
      exact ⟨y, hδO (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩), hyC⟩
    have hb_closure : b ∈ closure C := by
      rw [mem_closure_iff_nhds]
      intro O hO
      obtain ⟨δ, hδpos, hδO⟩ := Metric.mem_nhds_iff.mp hO
      have hex : ∃ y ∈ C, b - δ / 2 < y := by
        by_contra h
        push_neg at h
        have : b ≤ b - δ / 2 := hbdef.symm ▸ csSup_le hCne (fun y hy => h y hy)
        linarith
      obtain ⟨y, hyC, hyb⟩ := hex
      have hyb' : y ≤ b := hb_le y hyC
      have hyne : y ≠ b := fun h => hbC (h ▸ hyC)
      exact ⟨y, hδO (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩), hyC⟩
    have ha_notS : a ∉ S := by
      intro haS
      have hpre : IsPreconnected (C ∪ {a}) :=
        hCpre.subset_closure (by intro z hz; exact Or.inl hz) (by
          intro z hz
          rcases hz with hz | rfl
          · exact subset_closure hz
          · exact ha_closure)
      have hsub : C ∪ {a} ⊆ S := by
        intro z hz
        rcases hz with hz | rfl
        · exact hCsub hz
        · exact haS
      have hmem : C ∪ {a} ⊆ connectedComponentIn S u :=
        hpre.subset_connectedComponentIn (x := u) (Or.inl huC) hsub
      exact haC (hmem (Or.inr rfl))
    have hb_notS : b ∉ S := by
      intro hbS
      have hpre : IsPreconnected (C ∪ {b}) :=
        hCpre.subset_closure (by intro z hz; exact Or.inl hz) (by
          intro z hz
          rcases hz with hz | rfl
          · exact subset_closure hz
          · exact hb_closure)
      have hsub : C ∪ {b} ⊆ S := by
        intro z hz
        rcases hz with hz | rfl
        · exact hCsub hz
        · exact hbS
      have hmem : C ∪ {b} ⊆ connectedComponentIn S u :=
        hpre.subset_connectedComponentIn (x := u) (Or.inl huC) hsub
      exact hbC (hmem (Or.inr rfl))
    have hau : a < u := lt_of_le_of_ne (ha_le u huC) (fun h => haC (h ▸ huC))
    have hub : u < b := lt_of_le_of_ne (hb_le u huC) (fun h => hbC (h ▸ huC))
    have hab : a < b := lt_trans hau hub
    have hIooC : Set.Ioo a b ⊆ C := by
      intro x hx
      have hx1 : ∃ y ∈ C, y < x := by
        by_contra h
        push_neg at h
        have : x ≤ a := hadef.symm ▸ le_csInf hCne (fun y hy => h y hy)
        linarith [hx.1]
      obtain ⟨y, hyC, hyx⟩ := hx1
      have hx2 : ∃ y' ∈ C, x < y' := by
        by_contra h
        push_neg at h
        have : b ≤ x := hbdef.symm ▸ csSup_le hCne (fun y hy => h y hy)
        linarith [hx.2]
      obtain ⟨y', hy'C, hxy'⟩ := hx2
      exact hCord.out hyC hy'C ⟨hyx.le, hxy'.le⟩
    -- The image of `(a,b)` is clopen in the connected `W`.
    set D : Set X := α '' Set.Ioo a b with hDdef
    have hDW : D ⊆ W := by
      rintro z ⟨t, ht, rfl⟩
      exact hCsub (hIooC (Set.mem_Ioo.mpr ht))
    have hDopen : IsOpen D :=
      isOpenMap_of_injective_continuous H hcont hinj _ isOpen_Ioo
    have hDcl : D = closure D ∩ W := by
      apply subset_antisymm
      · intro z hz
        exact ⟨subset_closure hz, hDW hz⟩
      · intro z hz
        obtain ⟨hzcl, hzW⟩ := hz
        have h1 : closure D ⊆ α '' Set.Icc a b :=
          closure_minimal (Set.image_mono Set.Ioo_subset_Icc_self)
            (isCompact_Icc.image hcont).isClosed
        obtain ⟨s, hs, hse⟩ := h1 hzcl
        have hzW' : α s ∈ W := by rw [hse]; exact hzW
        have hsS : s ∈ S := (hmS s).mpr hzW'
        have hsI : s ∈ Set.Ioo a b := by
          refine ⟨?_, ?_⟩
          · by_contra hcon
            push_neg at hcon
            exact ha_notS (le_antisymm hcon hs.1 ▸ hsS)
          · by_contra hcon
            push_neg at hcon
            exact hb_notS (le_antisymm hs.2 hcon ▸ hsS)
        exact ⟨s, hsI, hse⟩
    have hDne : D.Nonempty := ⟨α u, ⟨u, ⟨hau, hub⟩, rfl⟩⟩
    set D' : Set ↥W := {x : ↥W | (x : X) ∈ D} with hD'def
    have hD'open : IsOpen D' := hDopen.preimage continuous_subtype_val
    have hD'closed : IsClosed D' := by
      have hcomp' : D' = Subtype.val ⁻¹' closure D := by
        ext x
        constructor
        · intro hx
          exact subset_closure hx
        · intro hx
          have hx' : (x : X) ∈ closure D ∩ W := ⟨hx, x.2⟩
          rw [← hDcl] at hx'
          exact hx'
      rw [hcomp']
      exact isClosed_closure.preimage continuous_subtype_val
    have hD'ne : D'.Nonempty := by
      rcases hDne with ⟨z, hz⟩
      exact ⟨⟨z, hDW hz⟩, hz⟩
    have hD'univ : D' ≠ Set.univ := by
      intro h
      have hpD : (⟨p, hpW⟩ : ↥W) ∈ D' := h ▸ Set.mem_univ _
      have hpD' : p ∈ D := hpD
      obtain ⟨t, -, ht⟩ := hpD'
      exact hp ⟨t, ht⟩
    exact hD'univ ((isClopen_iff.mp (⟨hD'closed, hD'open⟩ : IsClopen D')).resolve_left hD'ne.ne_empty)
  -- The arc enters `W` from one side.
  have hsubT : ∀ t ∈ Set.Ici T, α t ∈ c.V := fun t ht => hWV ((hmS t).mp (hT t ht))
  let φ : ↥(Set.Ici T) → ℝ := fun s => c.coord ⟨α s.1, hsubT s.1 s.2⟩
  have hφ_cont : Continuous φ :=
    c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      (fun s => hsubT s.1 s.2))
  have hφ_ne : ∀ s : ↥(Set.Ici T), φ s ≠ 0 := by
    intro s h0
    have h1 : c.map (φ s) = α s.1 := c.map_coord _
    rw [h0, c.map_zero] at h1
    exact hp ⟨s.1, h1.symm⟩
  have hφ_range : Set.range φ ⊆ Set.Ioi (0:ℝ) ∪ Set.Iio (0:ℝ) := by
    rintro x ⟨s, rfl⟩
    rcases lt_or_gt_of_ne (hφ_ne s) with h | h
    · exact Or.inr h
    · exact Or.inl h
  haveI hpreT : PreconnectedSpace ↥(Set.Ici T) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  have hφ_pre : IsPreconnected (Set.range φ) := by
    have h := isPreconnected_univ.image φ hφ_cont.continuousOn
    rwa [Set.image_univ] at h
  have hφ_sign : (∀ s : ↥(Set.Ici T), 0 < φ s) ∨ (∀ s : ↥(Set.Ici T), φ s < 0) := by
    obtain hpos | hneg := IsPreconnected.subset_or_subset isOpen_Ioi isOpen_Iio
      (Set.disjoint_left.mpr fun x hx hx' => by
        simp only [Set.mem_Ioi] at hx
        simp only [Set.mem_Iio] at hx'
        linarith)
      hφ_range hφ_pre
    · left; intro s; exact hpos (Set.mem_range_self s)
    · right; intro s; exact hneg (Set.mem_range_self s)
  -- conclude: the side opposite to the occupied one is missed by `α`
  rcases hφ_sign with hpos | hneg
  · refine ⟨ε, hεpos, hqW, Or.inl ?_⟩
    rintro z ⟨v, hv, rfl⟩ ⟨s, hs⟩
    have hsS : s ∈ S := (hmS s).mpr ⟨v, ⟨hv.1, hv.2.trans (by linarith)⟩, hs.symm⟩
    obtain ⟨t, htC, htT⟩ := hcomp s hsS T
    have hCSV : ∀ w ∈ connectedComponentIn S s, α w ∈ c.V := fun w hw =>
      hWV ((hmS w).mp (connectedComponentIn_subset S s hw))
    let η : ↥(connectedComponentIn S s) → ℝ := fun w => c.coord ⟨α w.1, hCSV w.1 w.2⟩
    have hη_cont : Continuous η :=
      c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
        (fun w => hCSV w.1 w.2))
    haveI : PreconnectedSpace ↥(connectedComponentIn S s) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
    have hη_ord : (Set.range η).OrdConnected := by
      have h := isPreconnected_univ.image η hη_cont.continuousOn
      rw [Set.image_univ] at h
      exact h.ordConnected
    have hneg_val : η ⟨s, mem_connectedComponentIn hsS⟩ < 0 := by
      have h1 : η ⟨s, mem_connectedComponentIn hsS⟩ = v := by
        show c.coord ⟨α s, hCSV s (mem_connectedComponentIn hsS)⟩ = v
        have h3 : (⟨α s, hCSV s (mem_connectedComponentIn hsS)⟩ : c.V) =
            ⟨c.map v, c.map_mem v⟩ := Subtype.ext hs
        rw [h3, Work.Smooth.SphereJordan.ArcChart.coord_apply_map]
      rw [h1]; exact hv.2
    have hpos_val : 0 < η ⟨t, htC⟩ := by
      have h1 : η ⟨t, htC⟩ = φ ⟨t, htT⟩ := rfl
      rw [h1]; exact hpos ⟨t, htT⟩
    have h0 : (0:ℝ) ∈ Set.range η :=
      hη_ord.out (Set.mem_range_self _) (Set.mem_range_self _) ⟨hneg_val.le, hpos_val.le⟩
    obtain ⟨w, hw⟩ := h0
    have hweq : α w.1 = p := by
      have h1 : c.map (η w) = α w.1 := c.map_coord _
      rw [hw, c.map_zero] at h1
      exact h1.symm
    exact hp ⟨w.1, hweq⟩
  · refine ⟨ε, hεpos, hqW, Or.inr ?_⟩
    rintro z ⟨v, hv, rfl⟩ ⟨s, hs⟩
    have hsS : s ∈ S := (hmS s).mpr ⟨v, ⟨by linarith [hv.1, hεpos], hv.2⟩, hs.symm⟩
    obtain ⟨t, htC, htT⟩ := hcomp s hsS T
    have hCSV : ∀ w ∈ connectedComponentIn S s, α w ∈ c.V := fun w hw =>
      hWV ((hmS w).mp (connectedComponentIn_subset S s hw))
    let η : ↥(connectedComponentIn S s) → ℝ := fun w => c.coord ⟨α w.1, hCSV w.1 w.2⟩
    have hη_cont : Continuous η :=
      c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
        (fun w => hCSV w.1 w.2))
    haveI : PreconnectedSpace ↥(connectedComponentIn S s) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
    have hη_ord : (Set.range η).OrdConnected := by
      have h := isPreconnected_univ.image η hη_cont.continuousOn
      rw [Set.image_univ] at h
      exact h.ordConnected
    have hpos_val : 0 < η ⟨s, mem_connectedComponentIn hsS⟩ := by
      have h1 : η ⟨s, mem_connectedComponentIn hsS⟩ = v := by
        show c.coord ⟨α s, hCSV s (mem_connectedComponentIn hsS)⟩ = v
        have h3 : (⟨α s, hCSV s (mem_connectedComponentIn hsS)⟩ : c.V) =
            ⟨c.map v, c.map_mem v⟩ := Subtype.ext hs
        rw [h3, Work.Smooth.SphereJordan.ArcChart.coord_apply_map]
      rw [h1]; exact hv.1
    have hneg_val : η ⟨t, htC⟩ < 0 := by
      have h1 : η ⟨t, htC⟩ = φ ⟨t, htT⟩ := rfl
      rw [h1]; exact hneg ⟨t, htT⟩
    have h0 : (0:ℝ) ∈ Set.range η :=
      hη_ord.out (Set.mem_range_self _) (Set.mem_range_self _) ⟨hneg_val.le, hpos_val.le⟩
    obtain ⟨w, hw⟩ := h0
    have hweq : α w.1 = p := by
      have h1 : c.map (η w) = α w.1 := c.map_coord _
      rw [hw, c.map_zero] at h1
      exact h1.symm
    exact hp ⟨w.1, hweq⟩

end

end Work.Smooth.SphereJordan.LocalArc
