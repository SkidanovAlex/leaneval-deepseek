import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic

/-!
# Limit points of an embedded line in a 1-manifold

An injective continuous map `α : ℝ → X` into a locally-arc Hausdorff space cannot behave like a
"spiral": if a point `y` is a limit point of the tail `α '' Ici s` for every `s`, then `α` eventually
stays in *any* neighbourhood of `y` cut out by a chart, and consequently `α t → y` as `t → +∞`.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter
open scoped Topology

noncomputable section

/-! ## A combinatorial fact about ord-connected subsets of `ℝ` -/

/-- Two ord-connected subsets of `ℝ` whose closures both contain a common point `δ` which is
strictly above both of them must meet. -/
lemma ordConnected_inter_of_mem_closure_right {S S' : Set ℝ} {δ : ℝ}
    (hS : S.OrdConnected) (hS' : S'.OrdConnected) (hne : S.Nonempty) (hne' : S'.Nonempty)
    (hsub : S ⊆ Set.Iio δ) (hsub' : S' ⊆ Set.Iio δ)
    (hc : δ ∈ closure S) (hc' : δ ∈ closure S') : (S ∩ S').Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨x', hx'⟩ := hne'
  have hxδ : x < δ := hsub hx
  have hx'δ : x' < δ := hsub' hx'
  set M : ℝ := (max x x' + δ) / 2 with hMdef
  have hMx : x < M := by
    have : x ≤ max x x' := le_max_left x x'
    have : x < δ := hxδ
    simp only [hMdef]; linarith
  have hMx' : x' < M := by
    have : x' ≤ max x x' := le_max_right x x'
    have : x' < δ := hx'δ
    simp only [hMdef]; linarith
  have hmaxδ : max x x' < δ := max_lt hxδ hx'δ
  have hxs : ∃ s ∈ S, M < s := by
    by_contra h
    push_neg at h
    have hsub2 : S ⊆ Set.Iic M := fun y hy => h y hy
    have : δ ∈ Set.Iic M := closure_minimal hsub2 isClosed_Iic hc
    simp only [Set.mem_Iic] at this
    linarith [hMdef, hmaxδ]
  obtain ⟨s, hs, hMs⟩ := hxs
  have hxs' : ∃ s' ∈ S', M < s' := by
    by_contra h
    push_neg at h
    have hsub2 : S' ⊆ Set.Iic M := fun y hy => h y hy
    have : δ ∈ Set.Iic M := closure_minimal hsub2 isClosed_Iic hc'
    simp only [Set.mem_Iic] at this
    linarith [hMdef, hmaxδ]
  obtain ⟨s', hs', hs'M⟩ := hxs'
  exact ⟨M, hS.out hx hs ⟨hMx.le, hMs.le⟩, hS'.out hx' hs' ⟨hMx'.le, hs'M.le⟩⟩

/-- Mirror image of `ordConnected_inter_of_mem_closure_right`: the common point lies strictly below
both sets. -/
lemma ordConnected_inter_of_mem_closure_left {S S' : Set ℝ} {c : ℝ}
    (hS : S.OrdConnected) (hS' : S'.OrdConnected) (hne : S.Nonempty) (hne' : S'.Nonempty)
    (hsub : S ⊆ Set.Ioi c) (hsub' : S' ⊆ Set.Ioi c)
    (hc : c ∈ closure S) (hc' : c ∈ closure S') : (S ∩ S').Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨x', hx'⟩ := hne'
  have hcx : c < x := hsub hx
  have hcx' : c < x' := hsub' hx'
  set M : ℝ := (min x x' + c) / 2 with hMdef
  have hMx : M < x := by
    have : min x x' ≤ x := min_le_left x x'
    simp only [hMdef]; linarith
  have hMx' : M < x' := by
    have : min x x' ≤ x' := min_le_right x x'
    simp only [hMdef]; linarith
  have hcmin : c < min x x' := lt_min hcx hcx'
  have hxs : ∃ s ∈ S, s < M := by
    by_contra h
    push_neg at h
    have hsub2 : S ⊆ Set.Ici M := fun y hy => h y hy
    have : c ∈ Set.Ici M := closure_minimal hsub2 isClosed_Ici hc
    simp only [Set.mem_Ici] at this
    linarith [hMdef, hcmin]
  obtain ⟨s, hs, hsM⟩ := hxs
  have hxs' : ∃ s' ∈ S', s' < M := by
    by_contra h
    push_neg at h
    have hsub2 : S' ⊆ Set.Ici M := fun y hy => h y hy
    have : c ∈ Set.Ici M := closure_minimal hsub2 isClosed_Ici hc'
    simp only [Set.mem_Ici] at this
    linarith [hMdef, hcmin]
  obtain ⟨s', hs', hs'M⟩ := hxs'
  exact ⟨M, hS.out hs hx ⟨hsM.le, hMx.le⟩, hS'.out hs' hx' ⟨hs'M.le, hMx'.le⟩⟩


/-- **A limit point of the `+∞`-tail of an arc is eventually contained in every chart interval.** -/
theorem localArc_eventually_mem_chart_interval {X : Type*} [TopologicalSpace X] [T2Space X]
    {y : X} (c : ArcChart X y) {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α)
    (hy : ∀ s : ℝ, y ∈ closure (α '' Set.Ici s)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t ≥ T, α t ∈ c.map '' Set.Ioo (-δ) δ := by
  classical
  set W : Set X := c.map '' Set.Ioo (-δ) δ with hWdef
  have hWopen : IsOpen W := by
    have h1 : W = (Subtype.val : c.V → X) '' (c.homeo '' Set.Ioo (-δ) δ) := by
      rw [hWdef]
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨c.homeo t, ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, rfl⟩
    rw [h1]
    exact c.isOpen_V.isOpenMap_subtype_val _ (c.homeo.isOpenMap _ isOpen_Ioo)
  have hyW : y ∈ W := ⟨0, ⟨by linarith, by linarith⟩, c.map_zero⟩
  have hWV : W ⊆ c.V := by
    rw [hWdef]
    rintro z ⟨t, ht, rfl⟩
    exact c.map_mem t
  set B : Set ℝ := α ⁻¹' W with hBdef
  have hBopen : IsOpen B := hWopen.preimage hcont
  by_contra hcon
  push_neg at hcon
  have hBunb : ∀ T : ℝ, ∃ t ≥ T, t ∈ B := by
    intro T
    have hne : (α '' Set.Ici T) ∩ W ≠ ∅ := by
      intro hempty
      have hsub : α '' Set.Ici T ⊆ Wᶜ := by
        intro z hz
        exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hempty) hz
      exact (closure_minimal hsub hWopen.isClosed_compl (hy T)) hyW
    obtain ⟨z, hz1, hz2⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨t, ht, rfl⟩ := hz1
    exact ⟨t, ht, hz2⟩
  set u : ℝ → ℝ := fun t => sInf {v : ℝ | t ≤ v ∧ v ∉ B} with hudef
  have hu_mem : ∀ t : ℝ, t ≤ u t ∧ u t ∉ B := by
    intro t
    obtain ⟨s, hs, hsb⟩ := hcon t
    have hne : ({v : ℝ | t ≤ v ∧ v ∉ B} : Set ℝ).Nonempty := ⟨s, hs, hsb⟩
    have hcl : IsClosed {v : ℝ | t ≤ v ∧ v ∉ B} := isClosed_Ici.inter hBopen.isClosed_compl
    have hbdd : BddBelow {v : ℝ | t ≤ v ∧ v ∉ B} := ⟨t, fun v hv => hv.1⟩
    exact hcl.csInf_mem hne hbdd
  have hu_spec : ∀ t v : ℝ, t ≤ v → v < u t → v ∈ B := by
    intro t v ht hv
    by_contra hvB
    have hmem : v ∈ {v : ℝ | t ≤ v ∧ v ∉ B} := ⟨ht, hvB⟩
    have hbdd : BddBelow {v : ℝ | t ≤ v ∧ v ∉ B} := ⟨t, fun x hx => hx.1⟩
    have hle : u t ≤ v := csInf_le hbdd hmem
    exact absurd hle (not_le.mpr hv)
  obtain ⟨t₁, -, ht₁B⟩ := hBunb 0
  obtain ⟨t₂, ht₂ge, ht₂B⟩ := hBunb (u t₁)
  have ht₂gt : u t₁ < t₂ := lt_of_le_of_ne ht₂ge fun h => (hu_mem t₁).2 (h ▸ ht₂B)
  obtain ⟨t₃, ht₃ge, ht₃B⟩ := hBunb (u t₂)
  have ht₃gt : u t₂ < t₃ := lt_of_le_of_ne ht₃ge fun h => (hu_mem t₂).2 (h ▸ ht₃B)
  have ht₁u : t₁ < u t₁ := lt_of_le_of_ne (hu_mem t₁).1 fun h => (hu_mem t₁).2 (h ▸ ht₁B)
  have ht₂u : t₂ < u t₂ := lt_of_le_of_ne (hu_mem t₂).1 fun h => (hu_mem t₂).2 (h ▸ ht₂B)
  have ht₃u : t₃ < u t₃ := lt_of_le_of_ne (hu_mem t₃).1 fun h => (hu_mem t₃).2 (h ▸ ht₃B)
  -- the chart coordinate on the preimage of the chart
  let ξ : ℝ → ℝ := fun s => if h : α s ∈ c.V then c.coord ⟨α s, h⟩ else 0
  have hξ_map : ∀ s ∈ B, c.map (ξ s) = α s := by
    intro s hs
    have hsV : α s ∈ c.V := hWV hs
    simp only [ξ, dif_pos hsV]
    exact c.map_coord ⟨α s, hsV⟩
  have hξ_inj : InjOn ξ B := by
    intro s hs t ht hst
    exact hinj (by rw [← hξ_map s hs, ← hξ_map t ht, hst])
  have hξ_contOn : ∀ t : ℝ, ContinuousOn ξ (Set.Ico t (u t)) := by
    intro t
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Set.domRestrict (Set.Ico t (u t)) ξ =
        fun z : Set.Ico t (u t) =>
          c.coord ⟨α z.1, hWV (hu_spec t z.1 z.2.1 z.2.2)⟩ := by
      funext z
      simp only [Set.domRestrict, ξ]
      exact dif_pos (hWV (hu_spec t z.1 z.2.1 z.2.2))
    rw [hfun]
    exact c.continuous_coord.comp (Continuous.subtype_mk (hcont.comp continuous_subtype_val)
      fun z => hWV (hu_spec t z.1 z.2.1 z.2.2))
  have hξ_sub : ∀ t : ℝ, ξ '' Set.Ico t (u t) ⊆ Set.Ioo (-δ) δ := by
    intro t x hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hsB : s ∈ B := hu_spec t s hs.1 hs.2
    have hαsW : α s ∈ W := hsB
    obtain ⟨q, hq, hqe⟩ := hαsW
    have hmap : c.map q = c.map (ξ s) := by rw [hqe, hξ_map s hsB]
    have hqeq : q = ξ s := c.injective_map hmap
    rwa [← hqeq]
  have hξ_preconn : ∀ t : ℝ, IsPreconnected (ξ '' Set.Ico t (u t)) :=
    fun t => isPreconnected_Ico.image ξ (hξ_contOn t)
  -- every excursion meets `±δ` in its closure
  have key : ∀ t : ℝ, t ∈ B →
      δ ∈ closure (ξ '' Set.Ico t (u t)) ∨ -δ ∈ closure (ξ '' Set.Ico t (u t)) := by
    intro t htB
    have htu : t < u t := lt_of_le_of_ne (hu_mem t).1 fun h => (hu_mem t).2 (h ▸ htB)
    have hne : (ξ '' Set.Ico t (u t)).Nonempty := ⟨ξ t, ⟨t, ⟨le_refl t, htu⟩, rfl⟩⟩
    by_contra h
    push_neg at h
    obtain ⟨hδc, hmδc⟩ := h
    have hcl_sub : closure (ξ '' Set.Ico t (u t)) ⊆ Set.Icc (-δ) δ :=
      closure_minimal (fun x hx => ⟨(hξ_sub t hx).1.le, (hξ_sub t hx).2.le⟩) isClosed_Icc
    have hne' : (closure (ξ '' Set.Ico t (u t))).Nonempty := hne.mono subset_closure
    have hbddA : BddAbove (closure (ξ '' Set.Ico t (u t))) := ⟨δ, fun x hx => (hcl_sub hx).2⟩
    have hbddB : BddBelow (closure (ξ '' Set.Ico t (u t))) := ⟨-δ, fun x hx => (hcl_sub hx).1⟩
    have hLmem : sInf (closure (ξ '' Set.Ico t (u t))) ∈ closure (ξ '' Set.Ico t (u t)) :=
      isClosed_closure.isLeast_csInf hne' hbddB |>.1
    have hRmem : sSup (closure (ξ '' Set.Ico t (u t))) ∈ closure (ξ '' Set.Ico t (u t)) :=
      isClosed_closure.isGreatest_csSup hne' hbddA |>.1
    have hLgt : -δ < sInf (closure (ξ '' Set.Ico t (u t))) := by
      by_contra hle
      have h2 : sInf (closure (ξ '' Set.Ico t (u t))) = -δ :=
        le_antisymm (not_lt.mp hle) (hcl_sub hLmem).1
      exact hmδc (h2 ▸ hLmem)
    have hRlt : sSup (closure (ξ '' Set.Ico t (u t))) < δ := by
      by_contra hle
      have h2 : sSup (closure (ξ '' Set.Ico t (u t))) = δ :=
        le_antisymm (hcl_sub hRmem).2 (not_lt.mp hle)
      exact hδc (h2 ▸ hRmem)
    have humem : u t ∈ closure (Set.Ico t (u t)) := by
      rw [show closure (Set.Ico t (u t)) = Set.Icc t (u t) from
        closure_Ico (a := t) (b := u t) (ne_of_lt htu)]
      exact ⟨htu.le, le_refl _⟩
    have hmem_cl : α (u t) ∈ closure (α '' Set.Ico t (u t)) :=
      mem_closure_image hcont.continuousAt humem
    have hαsub : α '' Set.Ico t (u t) ⊆
        c.map '' Set.Icc (sInf (closure (ξ '' Set.Ico t (u t))))
          (sSup (closure (ξ '' Set.Ico t (u t)))) := by
      rintro z ⟨s, hs, rfl⟩
      exact ⟨ξ s, ⟨csInf_le hbddB (subset_closure ⟨s, hs, rfl⟩),
        le_csSup hbddA (subset_closure ⟨s, hs, rfl⟩)⟩, hξ_map s (hu_spec t s hs.1 hs.2)⟩
    have hclosed : IsClosed (c.map '' Set.Icc (sInf (closure (ξ '' Set.Ico t (u t))))
        (sSup (closure (ξ '' Set.Ico t (u t))))) :=
      (isCompact_Icc.image c.continuous_map).isClosed
    have hmem2 : α (u t) ∈ c.map '' Set.Icc (sInf (closure (ξ '' Set.Ico t (u t))))
        (sSup (closure (ξ '' Set.Ico t (u t)))) := closure_minimal hαsub hclosed hmem_cl
    obtain ⟨q, hq, hqe⟩ := hmem2
    exact (hu_mem t).2 (⟨q, ⟨by linarith [hq.1], by linarith [hq.2]⟩, hqe⟩ : α (u t) ∈ W)
  -- two excursions of the same type cannot coexist
  have overlap : ∀ t t' : ℝ, t ∈ B → t' ∈ B → u t < t' →
      (δ ∈ closure (ξ '' Set.Ico t (u t)) → δ ∈ closure (ξ '' Set.Ico t' (u t')) → False) ∧
      (-δ ∈ closure (ξ '' Set.Ico t (u t)) → -δ ∈ closure (ξ '' Set.Ico t' (u t')) → False) := by
    intro t t' htB ht'B hlt
    have hord1 : (ξ '' Set.Ico t (u t)).OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hξ_preconn t)
    have hord2 : (ξ '' Set.Ico t' (u t')).OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hξ_preconn t')
    have hltu : t < u t := lt_of_le_of_ne (hu_mem t).1 fun h => (hu_mem t).2 (h ▸ htB)
    have hltu' : t' < u t' := lt_of_le_of_ne (hu_mem t').1 fun h => (hu_mem t').2 (h ▸ ht'B)
    have hne1 : (ξ '' Set.Ico t (u t)).Nonempty := ⟨ξ t, ⟨t, ⟨le_refl t, hltu⟩, rfl⟩⟩
    have hne2 : (ξ '' Set.Ico t' (u t')).Nonempty := ⟨ξ t', ⟨t', ⟨le_refl t', hltu'⟩, rfl⟩⟩
    constructor
    · intro h1 h2
      obtain ⟨M, hM1, hM2⟩ := ordConnected_inter_of_mem_closure_right hord1 hord2 hne1 hne2
        (fun x hx => (hξ_sub t hx).2) (fun x hx => (hξ_sub t' hx).2) h1 h2
      obtain ⟨s, hs, hMs⟩ := hM1
      obtain ⟨s', hs', hMs'⟩ := hM2
      have h2' : α s = α s' := by
        rw [← hξ_map s (hu_spec t s hs.1 hs.2), ← hξ_map s' (hu_spec t' s' hs'.1 hs'.2),
          hMs, hMs']
      have hss : s = s' := hinj h2'
      have h1s : s < u t := hs.2
      have h2s : t' ≤ s' := hs'.1
      rw [← hss] at h2s
      linarith
    · intro h1 h2
      obtain ⟨M, hM1, hM2⟩ := ordConnected_inter_of_mem_closure_left hord1 hord2 hne1 hne2
        (fun x hx => (hξ_sub t hx).1) (fun x hx => (hξ_sub t' hx).1) h1 h2
      obtain ⟨s, hs, hMs⟩ := hM1
      obtain ⟨s', hs', hMs'⟩ := hM2
      have h2' : α s = α s' := by
        rw [← hξ_map s (hu_spec t s hs.1 hs.2), ← hξ_map s' (hu_spec t' s' hs'.1 hs'.2),
          hMs, hMs']
      have hss : s = s' := hinj h2'
      have h1s : s < u t := hs.2
      have h2s : t' ≤ s' := hs'.1
      rw [← hss] at h2s
      linarith
  have hlt13 : u t₁ < t₃ := lt_trans ht₂gt (lt_trans ht₂u ht₃gt)
  rcases key t₁ ht₁B with h1 | h1 <;> rcases key t₂ ht₂B with h2 | h2 <;>
    rcases key t₃ ht₃B with h3 | h3
  · exact (overlap t₁ t₂ ht₁B ht₂B ht₂gt).1 h1 h2
  · exact (overlap t₁ t₂ ht₁B ht₂B ht₂gt).1 h1 h2
  · exact (overlap t₁ t₃ ht₁B ht₃B hlt13).1 h1 h3
  · exact (overlap t₂ t₃ ht₂B ht₃B ht₃gt).2 h2 h3
  · exact (overlap t₂ t₃ ht₂B ht₃B ht₃gt).1 h2 h3
  · exact (overlap t₁ t₃ ht₁B ht₃B hlt13).2 h1 h3
  · exact (overlap t₁ t₂ ht₁B ht₂B ht₂gt).2 h1 h2
  · exact (overlap t₁ t₂ ht₁B ht₂B ht₂gt).2 h1 h2


/-- **A limit point of the `+∞`-tail is an actual limit.** -/
theorem localArc_tendsto_atTop {X : Type*} [TopologicalSpace X] [T2Space X]
    {y : X} (c : ArcChart X y) {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α)
    (hy : ∀ s : ℝ, y ∈ closure (α '' Set.Ici s)) :
    Tendsto α atTop (nhds y) := by
  rw [tendsto_def]
  intro O hO
  obtain ⟨δ, hδpos, hδO⟩ : ∃ δ > 0, c.map '' Set.Ioo (-δ) δ ⊆ O := by
    have h1 : (Subtype.val : c.V → X) ⁻¹' O ∈ 𝓝 (⟨y, c.mem_V⟩ : c.V) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hO
    have h1' : (Subtype.val : c.V → X) ⁻¹' O ∈ 𝓝 (c.homeo 0) := by
      rw [c.homeo_zero]
      exact h1
    have h2 : c.homeo ⁻¹' ((Subtype.val : c.V → X) ⁻¹' O) ∈ 𝓝 (0 : ℝ) :=
      c.homeo.continuous.continuousAt.preimage_mem_nhds h1'
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp h2
    refine ⟨δ, hδpos, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    exact hδsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hq.1], by linarith [hq.2]⟩)
  obtain ⟨T, hT⟩ := localArc_eventually_mem_chart_interval c hcont hinj hy hδpos
  exact Filter.eventually_atTop.mpr ⟨T, fun t ht => hδO (hT t ht)⟩

/-- **A limit point of the `-∞`-tail is an actual limit.** -/
theorem localArc_tendsto_atBot {X : Type*} [TopologicalSpace X] [T2Space X]
    {y : X} (c : ArcChart X y) {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α)
    (hy : ∀ s : ℝ, y ∈ closure (α '' Set.Iic s)) :
    Tendsto α atBot (nhds y) := by
  have hβcont : Continuous fun t : ℝ => α (-t) := hcont.comp continuous_neg
  have hβinj : Function.Injective fun t : ℝ => α (-t) := fun s t h => by simpa using hinj h
  have hβ : ∀ s : ℝ, y ∈ closure ((fun t : ℝ => α (-t)) '' Set.Ici s) := by
    intro s
    have h1 : (fun t : ℝ => α (-t)) '' Set.Ici s = α '' Set.Iic (-s) := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨-t, ?_, by simp⟩
        simp only [Set.mem_Ici, Set.mem_Iic] at ht ⊢
        linarith
      · rintro ⟨u, hu, rfl⟩
        refine ⟨-u, ?_, by simp⟩
        simp only [Set.mem_Ici, Set.mem_Iic] at hu ⊢
        linarith
    rw [h1]
    exact hy (-s)
  have h := localArc_tendsto_atTop c hβcont hβinj hβ
  rw [tendsto_def] at h ⊢
  intro O hO
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (h O hO)
  exact Filter.eventually_atBot.mpr ⟨-T, fun u hu => by
    simpa using hT (-u) (by linarith)⟩

/-- **An arc fills a neighbourhood of each of its points.** -/
theorem localArc_fills_neighbourhood {X : Type*} [TopologicalSpace X]
    {α : ℝ → X} (hcont : Continuous α) (hinj : Function.Injective α) (s : ℝ)
    (c : ArcChart X (α s)) :
    ∃ ε > 0, c.map '' Set.Ioo (-ε) ε ⊆ Set.range α := by
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
  have hξ_cont : ContinuousOn ξ (Set.Ioo (s - η) (s + η)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : Set.domRestrict (Set.Ioo (s - η) (s + η)) ξ =
        fun z : Set.Ioo (s - η) (s + η) => c.coord ⟨α z.1, hsub z.2⟩ := by
      funext z
      change (if h : α z.1 ∈ c.V then c.coord ⟨α z.1, h⟩ else 0) =
        c.coord ⟨α z.1, hsub z.2⟩
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
    exact ⟨u, by rw [← hueq, hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu))]⟩
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
      ⟨by linarith [hw.1, hA], by linarith [hw.2, hB]⟩
    rw [← himg] at hw'
    obtain ⟨u, hu, hueq⟩ := hw'
    exact ⟨u, by rw [← hueq, hξ_map u (hsub2 (Set.Ioo_subset_Icc_self hu))]⟩

end

end Work.Smooth.SphereJordan.LocalArc
