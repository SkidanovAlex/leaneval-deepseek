import Mathlib
import Submission.Work.RatHurewicz.SkelGraph.points
import Submission.Work.RatHurewicz.SkelGraph.graphElementDefs
import Submission.Work.RatHurewicz.SkelGraph.goodDefs
import Submission.Work.RatHurewicz.SkelGraph.existsOpenVertex
import Submission.Work.RatHurewicz.SkelGraph.existsOpenEdge
import Submission.Work.RatHurewicz.SkelGraph.existsOpenArc
import Submission.Work.RatHurewicz.PiOneSkel.graphElementData
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.finiteGraphDefs

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## Local openness of `good` -/

theorem exists_open_of_mem_good {D : MData X n x₀} {U : Set (V D ⊕ (E D × I))}
    (hU : IsOpen U) (hSat : GoodAux.Sat D U) {y : Raw D} (hy : y ∈ GoodAux.good D U) :
    ∃ N : Set (Raw D), IsOpen N ∧ y ∈ N ∧
      ∀ y' ∈ N, isLowDim D y' → y' ∈ GoodAux.good D U := by
  obtain ⟨h, hmem⟩ := hy
  rcases y with ⟨i, x⟩ | ⟨i, s₀⟩
  · rcases hdec : decomp x with p | ⟨⟨⟨p, q⟩, hpq⟩, s⟩
    · have hm : Sum.inl (vCl D (Sum.inl ⟨i, p⟩)) ∈ U := by
        rw [wOf_inl_inl D i x h p hdec] at hmem
        exact hmem
      obtain ⟨N, hN, hyN, hsub⟩ := existsOpenVertex D hU hSat hm
      have hx : x = stdSimplex.vertex p := GoodAux.eq_vertex_of_decomp_inl hdec
      exact ⟨N, hN, by rw [hx]; exact hyN, hsub⟩
    · obtain ⟨hx, h0, h1⟩ := GoodAux.eq_sdPt_of_decomp_inr hdec h
      have hm : Sum.inr (eCl D (Sum.inl (⟨i,
          (⟨(p, q), hpq⟩ : {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})⟩ :
          Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2})), s) ∈ U := by
        rw [wOf_inl_inr D i x h ⟨(p, q), hpq⟩ s hdec] at hmem
        exact hmem
      obtain ⟨N, hN, hyN, hsub⟩ := existsOpenEdge D hU hpq h0 h1 hm
      exact ⟨N, hN, by rw [hx]; exact hyN, hsub⟩
  · have hm : Sum.inr (eCl D (Sum.inr ⟨i, PUnit.unit⟩), s₀) ∈ U := by
      rw [wOf_inr D i s₀ h] at hmem
      exact hmem
    exact existsOpenArc D hU hm

/-! ## The main result -/

theorem isOpenMapPhi {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) :
    IsOpenMap (Work.RatHurewicz.SkelGraph.Phi D) := by
  intro W hW
  set U : Set (V D ⊕ (E D × I)) := gq (a D) (b D) ⁻¹' W with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact hW.preimage continuous_quotient_mk'
  have hSat : GoodAux.Sat D U := GoodAux.sat_preimage W
  -- ### The image of `W` is the trace of `good D U` on the skeleton
  have hmain : Phi D '' W = Subtype.val ⁻¹' (Quotient.mk'' '' GoodAux.good D U) := by
    ext z
    constructor
    · rintro ⟨x, hxW, rfl⟩
      obtain ⟨w, rfl⟩ := Quotient.mk''_surjective x
      have hwU : w ∈ U := by rw [hUdef]; exact hxW
      show (Phi D (gq (a D) (b D) w)).1 ∈ Quotient.mk'' '' GoodAux.good D U
      refine ⟨(rawOf D w).1, GoodAux.mem_good_of (rawOf D w).2 ?_, ?_⟩
      · rw [hUdef] at hwU ⊢
        simp only [Set.mem_preimage] at hwU ⊢
        simpa only [PiOneSkel.gq_wOf_rawOf D w] using hwU
      · rw [Phi_apply, psi_rawOf]
        rfl
    · rintro ⟨y, hygood, hyeq⟩
      obtain ⟨hyl, hmemU⟩ := hygood
      refine ⟨gq (a D) (b D) (wOf D ⟨y, hyl⟩), ?_, ?_⟩
      · rw [hUdef] at hmemU
        exact hmemU
      · apply Subtype.ext
        show (Phi D (gq (a D) (b D) (wOf D ⟨y, hyl⟩))).1 = (z : Model D)
        rw [Phi_apply, PiOneSkel.psi_wOf D ⟨y, hyl⟩]
        exact hyeq
  -- ### `good D U` is open in the subspace of low dimensional points
  have hloc : ∀ y : {y : Raw D // y ∈ GoodAux.good D U}, ∃ N : Set (Raw D), IsOpen N ∧
      (y : Raw D) ∈ N ∧ ∀ y' ∈ N, isLowDim D y' → y' ∈ GoodAux.good D U :=
    fun y => exists_open_of_mem_good hUopen hSat y.2
  choose N hNopen hyN hNsub using hloc
  set W' : Set (Raw D) := ⋃ y : {y : Raw D // y ∈ GoodAux.good D U}, N y with hW'def
  have hW'open : IsOpen W' := by rw [hW'def]; exact isOpen_iUnion (fun y => hNopen y)
  have hW'S : W' ∩ {y : Raw D | isLowDim D y} = GoodAux.good D U := by
    apply Set.Subset.antisymm
    · rintro y ⟨hyW, hyL⟩
      obtain ⟨y0, hy0⟩ := Set.mem_iUnion.mp hyW
      exact hNsub y0 y hy0 hyL
    · intro y hy
      rw [hW'def]
      exact ⟨Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyN ⟨y, hy⟩⟩, GoodAux.isLowDim_of_mem_good hy⟩
  -- ### `good D U` is saturated for the gluing relation
  have hsatgood : ∀ {y y' : Raw D}, y ∈ GoodAux.good D U →
      Relation.EqvGen (modelRel D) y y' → isLowDim D y' → y' ∈ GoodAux.good D U := by
    intro y y' hy h hyl'
    obtain ⟨hyl, hmem⟩ := hy
    have hmemW : gq (a D) (b D) (wOf D ⟨y, hyl⟩) ∈ W := by
      rw [hUdef] at hmem
      exact hmem
    have hgq := PiOneSkel.gq_wOf_eqvGen D h hyl hyl'
    refine ⟨hyl', ?_⟩
    rw [hUdef]
    simp only [Set.mem_preimage]
    rw [← hgq]
    exact hmemW
  -- ### an open set of the model whose trace on the skeleton is `good D U`
  have hVopen : IsOpen ((Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y}) : Set (Model D))) := by
    refine (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (modelRel D))).isCoinducing
      |>.isOpen_preimage.mp ?_
    change IsOpen {y : Raw D | Quotient.mk'' y ∈
      Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y})}
    rw [show {y : Raw D | Quotient.mk'' y ∈
          Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y})}
        = ({y : Raw D | ∃ y' ∈ W', Relation.EqvGen (modelRel D) y' y}
            ∪ {y : Raw D | ¬ isLowDim D y}) from by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_union]
      constructor
      · rintro ⟨a, ha, hay⟩
        rcases ha with ha | ha
        · exact Or.inl ⟨a, ha, Quotient.eq.mp hay⟩
        · refine Or.inr (fun hy => ha ?_)
          exact (GoodAux.isLowDim_eqvGen (Quotient.eq.mp hay)).mpr hy
      · rintro (⟨a, ha, hay⟩ | hy)
        · exact ⟨a, Or.inl ha, Quotient.sound hay⟩
        · exact ⟨y, Or.inr hy, rfl⟩]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    by_cases hyl : isLowDim D y
    · -- `y` is low dimensional, hence related to a good point
      have hyrel : ∃ y0 ∈ W', Relation.EqvGen (modelRel D) y0 y := by
        rcases hy with ⟨y0, hy0, hrel⟩ | hyS
        · exact ⟨y0, hy0, hrel⟩
        · exact absurd hyl hyS
      obtain ⟨y0, hy0W, hrel⟩ := hyrel
      have hy0l : isLowDim D y0 := (GoodAux.isLowDim_eqvGen hrel).mpr hyl
      have hy0good : y0 ∈ GoodAux.good D U := by
        rw [← hW'S]; exact ⟨hy0W, hy0l⟩
      have hygood : y ∈ GoodAux.good D U := hsatgood hy0good hrel hyl
      refine Filter.mem_of_superset
        ((hNopen ⟨y, hygood⟩).mem_nhds (hyN ⟨y, hygood⟩)) ?_
      intro y' hy'
      by_cases hyl' : isLowDim D y'
      · have hy'good : y' ∈ GoodAux.good D U := hNsub ⟨y, hygood⟩ y' hy' hyl'
        have hy'W : y' ∈ W' := by
          have hmem : y' ∈ W' ∩ {y : Raw D | isLowDim D y} := by rw [hW'S]; exact hy'good
          exact hmem.1
        exact Or.inl ⟨y', hy'W, Relation.EqvGen.refl _⟩
      · exact Or.inr hyl'
    · -- `y` is not low dimensional
      rcases y with ⟨i, x⟩ | ⟨i, s₀⟩
      · let B : Set (stdSimplex ℝ (Fin (n + 2))) :=
          {x' | ∀ k ∈ supp x, 0 < x'.1 k}
        have hBopen : IsOpen B := by
          rw [show B = Subtype.val ⁻¹'
              (⋂ k ∈ supp x, {f : Fin (n + 2) → ℝ | 0 < f k}) from by
            ext x'
            simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iInter]]
          exact (isOpen_biInter_finset (fun k _ =>
            isOpen_lt continuous_const (continuous_apply k))).preimage continuous_subtype_val
        have hNopen : IsOpen ((Sum.inl '' (Sigma.mk i '' B) : Set (Raw D))) := by
          have h1 : IsOpen ((Sigma.mk i '' B :
              Set (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))) :=
            @isOpenMap_sigmaMk D.Idx (fun _ => stdSimplex ℝ (Fin (n + 2))) _ i B hBopen
          exact @isOpenMap_inl (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))
            (Σ _ : D.Idx, unitInterval) _ _ (Sigma.mk i '' B) h1
        have hyN : (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) : Raw D)
            ∈ (Sum.inl '' (Sigma.mk i '' B) : Set (Raw D)) := by
          rw [Set.mem_image]
          refine ⟨⟨i, x⟩, ?_, rfl⟩
          rw [Set.mem_image]
          refine ⟨x, ?_, rfl⟩
          change ∀ k ∈ supp x, 0 < x.1 k
          intro k hk
          rw [mem_supp] at hk
          exact lt_of_le_of_ne (x.2.1 k) (Ne.symm hk)
        refine Filter.mem_of_superset (hNopen.mem_nhds hyN) ?_
        intro y' hy'
        rw [Set.mem_image] at hy'
        obtain ⟨p, hp, rfl⟩ := hy'
        rw [Set.mem_image] at hp
        obtain ⟨x', hxB, rfl⟩ := hp
        refine Or.inr ?_
        have hcardx : ¬ ((supp x).card ≤ 2) := by
          simpa only [GoodAux.isLowDim_inl_iff] using hyl
        intro hcon
        have hcon' : (supp x').card ≤ 2 := by
          simpa only [GoodAux.isLowDim_inl_iff] using hcon
        have hxB' : ∀ k ∈ supp x, 0 < x'.1 k := by
          simpa only [B, Set.mem_ofPred_eq] using hxB
        have hsub : supp x ⊆ supp x' := by
          intro k hk
          rw [mem_supp]
          exact ne_of_gt (hxB' k hk)
        have hcard : (supp x).card ≤ (supp x').card := Finset.card_le_card hsub
        omega
      · exact absurd (GoodAux.isLowDim_inr i s₀) hyl
  -- ### the two sets have the same trace on the skeleton
  have hBeq : (Quotient.mk'' '' GoodAux.good D U : Set (Model D))
      = (Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y}) : Set (Model D)) ∩ skeleton D := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_image] at hz
      obtain ⟨y, hygood, rfl⟩ := hz
      have hyW : y ∈ W' := by
        rw [hW'def]
        exact Set.mem_iUnion.mpr ⟨⟨y, hygood⟩, hyN ⟨y, hygood⟩⟩
      have h1 : (Quotient.mk'' y : Model D) ∈
          (Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y}) : Set (Model D)) := by
        rw [Set.mem_image]
        exact ⟨y, Or.inl hyW, rfl⟩
      have h2 : (Quotient.mk'' y : Model D) ∈ skeleton D := by
        show ∃ y' : Raw D, Quotient.mk'' y' = Quotient.mk'' y ∧ isLowDim D y'
        exact ⟨y, rfl, GoodAux.isLowDim_of_mem_good hygood⟩
      rw [Set.mem_inter_iff]
      exact ⟨h1, h2⟩
    · rintro z hz
      rw [Set.mem_inter_iff] at hz
      obtain ⟨hzV, hzs⟩ := hz
      rw [Set.mem_image] at hzV
      obtain ⟨a, ha, haz⟩ := hzV
      obtain ⟨s, hs, hsmem⟩ := hzs
      have hrel : Relation.EqvGen (modelRel D) a s :=
        (Quotient.eq.mp (hs.trans haz.symm)).symm
      rcases ha with ha | ha
      · have hal : isLowDim D a := (GoodAux.isLowDim_eqvGen hrel).mpr hsmem
        have hagood : a ∈ GoodAux.good D U := by
          rw [← hW'S]; exact ⟨ha, hal⟩
        rw [Set.mem_image]
        exact ⟨a, hagood, haz⟩
      · exact absurd ((GoodAux.isLowDim_eqvGen hrel).mpr hsmem) ha
  have hkey : ∀ z : ↥(skeleton D),
      (z : Model D) ∈ (Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y}) : Set (Model D)) ↔
        (z : Model D) ∈ Quotient.mk'' '' GoodAux.good D U := by
    intro z
    rw [hBeq]
    constructor
    · intro h
      rw [Set.mem_inter_iff]
      exact ⟨h, z.2⟩
    · intro h
      rw [Set.mem_inter_iff] at h
      exact h.1
  rw [hmain]
  rw [show Subtype.val ⁻¹' (Quotient.mk'' '' GoodAux.good D U)
      = Subtype.val ⁻¹'
        (Quotient.mk'' '' (W' ∪ {y : Raw D | ¬ isLowDim D y}) : Set (Model D)) from by
    ext z
    simp only [Set.mem_preimage]
    exact (hkey z).symm]
  exact hVopen.preimage continuous_subtype_val

end

end Work.RatHurewicz.SkelGraph
