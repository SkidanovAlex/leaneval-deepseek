import Submission.Work.Whitney.PathTools.JaniszewskiSep
import Submission.Work.Whitney.PathTools.exists_chain_of_path

/-!
# Janiszewski's theorem for two separated compacta in the plane

If `A` and `B` are disjoint compact subsets of `ℝ²`, and two points `X, Y` outside `A ∪ B` can be
joined by paths avoiding `A` and avoiding `B` respectively, then they can be joined by a path
avoiding `A ∪ B`.

The proof uses the mod-2 grid machinery: the two paths lie at a positive distance from the
respective compacta (all sets being compact), so they can be snapped to grid chains avoiding the
cells meeting `A` and `B`; the Alexander/Janiszewski splitting lemma
`exists_chain_avoiding_union'` combines the two chains.
-/

namespace Work.Whitney.PathTools
namespace Grid

open Set Metric Topology

noncomputable section

/-- Two disjoint compact subsets of `Pt` have positive, uniform distance. -/
theorem exists_pos_le_dist {A B : Set Pt} (hA : IsCompact A) (hB : IsCompact B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, 0 < dist x y) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ A, ∀ y ∈ B, d ≤ dist x y := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨1, one_pos, fun x hx => absurd hx (by simp)⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · exact ⟨1, one_pos, fun x hx y hy => absurd hy (by simp)⟩
  obtain ⟨a', ha'pos, ha'le⟩ := (hA.prod hB).exists_forall_le'
    (f := fun q : Pt × Pt => dist q.1 q.2)
    (continuous_fst.dist continuous_snd).continuousOn
    (a := 0) (fun b hb => hsep b.1 hb.1 b.2 hb.2)
  exact ⟨a', ha'pos, fun x hx y hy => ha'le (x, y) ⟨hx, hy⟩⟩

/-- **Janiszewski for two separated compacta.** -/
theorem joinedIn_compl_union {A B : Set Pt} (hAc : IsCompact A) (hBc : IsCompact B)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, 0 < dist x y) {X Y : Pt}
    (hX : X ∉ A ∪ B) (hY : Y ∉ A ∪ B)
    (hjoinA : JoinedIn (Aᶜ) X Y) (hjoinB : JoinedIn (Bᶜ) X Y) :
    JoinedIn ((A ∪ B)ᶜ) X Y := by
  classical
  by_cases hAB : A = ∅
  · rw [hAB, Set.empty_union]; exact hjoinB
  by_cases hBB : B = ∅
  · rw [hBB, Set.union_empty]; exact hjoinA
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAB
  have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hBB
  have hABc : (A ∪ B).Nonempty := hAne.inl
  by_cases hXY : X = Y
  · subst hXY
    exact JoinedIn.refl (by
      simp only [mem_compl_iff, mem_union, not_or]
      exact ⟨fun h => hX (Or.inl h), fun h => hX (Or.inr h)⟩)
  obtain ⟨γ, hγ⟩ := hjoinA
  obtain ⟨η, hη⟩ := hjoinB
  have hγA : ∀ t, γ t ∉ A := fun t => by simpa [mem_compl_iff] using hγ t
  have hηB : ∀ t, η t ∉ B := fun t => by simpa [mem_compl_iff] using hη t
  -- uniform separations
  obtain ⟨dAB, hdAB, hdABle⟩ := exists_pos_le_dist hAc hBc hsep
  obtain ⟨δγ, hδγ, hδγle⟩ := exists_pos_le_dist (isCompact_range γ.continuous) hAc
    (fun t ht a ha => by
      obtain ⟨s, rfl⟩ := ht
      exact dist_pos.mpr fun h => hγA s (h ▸ ha))
  obtain ⟨δη, hδη, hδηle⟩ := exists_pos_le_dist (isCompact_range η.continuous) hBc
    (fun t ht b hb => by
      obtain ⟨s, rfl⟩ := ht
      exact dist_pos.mpr fun h => hηB s (h ▸ hb))
  -- distances of the endpoints from `A ∪ B`
  have hXcl : X ∉ closure (A ∪ B) := by
    rw [hAc.union hBc |>.isClosed.closure_eq]; exact hX
  have hYcl : Y ∉ closure (A ∪ B) := by
    rw [hAc.union hBc |>.isClosed.closure_eq]; exact hY
  have hXi : 0 < Metric.infDist X (A ∪ B) :=
    (Metric.infDist_pos_iff_notMem_closure hABc).mp hXcl
  have hYi : 0 < Metric.infDist Y (A ∪ B) :=
    (Metric.infDist_pos_iff_notMem_closure hABc).mp hYcl
  have hXYpos : 0 < dist X Y := dist_pos.mpr hXY
  -- the mesh
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set h : ℝ := min 1 (min (dAB / (16 * Real.sqrt 2)) (min (δγ / 200) (min (δη / 200)
    (min (Metric.infDist X (A ∪ B) / 8) (min (Metric.infDist Y (A ∪ B) / 8)
      (dist X Y / 8)))))) with hhdef
  have hh : 0 < h := by
    rw [hhdef]
    refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  have hh1 : h ≤ dAB / (16 * Real.sqrt 2) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hh2 : h ≤ δγ / 200 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh3 : h ≤ δη / 200 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hh4 : h ≤ Metric.infDist X (A ∪ B) / 8 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hh5 : h ≤ Metric.infDist Y (A ∪ B) / 8 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hh6 : h ≤ dist X Y / 8 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
  have hmesh : 8 * h * Real.sqrt 2 < dAB := by
    have h2 : 8 * (dAB / (16 * Real.sqrt 2)) * Real.sqrt 2 = dAB / 2 := by
      field_simp; ring
    have h3 : 8 * h * Real.sqrt 2 ≤ 8 * (dAB / (16 * Real.sqrt 2)) * Real.sqrt 2 := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hsqrt2)
      nlinarith [hh1, hh]
    rw [h2] at h3
    linarith
  -- the paths as functions on `ℝ`
  set γ' : ℝ → Pt := fun s => γ (Set.projIcc 0 1 zero_le_one s) with hγ'def
  set η' : ℝ → Pt := fun s => η (Set.projIcc 0 1 zero_le_one s) with hη'def
  have hγ'0 : γ' 0 = X := by
    have := Set.projIcc_left (a := (0:ℝ)) (b := 1) zero_le_one
    simp only [hγ'def, this]
    exact γ.source
  have hγ'1 : γ' 1 = Y := by
    have := Set.projIcc_right (a := (0:ℝ)) (b := 1) zero_le_one
    simp only [hγ'def, this]
    exact γ.target
  have hη'0 : η' 0 = X := by
    have := Set.projIcc_left (a := (0:ℝ)) (b := 1) zero_le_one
    simp only [hη'def, this]
    exact η.source
  have hη'1 : η' 1 = Y := by
    have := Set.projIcc_right (a := (0:ℝ)) (b := 1) zero_le_one
    simp only [hη'def, this]
    exact η.target
  have hγ'cont : ContinuousOn γ' (Set.Icc (0:ℝ) 1) :=
    (γ.continuous.comp continuous_projIcc).continuousOn
  have hη'cont : ContinuousOn η' (Set.Icc (0:ℝ) 1) :=
    (η.continuous.comp continuous_projIcc).continuousOn
  have hroomγ : ∀ t ∈ Set.Icc (0:ℝ) 1, 100 * h ≤ Metric.infDist (γ' t) A := by
    intro t ht
    have h1 : 100 * h ≤ δγ := by have := hh2; linarith
    have h2 : δγ ≤ Metric.infDist (γ' t) A := by
      rw [Metric.le_infDist hAne]
      intro a ha
      exact hδγle (γ' t) ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩ a ha
    linarith
  have hroomη : ∀ t ∈ Set.Icc (0:ℝ) 1, 100 * h ≤ Metric.infDist (η' t) B := by
    intro t ht
    have h1 : 100 * h ≤ δη := by have := hh3; linarith
    have h2 : δη ≤ Metric.infDist (η' t) B := by
      rw [Metric.le_infDist hBne]
      intro b hb
      exact hδηle (η' t) ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩ b hb
    linarith
  -- snap the two paths
  obtain ⟨l₁, hb₁, hav₁⟩ := exists_chain_of_path hh hγ'cont hAc hroomγ
  obtain ⟨l₂, hb₂, hav₂⟩ := exists_chain_of_path hh hη'cont hBc hroomη
  have hb₁' : ∀ v : ℤ × ℤ, bdry1 ((l₁ : Chain1) : Edge → ZMod 2) v
      = (if v = gNear h X then 1 else 0) + (if v = gNear h Y then 1 else 0) := by
    intro v; rw [hb₁ v, hγ'0, hγ'1]
  have hb₂' : ∀ v : ℤ × ℤ, bdry1 ((l₂ : Chain1) : Edge → ZMod 2) v
      = (if v = gNear h X then 1 else 0) + (if v = gNear h Y then 1 else 0) := by
    intro v; rw [hb₂ v, hη'0, hη'1]
  -- the grid geometry of the two cell sets
  have hgeo₁ := cellSet_geometry hh hAc hBc.isClosed (fun x hx y hy => by
    have := hdABle x hx y hy; linarith)
  have hgeo₂ := cellSet_geometry hh hBc hAc.isClosed (fun x hx y hy => by
    have := hdABle y hy x hx; rw [dist_comm] at this; linarith)
  obtain ⟨hcellfin, hdisj, hstar, havoidA⟩ := hgeo₁
  obtain ⟨-, -, -, havoidB⟩ := hgeo₂
  obtain ⟨l₀, hb₀, hav₀⟩ := exists_chain_avoiding_union' hcellfin hdisj hstar
    (by funext v; rw [hb₁' v, hb₂' v]) hav₁ hav₂
  -- the endpoints
  have hgridX : dist X (gptH h (gNear h X)) ≤ 2 * h := by
    rw [dist_comm]; exact gNF_dist h hh X
  have hgridY : dist Y (gptH h (gNear h Y)) ≤ 2 * h := by
    rw [dist_comm]; exact gNF_dist h hh Y
  have hfarX : gptH h (gNear h X) ∉ A ∪ B := by
    intro hmem
    have h1 : Metric.infDist X (A ∪ B) ≤ dist X (gptH h (gNear h X)) :=
      Metric.infDist_le_dist_of_mem hmem
    have h2 : h ≤ Metric.infDist X (A ∪ B) / 8 := hh4
    linarith
  have hne : gNear h X ≠ gNear h Y := by
    intro heq
    have h1 : dist X Y ≤ dist X (gptH h (gNear h X)) + dist (gptH h (gNear h X)) Y :=
      dist_triangle _ _ _
    have h1' : dist (gptH h (gNear h X)) Y ≤ 2 * h := by rw [heq, dist_comm]; exact hgridY
    have h2 : h ≤ dist X Y / 8 := hh6
    linarith
  -- the chain gives a path between the grid points
  have hchain : JoinedIn ((A ∪ B)ᶜ) (gptH h (gNear h X)) (gptH h (gNear h Y)) := by
    refine joinedIn_of_chain hne hfarX (fun v => by rw [congrFun hb₀ v, hb₁' v]) ?_
    intro e he
    exact Disjoint.union_right (havoidA e (hav₀ e he).1) (havoidB e (hav₀ e he).2)
  -- connect the endpoints to the nearby grid points by straight segments
  have hsegX : JoinedIn ((A ∪ B)ᶜ) X (gptH h (gNear h X)) := by
    have hsub : segment ℝ X (gptH h (gNear h X)) ⊆ (A ∪ B)ᶜ := by
      intro z hz
      rw [mem_compl_iff]
      intro hmem
      have h1 : Metric.infDist X (A ∪ B) ≤ dist X z := Metric.infDist_le_dist_of_mem hmem
      have h2 : z ∈ closedBall X (dist X (gptH h (gNear h X))) :=
        segment_subset_closedBall_left X _ hz
      rw [Metric.mem_closedBall, dist_comm] at h2
      have h3 : h ≤ Metric.infDist X (A ∪ B) / 8 := hh4
      linarith
    obtain ⟨γseg, hγseg⟩ := ((convex_segment X (gptH h (gNear h X))).isPathConnected
      ⟨X, left_mem_segment ℝ X _⟩).joinedIn X (left_mem_segment ℝ X (gptH h (gNear h X))) (gptH h (gNear h X))
      (right_mem_segment ℝ X (gptH h (gNear h X)))
    exact ⟨γseg, fun t => hsub (hγseg t)⟩
  have hsegY : JoinedIn ((A ∪ B)ᶜ) Y (gptH h (gNear h Y)) := by
    have hsub : segment ℝ Y (gptH h (gNear h Y)) ⊆ (A ∪ B)ᶜ := by
      intro z hz
      rw [mem_compl_iff]
      intro hmem
      have h1 : Metric.infDist Y (A ∪ B) ≤ dist Y z := Metric.infDist_le_dist_of_mem hmem
      have h2 : z ∈ closedBall Y (dist Y (gptH h (gNear h Y))) :=
        segment_subset_closedBall_left Y _ hz
      rw [Metric.mem_closedBall, dist_comm] at h2
      have h3 : h ≤ Metric.infDist Y (A ∪ B) / 8 := hh5
      linarith
    obtain ⟨γseg, hγseg⟩ := ((convex_segment Y (gptH h (gNear h Y))).isPathConnected
      ⟨Y, left_mem_segment ℝ Y _⟩).joinedIn Y (left_mem_segment ℝ Y (gptH h (gNear h Y))) (gptH h (gNear h Y))
      (right_mem_segment ℝ Y (gptH h (gNear h Y)))
    exact ⟨γseg, fun t => hsub (hγseg t)⟩
  exact hsegX.trans (hchain.trans hsegY.symm)

end

end Grid
end Work.Whitney.PathTools
