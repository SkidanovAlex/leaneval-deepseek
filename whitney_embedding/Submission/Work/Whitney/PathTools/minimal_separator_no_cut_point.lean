import Mathlib
import Submission.Work.Whitney.PathTools.GridAux

set_option linter.unusedVariables false

/-!
# A minimal separator in the plane has no cut point

The main theorem `Work.Whitney.PathTools.minimal_separator_no_cut_point` states that a compact,
preconnected set `L ⊆ ℝ²` which is *minimal* among the compact subsets of itself separating two
points `x`, `y` remains preconnected after the removal of any one of its points.

The proof reduces to the planar Janiszewski splitting principle for two compacta meeting in a
single point (`Grid.janis_singleton_plane`, McCleary, *A First Course in Topology*, Chapter 9,
"Alexander's theorem"), proved here from the mod-two grid chain complex: if `L \ {p} = A ⊔ B` were
a disconnection, then `A ∪ {p}` and `B ∪ {p}` are compacta meeting exactly in `p` which do not
separate `x` from `y` individually (by minimality of `L`), so they do not separate them jointly
either — contradicting the separating property of `L`.
-/

namespace Work.Whitney.PathTools

open Set Metric
open scoped Topology

namespace Grid

noncomputable section

/-! ## Elementary geometry of the grid -/

/-- An edge outside the edge set of the cells meeting `K` has its segment disjoint from `K`. -/
lemma gseg_disjoint_of_notMem_edgeSet (h : ℝ) (hh : 0 < h) {K : Set Pt} {e : Edge}
    (he : e ∉ edgeSet (cellSet h K)) : Disjoint (gseg h e) K := by
  rw [Set.disjoint_left]
  intro z hz hzK
  exact he ⟨eCell e, ⟨z, gseg_subset_gsq hh e hz, hzK⟩, mem_cellEdges_eCell e⟩

/-! ## Janiszewski's theorem for two compacta meeting in a single point -/

/-- **Planar Janiszewski theorem, single-point case.**  If `K`, `L ⊆ ℝ²` are compact and
`K ∩ L = {p}`, and two points `x, y ∉ K ∪ L` can be joined by a path avoiding `K` and by a path
avoiding `L`, then they can be joined by a path avoiding `K ∪ L`.

Proof (McCleary's "Alexander theorem" with a two-mesh subdivision of the mod-two grid chain
complex).  Snap the two paths at a coarse mesh `h` to chains `l₁`, `l₂` with a common boundary and
avoiding the cells of `K` resp. `L`.  Their sum is a cycle; fill it to a `2`-chain `W` and arrange
(shifting the whole picture so that `p` lies in the interior of the cell `(0,0)`, and replacing `W`
by `W + Θ₂` if necessary) that `p ∉ |W|`.  Subdivide at a mesh `h/n` so fine that the parts of
`|W|` lying over `K` and over `L` are at distance `> 2 (h/n) √2`; the restriction `w` of the
subdivided `W` to the cells meeting `K` then has the property that the chain `l₀ = l₂* + ∂w`
avoids both the cells of `K` and the cells of `L`.  Reading a walk off `l₀` gives the path. -/
theorem janis_singleton_plane {K L : Set Pt} (hK : IsCompact K) (hL : IsCompact L) {p : Pt}
    (hKL : K ∩ L = {p}) {x y : Pt} (hx : x ∉ K ∪ L) (hy : y ∉ K ∪ L)
    (h₁ : JoinedIn (Kᶜ) x y) (h₂ : JoinedIn (Lᶜ) x y) :
    JoinedIn ((K ∪ L)ᶜ) x y := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · exact JoinedIn.refl (by
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩)
  obtain ⟨γ₁, hγ₁⟩ := h₁
  obtain ⟨γ₂, hγ₂⟩ := h₂
  -- ================= STEP 1: the mesh =================
  obtain ⟨d₁, hd₁pos, hd₁⟩ := exists_pos_le_dist (isCompact_range γ₁.continuous) hK
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      obtain ⟨t, rfl⟩ := ha
      exact (hγ₁ t) (h0 ▸ hb)))
  obtain ⟨d₂, hd₂pos, hd₂⟩ := exists_pos_le_dist (isCompact_range γ₂.continuous) hL
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      obtain ⟨t, rfl⟩ := ha
      exact (hγ₂ t) (h0 ▸ hb)))
  obtain ⟨dx, hdxpos, hdx⟩ := exists_pos_le_dist (Set.finite_singleton x).isCompact (hK.union hL)
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      rw [Set.mem_singleton_iff] at ha
      rw [← h0] at hb
      exact hx (ha ▸ hb)))
  obtain ⟨dy, hdypos, hdy⟩ := exists_pos_le_dist (Set.finite_singleton y).isCompact (hK.union hL)
    (fun a ha b hb => dist_pos.mpr (fun h0 => by
      rw [Set.mem_singleton_iff] at ha
      rw [← h0] at hb
      exact hy (ha ▸ hb)))
  set h₀ : ℝ := min (min (min d₁ d₂) (min dx dy)) (dist x y) / 80 with hhdef
  have hhpos : 0 < h₀ := by
    rw [hhdef]
    refine div_pos (lt_min (lt_min (lt_min hd₁pos hd₂pos) (lt_min hdxpos hdypos))
      (dist_pos.mpr hxy)) (by norm_num)
  have hh_d₁ : 20 * h₀ ≤ d₁ := by
    have h1 : h₀ ≤ d₁ / 80 := by
      rw [hhdef]
      have h2 : min (min (min d₁ d₂) (min dx dy)) (dist x y) ≤ d₁ :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
      linarith
    linarith
  have hh_d₂ : 20 * h₀ ≤ d₂ := by
    have h1 : h₀ ≤ d₂ / 80 := by
      rw [hhdef]
      have h2 : min (min (min d₁ d₂) (min dx dy)) (dist x y) ≤ d₂ :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
      linarith
    linarith
  have hh_dx : 20 * h₀ ≤ dx := by
    have h1 : h₀ ≤ dx / 80 := by
      rw [hhdef]
      have h2 : min (min (min d₁ d₂) (min dx dy)) (dist x y) ≤ dx :=
        (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      linarith
    linarith
  have hh_dy : 20 * h₀ ≤ dy := by
    have h1 : h₀ ≤ dy / 80 := by
      rw [hhdef]
      have h2 : min (min (min d₁ d₂) (min dx dy)) (dist x y) ≤ dy :=
        (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    linarith
  have hh_xy : 80 * h₀ ≤ dist x y := by
    have h1 : h₀ ≤ dist x y / 80 := by
      rw [hhdef]
      have h2 : min (min (min d₁ d₂) (min dx dy)) (dist x y) ≤ dist x y := min_le_right _ _
      linarith
    linarith
  -- ================= STEP 2: the shift =================
  set v : Pt := p - (h₀ / 3) • gpt (1, 1) with hv
  have hpeq : p - v = gptH (h₀ / 3) (1, 1) := by
    rw [hv, gptH]
    abel
  have hpv0 : (p - v) 0 = h₀ / 3 := by
    rw [hpeq]; simp
  have hpv1 : (p - v) 1 = h₀ / 3 := by
    rw [hpeq]; simp
  set x' : Pt := x - v with hx'
  set y' : Pt := y - v with hy'
  set K' : Set Pt := (fun z => z - v) '' K with hK'
  set L' : Set Pt := (fun z => z - v) '' L with hL'
  have hK'c : IsCompact K' := by rw [hK']; exact hK.image (continuous_id.sub continuous_const)
  have hL'c : IsCompact L' := by rw [hL']; exact hL.image (continuous_id.sub continuous_const)
  have hsub_dist : ∀ a b : Pt, dist (a - v) (b - v) = dist a b := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hx'ne : x' ∉ K' ∪ L' := by
    rw [hx', hK', hL', Set.mem_union]
    push_neg
    constructor
    · rintro ⟨z, hz, hzv⟩
      refine hx ?_
      have h2 : z = x := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rw [← h2]
      exact Or.inl hz
    · rintro ⟨z, hz, hzv⟩
      refine hx ?_
      have h2 : z = x := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rw [← h2]
      exact Or.inr hz
  have hy'ne : y' ∉ K' ∪ L' := by
    rw [hy', hK', hL', Set.mem_union]
    push_neg
    constructor
    · rintro ⟨z, hz, hzv⟩
      refine hy ?_
      have h2 : z = y := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rw [← h2]
      exact Or.inl hz
    · rintro ⟨z, hz, hzv⟩
      refine hy ?_
      have h2 : z = y := by
        have := congrArg (fun s : Pt => s + v) hzv
        simpa using this
      rw [← h2]
      exact Or.inr hz
  set γ₁' : Path x' y' := ⟨⟨fun t => γ₁ t - v, γ₁.continuous.sub continuous_const⟩,
    (by dsimp only; rw [hx']; exact congrArg (fun s => s - v) γ₁.source),
    (by dsimp only; rw [hy']; exact congrArg (fun s => s - v) γ₁.target)⟩ with hγ₁'
  have hγ₁'mem : ∀ t : unitInterval, γ₁' t ∈ (K')ᶜ := by
    intro t
    rw [Set.mem_compl_iff]
    rintro ⟨z, hz, hzv⟩
    have h1 : γ₁ t ∈ Kᶜ := hγ₁ t
    rw [Set.mem_compl_iff] at h1
    have h2 : γ₁' t = γ₁ t - v := rfl
    rw [h2] at hzv
    refine h1 ?_
    have h3 : γ₁ t = z := by
      simpa using (congrArg (fun s : Pt => s + v) hzv).symm
    rwa [h3]
  set γ₂' : Path x' y' := ⟨⟨fun t => γ₂ t - v, γ₂.continuous.sub continuous_const⟩,
    (by dsimp only; rw [hx']; exact congrArg (fun s => s - v) γ₂.source),
    (by dsimp only; rw [hy']; exact congrArg (fun s => s - v) γ₂.target)⟩ with hγ₂'
  have hγ₂'mem : ∀ t : unitInterval, γ₂' t ∈ (L')ᶜ := by
    intro t
    rw [Set.mem_compl_iff]
    rintro ⟨z, hz, hzv⟩
    have h1 : γ₂ t ∈ Lᶜ := hγ₂ t
    rw [Set.mem_compl_iff] at h1
    have h2 : γ₂' t = γ₂ t - v := rfl
    rw [h2] at hzv
    refine h1 ?_
    have h3 : γ₂ t = z := by
      simpa using (congrArg (fun s : Pt => s + v) hzv).symm
    rwa [h3]
  have hdist₁ : ∀ t : unitInterval, ∀ s ∈ K', 20 * h₀ ≤ dist (γ₁' t) s := by
    rintro t s ⟨z, hz, rfl⟩
    have h2 : γ₁' t = γ₁ t - v := rfl
    rw [h2, hsub_dist]
    exact le_trans hh_d₁ (hd₁ (γ₁ t) ⟨t, rfl⟩ z hz)
  have hdist₂ : ∀ t : unitInterval, ∀ s ∈ L', 20 * h₀ ≤ dist (γ₂' t) s := by
    rintro t s ⟨z, hz, rfl⟩
    have h2 : γ₂' t = γ₂ t - v := rfl
    rw [h2, hsub_dist]
    exact le_trans hh_d₂ (hd₂ (γ₂ t) ⟨t, rfl⟩ z hz)
  have hdx' : ∀ s ∈ K' ∪ L', 20 * h₀ ≤ dist x' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : x' = x - v := hx'
      rw [h2, hsub_dist]
      exact le_trans hh_dx (hdx x rfl z (Or.inl hz))
    · have h2 : x' = x - v := hx'
      rw [h2, hsub_dist]
      exact le_trans hh_dx (hdx x rfl z (Or.inr hz))
  have hdy' : ∀ s ∈ K' ∪ L', 20 * h₀ ≤ dist y' s := by
    rintro s (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · have h2 : y' = y - v := hy'
      rw [h2, hsub_dist]
      exact le_trans hh_dy (hdy y rfl z (Or.inl hz))
    · have h2 : y' = y - v := hy'
      rw [h2, hsub_dist]
      exact le_trans hh_dy (hdy y rfl z (Or.inr hz))
  have hdistxy : dist x' y' = dist x y := by
    have h2 : x' = x - v := hx'
    have h3 : y' = y - v := hy'
    rw [h2, h3, hsub_dist]
  -- ================= STEP 3: snapping to the coarse grid =================
  obtain ⟨l₁, hb₁, hav₁⟩ := exists_chain_avoiding (S := K') hhpos (X := x') (Y := y')
    (γ := γ₁') hdist₁
  obtain ⟨l₂, hb₂, hav₂⟩ := exists_chain_avoiding (S := L') hhpos (X := x') (Y := y')
    (γ := γ₂') hdist₂
  set P : ℤ × ℤ := nearGrid h₀ x' with hP
  set Q : ℤ × ℤ := nearGrid h₀ y' with hQ
  have hb₁' : ∀ w : ℤ × ℤ, bdry1 ((l₁ : Chain1) : Edge → ZMod 2) w
      = (if w = P then 1 else 0) + (if w = Q then 1 else 0) := by
    intro w
    rw [hb₁ w, hP, hQ]
  have hb₂' : ∀ w : ℤ × ℤ, bdry1 ((l₂ : Chain1) : Edge → ZMod 2) w
      = (if w = P then 1 else 0) + (if w = Q then 1 else 0) := by
    intro w
    rw [hb₂ w, hP, hQ]
  have hPQ : P ≠ Q := by
    intro hPQ
    have h1 : dist x' y' ≤ 2 * h₀ := by
      calc dist x' y' ≤ dist x' (gptH h₀ P) + dist (gptH h₀ P) y' := dist_triangle _ _ _
        _ = dist x' (gptH h₀ P) + dist (gptH h₀ Q) y' := by rw [hPQ]
        _ ≤ h₀ + h₀ := add_le_add (nearGrid_dist hhpos x')
          (by rw [dist_comm]; exact nearGrid_dist hhpos y')
        _ = 2 * h₀ := by ring
    rw [hdistxy] at h1
    linarith [hh_xy, hhpos]
  -- ================= STEP 4: the filling =================
  set c : Chain1 := l₁ + l₂ with hc
  have hbc : bdry1 (c : Edge → ZMod 2) = 0 := by
    funext w
    rw [hc, Finsupp.coe_add, bdry1_add, Pi.add_apply, hb₁' w, hb₂' w, Pi.zero_apply]
    generalize (if w = P then (1 : ZMod 2) else 0) = A
    generalize (if w = Q then (1 : ZMod 2) else 0) = B
    rw [show (A + B) + (A + B) = (A + A) + (B + B) from by abel,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  set W₀ : C2 := fill c with hW₀
  have hW₀b : bdry2 W₀ = (c : Edge → ZMod 2) := by
    rw [hW₀]
    exact bdry2_fill c hbc
  have hpv_mem : p - v ∈ gsq h₀ (0, 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hpv0, hpv1] <;> norm_num <;> linarith [hhpos]
  have hcell_unique : ∀ cc : Cell, p - v ∈ gsq h₀ cc → cc = (0, 0) := by
    intro cc hcc
    obtain ⟨g1, g2, g3, g4⟩ := hcc
    rw [hpv0] at g1 g2
    rw [hpv1] at g3 g4
    have h1 : cc.1 = 0 := by
      have hlt : (cc.1 : ℝ) < 1 := by nlinarith [hhpos]
      have hge : (-1 : ℝ) < (cc.1 : ℝ) := by nlinarith [hhpos, g2]
      have hle' : cc.1 < 1 := by exact_mod_cast hlt
      have hge' : -1 < cc.1 := by exact_mod_cast hge
      omega
    have h2 : cc.2 = 0 := by
      have hlt : (cc.2 : ℝ) < 1 := by nlinarith [hhpos]
      have hge : (-1 : ℝ) < (cc.2 : ℝ) := by nlinarith [hhpos, g4]
      have hle' : cc.2 < 1 := by exact_mod_cast hlt
      have hge' : -1 < cc.2 := by exact_mod_cast hge
      omega
    exact Prod.ext h1 h2
  have hZMod2 : ∀ z : ZMod 2, z + 1 ≠ 0 → z ≠ 0 → False := by decide
  set W : C2 := if W₀ (0, 0) = 0 then W₀ else W₀ + Theta2 with hW
  have hWb : bdry2 W = (c : Edge → ZMod 2) := by
    rw [hW]
    split
    · exact hW₀b
    · rw [bdry2_add, hW₀b, bdry2_Theta2, add_zero]
  have hpvW : p - v ∉ locus h₀ W := by
    rw [hW]
    split
    · rename_i h0
      rintro ⟨cc, hcc, hccm⟩
      rw [hcell_unique cc hccm] at hcc
      exact hcc h0
    · rename_i h0
      rintro ⟨cc, hcc, hccm⟩
      rw [hcell_unique cc hccm] at hcc
      exact hZMod2 _ hcc h0
  -- ================= STEP 5: the separation and the fine mesh =================
  have hKW : IsCompact (locus h₀ W ∩ K') := by
    have heq : locus h₀ W ∩ K' =
        ⋃ cc ∈ (Function.support W ∩ cellSet h₀ K'), (gsq h₀ cc ∩ K') := by
      apply Set.Subset.antisymm
      · rintro z ⟨⟨cc, hcc, hccm⟩, hzK⟩
        exact Set.mem_biUnion ⟨hcc, ⟨z, hccm, hzK⟩⟩ ⟨hccm, hzK⟩
      · intro z hz
        obtain ⟨cc, hmem⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hcc, hccm⟩ := Set.mem_iUnion.mp hmem
        exact ⟨⟨cc, hcc.1, hccm.1⟩, hccm.2⟩
    rw [heq]
    refine Set.Finite.isCompact_biUnion ((cellSet_finite hhpos hK'c).inter_of_right _) ?_
    intro cc _
    exact hK'c.of_isClosed_subset ((isClosed_gsq h₀ cc).inter hK'c.isClosed)
      Set.inter_subset_right
  have hLW : IsCompact (locus h₀ W ∩ L') := by
    have heq : locus h₀ W ∩ L' =
        ⋃ cc ∈ (Function.support W ∩ cellSet h₀ L'), (gsq h₀ cc ∩ L') := by
      apply Set.Subset.antisymm
      · rintro z ⟨⟨cc, hcc, hccm⟩, hzL⟩
        exact Set.mem_biUnion ⟨hcc, ⟨z, hccm, hzL⟩⟩ ⟨hccm, hzL⟩
      · intro z hz
        obtain ⟨cc, hmem⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hcc, hccm⟩ := Set.mem_iUnion.mp hmem
        exact ⟨⟨cc, hcc.1, hccm.1⟩, hccm.2⟩
    rw [heq]
    refine Set.Finite.isCompact_biUnion ((cellSet_finite hhpos hL'c).inter_of_right _) ?_
    intro cc _
    exact hL'c.of_isClosed_subset ((isClosed_gsq h₀ cc).inter hL'c.isClosed)
      Set.inter_subset_right
  have hdisjW : Disjoint (locus h₀ W ∩ K') (locus h₀ W ∩ L') := by
    rw [Set.disjoint_left]
    rintro z ⟨hzW, hzK⟩ hzL'
    have hzL : z ∈ L' := hzL'.2
    have hKLeq : K' ∩ L' = {p - v} := by
      rw [hK', hL', ← Set.image_inter (fun a b hab => by simpa using hab), hKL]
      simp
    have hzKW : z = p - v := by
      have hmem : z ∈ K' ∩ L' := ⟨hzK, hzL⟩
      rw [hKLeq] at hmem
      simpa using hmem
    exact hpvW (hzKW ▸ hzW)
  obtain ⟨δc, hδcpos, hδc⟩ := exists_pos_le_dist hKW hLW
    (fun a ha b hb => dist_pos.mpr fun h0 => Set.disjoint_left.mp hdisjW ha (h0 ▸ hb))
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨n, hnpos, hnδ⟩ : ∃ n : ℕ, 0 < n ∧ 2 * ((h₀ / n) * Real.sqrt 2) < δc := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * h₀ * Real.sqrt 2 / δc)
    refine ⟨k + 1, Nat.succ_pos k, ?_⟩
    have h1 : 2 * h₀ * Real.sqrt 2 / δc < ((k + 1 : ℕ) : ℝ) := by
      have h2 : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    rw [div_lt_iff₀ hδcpos] at h1
    have h3 : 2 * ((h₀ / ((k + 1 : ℕ) : ℝ)) * Real.sqrt 2)
        = 2 * h₀ * Real.sqrt 2 / ((k + 1 : ℕ) : ℝ) := by ring
    rw [h3, div_lt_iff₀ (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
    linarith
  set hf : ℝ := h₀ / n with hfdef
  have hfpos : 0 < hf := by rw [hfdef]; exact div_pos hhpos (by exact_mod_cast hnpos)
  have hnfac : 2 * (hf * Real.sqrt 2) < δc := by rw [hfdef]; exact hnδ
  -- ================= STEP 6: the fine chains and the modification =================
  set l₁f : Edge → ZMod 2 := sub1 n (l₁ : Edge → ZMod 2) with hl₁f
  set l₂f : Edge → ZMod 2 := sub1 n (l₂ : Edge → ZMod 2) with hl₂f
  set Wf : C2 := sub2 n W with hWf
  have hWfb : bdry2 Wf = l₁f + l₂f := by
    rw [hWf, bdry2_sub2 hnpos, hWb, hc, Finsupp.coe_add, sub1_add]
  set S : Set Cell := cellSet hf K' with hS
  have hSfin : S.Finite := by rw [hS]; exact cellSet_finite hfpos hK'c
  set WK : C2 := arestrict Wf S with hWK
  have hWKzero : ∀ cc ∉ S, WK cc = 0 := by
    intro cc hcc; rw [hWK]; exact arestrict_zero Wf S cc hcc
  have hWKself : ∀ cc ∈ S, WK cc = Wf cc := by
    intro cc hcc; rw [hWK]; exact arestrict_self Wf S cc hcc
  -- (α): a fine cell of `S` belonging to the support of `Wf` avoids `L'`.
  have hAlpha : ∀ cc ∈ S, Wf cc ≠ 0 → Disjoint (gsq hf cc) L' := by
    intro cc hcS hWc
    rw [Set.disjoint_left]
    intro z hzc hzL
    obtain ⟨a, haz, haK⟩ := hcS
    have hWpar : W ((cc.1 / (n : ℤ), cc.2 / (n : ℤ))) ≠ 0 := by
      simpa only [hWf, sub2] using hWc
    have hsub2 : gsq hf cc ⊆ gsq h₀ (cc.1 / (n : ℤ), cc.2 / (n : ℤ)) := by
      rw [hfdef]
      exact gsq_sub2_subset hnpos hhpos cc
    have haW : a ∈ locus h₀ W ∩ K' := ⟨⟨_, hWpar, hsub2 haz⟩, haK⟩
    have hzW : z ∈ locus h₀ W ∩ L' := ⟨⟨_, hWpar, hsub2 hzc⟩, hzL⟩
    have hd : dist a z ≤ hf * Real.sqrt 2 := by
      have hcell := dist_le_of_cell_diff (h := hf) hfpos (c₁ := cc) (c₂ := cc) (k := 0) haz hzc
        (by simp) (by simp)
      simpa using hcell
    have hδ := hδc a haW z hzW
    have hspos : 0 < hf * Real.sqrt 2 := mul_pos hfpos hsqrt2pos
    have hlt : hf * Real.sqrt 2 < δc := by linarith [hnfac, hspos]
    linarith [hδ, hd, hlt]
  -- ================= STEP 7: the boundary chain and its avoidance =================
  have hsupp_sub : Function.support (fun e => l₂f e + bdry2 WK e) ⊆
      Function.support l₂f ∪ edgeSet S := by
    intro e he
    rw [Function.mem_support] at he
    by_cases h2 : l₂f e = 0
    · refine Or.inr (support_bdry2 WK (fun cc hcc => hWKzero cc hcc) ?_)
      intro h0
      exact he (by simp [h2, h0])
    · exact Or.inl (Function.mem_support.mpr h2)
  have hl2fin : (Function.support (l₂ : Edge → ZMod 2)).Finite := by
    rw [Finsupp.fun_support_eq]
    exact (l₂ : Chain1).support.finite_toSet
  have hfin0 : (Function.support (fun e => l₂f e + bdry2 WK e)).Finite :=
    ((support_sub1_finite hnpos hl2fin).union (edgeSet_finite hSfin)).subset hsupp_sub
  set l₀ : Chain1 := Finsupp.ofSupportFinite (fun e => l₂f e + bdry2 WK e) hfin0 with hl₀
  have hl₀coe : (l₀ : Edge → ZMod 2) = fun e => l₂f e + bdry2 WK e := Finsupp.ofSupportFinite_coe
  have hl₀eq : (l₀ : Edge → ZMod 2) = l₂f + bdry2 WK := by
    rw [hl₀coe]; rfl
  have hl₀eq₁ : (l₀ : Edge → ZMod 2) = l₁f + bdry2 (Wf + WK) := by
    rw [hl₀eq]
    have h1 : (l₁f + bdry2 (Wf + WK) : Edge → ZMod 2) = l₂f + bdry2 WK := by
      rw [bdry2_add, hWfb]
      rw [show (l₁f + ((l₁f + l₂f) + bdry2 WK) : Edge → ZMod 2)
            = l₂f + (l₁f + l₁f) + bdry2 WK from by abel,
        CharTwo.add_self_eq_zero, add_zero]
    rw [h1]
  have heloc₁ : elocus hf (l₀ : Edge → ZMod 2) ⊆
      elocus h₀ (l₁ : Edge → ZMod 2) ∪ locus hf (Wf + WK) := by
    rw [hl₀eq₁]
    exact (elocus_add_subset).trans (Set.union_subset_union (elocus_sub1_subset hnpos hhpos)
      (elocus_bdry2_subset_locus hfpos (Wf + WK)))
  have heloc₂ : elocus hf (l₀ : Edge → ZMod 2) ⊆
      elocus h₀ (l₂ : Edge → ZMod 2) ∪ locus hf WK := by
    rw [hl₀eq]
    exact (elocus_add_subset).trans (Set.union_subset_union (elocus_sub1_subset hnpos hhpos)
      (elocus_bdry2_subset_locus hfpos WK))
  have hAnywhere : ∀ z ∈ elocus hf (l₀ : Edge → ZMod 2), z ∉ K' ∧ z ∉ L' := by
    intro z hz
    constructor
    · intro hzK
      rcases heloc₁ hz with h | h
      · rcases mem_elocus.mp h with ⟨e, he, hze⟩
        exact Set.disjoint_left.mp
          (gseg_disjoint_of_notMem_edgeSet h₀ hhpos
            (hav₁ e (Finsupp.mem_support_iff.mpr he))) hze hzK
      · rcases mem_locus.mp h with ⟨cc, hcc, hzcc⟩
        have hccS : cc ∉ S := by
          intro hcS
          exact hcc (by rw [Pi.add_apply, hWKself cc hcS, CharTwo.add_self_eq_zero])
        have hempty : gsq hf cc ∩ K' = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hccS ⟨y, hy⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hempty) z ⟨hzcc, hzK⟩
    · intro hzL
      rcases heloc₂ hz with h | h
      · rcases mem_elocus.mp h with ⟨e, he, hze⟩
        exact Set.disjoint_left.mp
          (gseg_disjoint_of_notMem_edgeSet h₀ hhpos
            (hav₂ e (Finsupp.mem_support_iff.mpr he))) hze hzL
      · rcases mem_locus.mp h with ⟨cc, hcc, hzcc⟩
        have hccS : cc ∈ S := by
          by_contra hcS
          exact hcc (hWKzero cc hcS)
        have hWcc : Wf cc ≠ 0 := by
          rw [← hWKself cc hccS]
          exact hcc
        exact Set.disjoint_left.mp (hAlpha cc hccS hWcc) hzcc hzL
  have hhav : ∀ e ∈ (l₀ : Chain1).support, Disjoint (gseg hf e) (K' ∪ L') := by
    intro e he
    rw [Set.disjoint_left]
    intro z hz hzKL
    have hzel : z ∈ elocus hf (l₀ : Edge → ZMod 2) :=
      ⟨e, Finsupp.mem_support_iff.mp he, hz⟩
    rcases hzKL with h | h
    · exact (hAnywhere z hzel).1 h
    · exact (hAnywhere z hzel).2 h
  -- ================= STEP 8: the chain gives a path =================
  have hpq : ((n * P.1, n * P.2) : ℤ × ℤ) ≠ (n * Q.1, n * Q.2) := by
    intro h
    refine hPQ ?_
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
    have h1 : n * P.1 = n * Q.1 := congrArg Prod.fst h
    have h2 : n * P.2 = n * Q.2 := congrArg Prod.snd h
    exact Prod.ext (mul_left_cancel₀ hnz h1) (mul_left_cancel₀ hnz h2)
  have hpK : gptH hf ((n * P.1, n * P.2) : ℤ × ℤ) ∉ K' ∪ L' := by
    rw [hfdef, gptH_scaled hnpos P]
    intro hmem
    have h1 : 20 * h₀ ≤ dist x' (gptH h₀ P) := hdx' _ hmem
    have h2 : dist x' (gptH h₀ P) ≤ h₀ := nearGrid_dist hhpos x'
    linarith [hhpos]
  have hbb : ∀ w : ℤ × ℤ, bdry1 ((l₀ : Chain1) : Edge → ZMod 2) w
      = (if w = (n * P.1, n * P.2) then 1 else 0)
        + (if w = (n * Q.1, n * Q.2) then 1 else 0) := by
    intro w
    rw [hl₀eq]
    have h3 : bdry1 ((l₂f + bdry2 WK : Edge → ZMod 2)) w
        = bdry1 (l₂f) w + bdry1 (bdry2 WK) w := by
      rw [bdry1_add]; rfl
    rw [h3, bdry1_bdry2, Pi.zero_apply, add_zero]
    have h2 : bdry1 (l₂f : Edge → ZMod 2) = sub0 n (bdry1 ((l₂ : Chain1) : Edge → ZMod 2)) := by
      rw [hl₂f]; exact bdry1_sub1 hnpos (l₂ : Edge → ZMod 2)
    rw [h2]
    have h4 : bdry1 ((l₂ : Chain1) : Edge → ZMod 2)
        = fun v => (if v = P then (1 : ZMod 2) else 0) + (if v = Q then 1 else 0) := by
      funext v; exact hb₂' v
    rw [h4]
    exact congrFun (sub0_pair hnpos P Q) w
  have hwalk : JoinedIn ((K' ∪ L')ᶜ) (gptH h₀ P) (gptH h₀ Q) := by
    have hmain := joinedIn_of_chain (h := hf) (K := K' ∪ L') (l := l₀)
      (p := (n * P.1, n * P.2)) (q := (n * Q.1, n * Q.2)) hpq hpK hbb hhav
    rw [hfdef] at hmain
    rwa [gptH_scaled hnpos P, gptH_scaled hnpos Q] at hmain
  -- ================= STEP 9: the endpoint segments =================
  have hseg₁ : JoinedIn ((K' ∪ L')ᶜ) x' (gptH h₀ P) :=
    joinedIn_seg hhpos (nearGrid_dist hhpos x') hdx'
  have hseg₂ : JoinedIn ((K' ∪ L')ᶜ) (gptH h₀ Q) y' :=
    (joinedIn_seg hhpos (nearGrid_dist hhpos y') hdy').symm
  have hmain : JoinedIn ((K' ∪ L')ᶜ) x' y' := hseg₁.trans (hwalk.trans hseg₂)
  -- ================= STEP 10: undoing the shift =================
  have hfinal : JoinedIn (((fun z : Pt => z - v) '' (K ∪ L))ᶜ) (x - v) (y - v) := by
    have hset : ((fun z : Pt => z - v) '' (K ∪ L)) = K' ∪ L' := by
      rw [hK', hL', Set.image_union]
    rw [hset, show x - v = x' from hx'.symm, show y - v = y' from hy'.symm]
    exact hmain
  exact (joinedIn_compl_sub_iff (S := K ∪ L) (x := x) (y := y) v).mp hfinal

end

end Grid

/-! ## The reduction -/

/-- **A minimal compact separator in the plane has no cut point.**  If `L ⊆ ℝ²` is compact and
minimal among the compact subsets of itself separating `x` from `y`, and `p ∈ L`, then `L \ {p}`
is preconnected.

Indeed, a disconnection `L \ {p} = A ⊔ B` would give compacta `A ∪ {p}` and `B ∪ {p}` meeting
exactly in `p`, which do not separate `x` from `y` individually (otherwise minimality of `L` would
force `L ⊆ A ∪ {p}` resp. `L ⊆ B ∪ {p}`, impossible since `B ≠ ∅` resp. `A ≠ ∅`), so that the
single-point Janiszewski theorem (`Grid.janis_singleton_plane`) joins `x` to `y` in the complement
of their union, i.e. in `Lᶜ` — contradicting the separating property of `L`. -/
theorem minimal_separator_no_cut_point {L : Set (EuclideanSpace ℝ (Fin 2))} (hLc : IsCompact L)
    (hLpre : IsPreconnected L) {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ L) (hy : y ∉ L)
    (hsep : ¬ JoinedIn (Lᶜ) x y)
    (hmin : ∀ M : Set (EuclideanSpace ℝ (Fin 2)), M ⊆ L → IsCompact M → ¬ JoinedIn (Mᶜ) x y → L ⊆ M)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ L) :
    IsPreconnected (L \ {p}) := by
  classical
  by_contra hnotpre
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hnotpre
  push_neg at hnotpre
  obtain ⟨u, v, hu, hv, huv, hdisj, hnu, hnv⟩ := hnotpre
  set A : Set (EuclideanSpace ℝ (Fin 2)) := (L \ {p}) ∩ u with hA
  set B : Set (EuclideanSpace ℝ (Fin 2)) := (L \ {p}) ∩ v with hB
  have hAne : A.Nonempty := by
    obtain ⟨z, hzLP, hzv⟩ : ∃ z, z ∈ L \ {p} ∧ z ∉ v := by
      by_contra h
      exact hnv (fun z hz => by by_contra hzv; exact h ⟨z, hz, hzv⟩)
    exact ⟨z, hzLP, (huv hzLP).resolve_right hzv⟩
  have hBne : B.Nonempty := by
    obtain ⟨z, hzLP, hzu⟩ : ∃ z, z ∈ L \ {p} ∧ z ∉ u := by
      by_contra h
      exact hnu (fun z hz => by by_contra hzu; exact h ⟨z, hz, hzu⟩)
    exact ⟨z, hzLP, (huv hzLP).resolve_left hzu⟩
  have hABdisj : A ∩ B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨⟨hzL, hzp⟩, hzu⟩, ⟨⟨-, -⟩, hzv⟩⟩
    have hmem : z ∈ (L \ {p}) ∩ (u ∩ v) := ⟨⟨hzL, hzp⟩, hzu, hzv⟩
    rw [hdisj] at hmem
    exact hmem
  have hABcover : A ∪ B = L \ {p} := by
    refine Set.Subset.antisymm ?_ ?_
    · rw [hA, hB]
      refine Set.union_subset (fun z hz => hz.1) (fun z hz => hz.1)
    · intro z hz
      rcases huv hz with hzu | hzv
      · exact Or.inl ⟨hz, hzu⟩
      · exact Or.inr ⟨hz, hzv⟩
  set M₁ : Set (EuclideanSpace ℝ (Fin 2)) := A ∪ {p} with hM₁
  set M₂ : Set (EuclideanSpace ℝ (Fin 2)) := B ∪ {p} with hM₂
  have hM₁eq : M₁ = (L ∩ u) ∪ {p} := by
    rw [hM₁, hA]
    ext z
    constructor
    · rintro (⟨⟨hzL, -⟩, hzu⟩ | hzp)
      · exact Or.inl ⟨hzL, hzu⟩
      · exact Or.inr hzp
    · rintro (⟨hzL, hzu⟩ | hzp)
      · by_cases hzp0 : z ∈ ({p} : Set _)
        · exact Or.inr hzp0
        · exact Or.inl ⟨⟨hzL, hzp0⟩, hzu⟩
      · exact Or.inr hzp
  have hM₂eq : M₂ = (L ∩ v) ∪ {p} := by
    rw [hM₂, hB]
    ext z
    constructor
    · rintro (⟨⟨hzL, -⟩, hzv⟩ | hzp)
      · exact Or.inl ⟨hzL, hzv⟩
      · exact Or.inr hzp
    · rintro (⟨hzL, hzv⟩ | hzp)
      · by_cases hzp0 : z ∈ ({p} : Set _)
        · exact Or.inr hzp0
        · exact Or.inl ⟨⟨hzL, hzp0⟩, hzv⟩
      · exact Or.inr hzp
  have hM₁L : M₁ ⊆ L := by
    rw [hM₁eq]
    rintro z (⟨hzL, -⟩ | hzp)
    · exact hzL
    · rw [Set.mem_singleton_iff] at hzp; rw [hzp]; exact hp
  have hM₂L : M₂ ⊆ L := by
    rw [hM₂eq]
    rintro z (⟨hzL, -⟩ | hzp)
    · exact hzL
    · rw [Set.mem_singleton_iff] at hzp; rw [hzp]; exact hp
  have hM₁cl : IsClosed M₁ := by
    rw [hM₁eq]
    exact (hLc.isClosed.inter hu).union isClosed_singleton
  have hM₂cl : IsClosed M₂ := by
    rw [hM₂eq]
    exact (hLc.isClosed.inter hv).union isClosed_singleton
  have hc₁ : IsCompact M₁ := hLc.of_isClosed_subset hM₁cl hM₁L
  have hc₂ : IsCompact M₂ := hLc.of_isClosed_subset hM₂cl hM₂L
  have hM₁M₂ : M₁ ∩ M₂ = {p} := by
    ext z
    constructor
    · intro hz
      rw [hM₁, hM₂] at hz
      rcases hz.1 with hzA | hzp
      · rcases hz.2 with hzB | hzp'
        · have hmem : z ∈ A ∩ B := ⟨hzA, hzB⟩
          rw [hABdisj] at hmem
          exact absurd hmem (by simp)
        · exact hzp'
      · exact hzp
    · intro hz
      have hzp : z = p := by simpa using hz
      subst hzp
      refine ⟨?_, ?_⟩
      · rw [hM₁]; exact Or.inr rfl
      · rw [hM₂]; exact Or.inr rfl
  have hM₁M₂cover : M₁ ∪ M₂ = L := by
    rw [hM₁, hM₂, hA, hB]
    ext z
    constructor
    · rintro (((⟨⟨hzL, -⟩, -⟩ | hzp) | (⟨⟨hzL, -⟩, -⟩ | hzp)))
      · exact hzL
      · rw [Set.mem_singleton_iff] at hzp; rw [hzp]; exact hp
      · exact hzL
      · rw [Set.mem_singleton_iff] at hzp; rw [hzp]; exact hp
    · intro hz
      by_cases hzp : z = p
      · exact Or.inl (Or.inr (by rw [Set.mem_singleton_iff]; exact hzp))
      · have hz' : z ∈ L \ {p} := ⟨hz, by simpa [Set.mem_singleton_iff] using hzp⟩
        rcases huv hz' with h | h
        · exact Or.inl (Or.inl ⟨hz', h⟩)
        · exact Or.inr (Or.inl ⟨hz', h⟩)
  have hjoin₁ : JoinedIn (M₁ᶜ) x y := by
    by_contra hcon
    have hsub : L ⊆ M₁ := hmin M₁ hM₁L hc₁ hcon
    obtain ⟨z, hzB⟩ := hBne
    have hzM : z ∈ M₁ := hsub hzB.1.1
    rcases hzM with hzA | hzp
    · have hmem : z ∈ A ∩ B := ⟨hzA, hzB⟩
      rw [hABdisj] at hmem
      exact hmem
    · exact hzB.1.2 hzp
  have hjoin₂ : JoinedIn (M₂ᶜ) x y := by
    by_contra hcon
    have hsub : L ⊆ M₂ := hmin M₂ hM₂L hc₂ hcon
    obtain ⟨z, hzA⟩ := hAne
    have hzM : z ∈ M₂ := hsub hzA.1.1
    rcases hzM with hzB | hzp
    · have hmem : z ∈ A ∩ B := ⟨hzA, hzB⟩
      rw [hABdisj] at hmem
      exact hmem
    · exact hzA.1.2 hzp
  have hx' : x ∉ M₁ ∪ M₂ := by rw [hM₁M₂cover]; exact hx
  have hy' : y ∉ M₁ ∪ M₂ := by rw [hM₁M₂cover]; exact hy
  have hfin := Grid.janis_singleton_plane hc₁ hc₂ hM₁M₂ hx' hy' hjoin₁ hjoin₂
  rw [hM₁M₂cover] at hfin
  exact hsep hfin

end Work.Whitney.PathTools
