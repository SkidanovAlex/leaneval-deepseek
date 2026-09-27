import Submission.Work.PL.Subdiv.Cube.Level
import Submission.Work.PL.Subdiv.Cube.convexHull_unitVerts
import Submission.Work.PL.Subdiv.Cube.mem_unitVerts_iff

/-!
# The Freudenthal simplices of neighbouring grid cells meet in a common face

Given `y ∈ unitSimp π` whose translate `y - cellPt c' + cellPt c` lies in `unitSimp π'`, every
vertex `wvec π k` of `unitSimp π` that receives positive level weight at `y` translates into a
`{0,1}`-point of `unitSimp π'`.  This is the key step in proving that two Freudenthal simplices of
adjacent grid cells intersect in the common face spanned by their common vertices.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

lemma sub_cellPt_apply (c c' : Fin n → ℕ) (y : PL.E n) (i : Fin n) :
    (y - cellPt c' + cellPt c) i = y i - (c' i : ℝ) + (c i : ℝ) := by
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply, cellPt_apply]

lemma wvec_sub_cellPt_apply {c c' : Fin n → ℕ} {π : Equiv.Perm (Fin n)} (k : ℕ) (i : Fin n) :
    (wvec π k - cellPt c' + cellPt c) i = wvec π k i - (c' i : ℝ) + (c i : ℝ) := by
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply, cellPt_apply]

/-- `levf` is non-negative on the simplex. -/
lemma levf_nonneg (π : Equiv.Perm (Fin n)) (y : PL.E n) (hy : y ∈ unitSimp π) (j : ℕ) :
    0 ≤ levf π y j := by
  rcases lt_or_ge j n with h | h
  · rw [levf_lt π y h]
    exact (hy.1 _).1
  · rw [levf_ge π y (not_lt.mpr h)]
    norm_num

/-- A positive level weight forces a positive level. -/
lemma levf_pos_of_lev_pos (π : Equiv.Perm (Fin n)) (y : PL.E n) (hy : y ∈ unitSimp π)
    {k : ℕ} (hpos : 0 < lev π k y) : 0 < levf π y k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rwa [lev_zero] at hpos
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    rw [lev_succ] at hpos
    have := levf_nonneg π y hy m
    linarith

/-- **Vertex transfer.** If `y ∈ unitSimp π` and its translate `y - cellPt c' + cellPt c` lies in
`unitSimp π'`, then every vertex `wvec π k` carrying positive level weight at `y` translates into a
`{0,1}`-point of `unitSimp π'`. -/
theorem wvec_sub_mem_unitSimp {c c' : Fin n → ℕ} {π π' : Equiv.Perm (Fin n)} {y : PL.E n}
    (hy : y ∈ unitSimp π) (hy' : y - cellPt c' + cellPt c ∈ unitSimp π')
    {k : ℕ} (hk : k ≤ n) (hpos : 0 < lev π k y) :
    (wvec π k - cellPt c' + cellPt c ∈ unitSimp π') ∧
      (∀ i, (wvec π k - cellPt c' + cellPt c) i = 0 ∨
            (wvec π k - cellPt c' + cellPt c) i = 1) := by
  have hΛpos : 0 < levf π y k := levf_pos_of_lev_pos π y hy hpos
  have hΛ1 : levf π y k ≤ 1 := by
    rcases lt_or_ge k n with h | h
    · rw [levf_lt π y h]; exact (hy.1 _).2
    · exact le_of_eq (levf_ge π y (not_lt.mpr h))
  have hlevf_eq : ∀ a : Fin n, y (π a) = levf π y (a : ℕ) := by
    intro a
    rw [levf_lt π y a.isLt, show (⟨(a : ℕ), a.isLt⟩ : Fin n) = a from Fin.ext rfl]
  have hbdd : ∀ i, -1 ≤ (c' i : ℝ) - (c i : ℝ) ∧ (c' i : ℝ) - (c i : ℝ) ≤ 1 := by
    intro i
    have h1 := (hy'.1 i).1
    have h2 := (hy'.1 i).2
    have h3 := (hy.1 i).1
    have h4 := (hy.1 i).2
    rw [sub_cellPt_apply] at h1 h2
    constructor <;> linarith
  have hcases : ∀ i, ((c' i : ℝ) - (c i : ℝ)) = -1 ∨ ((c' i : ℝ) - (c i : ℝ)) = 0 ∨
      ((c' i : ℝ) - (c i : ℝ)) = 1 := by
    intro i
    have hcast : (c' i : ℝ) - (c i : ℝ) = (((c' i : ℤ) - (c i : ℤ) : ℤ) : ℝ) := by
      simp
    have h1 : (-1 : ℤ) ≤ (c' i : ℤ) - (c i : ℤ) := by
      have h : (-1 : ℝ) ≤ (((c' i : ℤ) - (c i : ℤ) : ℤ) : ℝ) := by
        rw [← hcast]; exact (hbdd i).1
      exact_mod_cast h
    have h2 : (c' i : ℤ) - (c i : ℤ) ≤ 1 := by
      have h : (((c' i : ℤ) - (c i : ℤ) : ℤ) : ℝ) ≤ (1 : ℝ) := by
        rw [← hcast]; exact (hbdd i).2
      exact_mod_cast h
    have hz : (c' i : ℤ) - (c i : ℤ) = -1 ∨ (c' i : ℤ) - (c i : ℤ) = 0 ∨
        (c' i : ℤ) - (c i : ℤ) = 1 := by omega
    rcases hz with h | h | h
    · left; rw [hcast, h]; norm_num
    · right; left; rw [hcast, h]; norm_num
    · right; right; rw [hcast, h]; norm_num
  have hy_one : ∀ i, (c' i : ℝ) - (c i : ℝ) = 1 → y i = 1 := by
    intro i hd
    have h := (hy'.1 i).1
    rw [sub_cellPt_apply] at h
    linarith [(hy.1 i).2]
  have hy_zero : ∀ i, (c' i : ℝ) - (c i : ℝ) = -1 → y i = 0 := by
    intro i hd
    have h := (hy'.1 i).2
    rw [sub_cellPt_apply] at h
    linarith [(hy.1 i).1]
  have hle_of_one : ∀ a : Fin n, (c' (π a) : ℝ) - (c (π a) : ℝ) = 1 → k ≤ (a : ℕ) := by
    intro a hd
    have hyi1 : y (π a) = 1 := hy_one (π a) hd
    by_contra hnot
    have hlt : (a : ℕ) < k := Nat.lt_of_not_le hnot
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
      have hmono : levf π y (a : ℕ) ≤ levf π y m := levf_mono π y hy (by omega) (by omega)
      have h1 : levf π y (m + 1) ≤ 1 := by
        rcases lt_or_ge (m + 1) n with h | h
        · rw [levf_lt π y h]; exact (hy.1 _).2
        · exact le_of_eq (levf_ge π y (not_lt.mpr h))
      rw [← hlevf_eq a, hyi1] at hmono
      rw [lev_succ] at hpos
      linarith
  have hlt_of_neg : ∀ a : Fin n, (c' (π a) : ℝ) - (c (π a) : ℝ) = -1 → (a : ℕ) < k := by
    intro a hd
    have hyi0 : y (π a) = 0 := hy_zero (π a) hd
    by_contra hnot
    have hge : k ≤ (a : ℕ) := Nat.le_of_not_lt hnot
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
      have hmono : y (π ⟨0, hn⟩) ≤ y (π a) := hy.2 ⟨0, hn⟩ a (Nat.zero_le _)
      rw [lev_zero, levf_lt π y hn] at hpos
      rw [hyi0] at hmono
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
      have hmono : levf π y (m + 1) ≤ levf π y (a : ℕ) :=
        levf_mono π y hy (j := m + 1) (j' := (a : ℕ)) (by omega) (le_of_lt a.isLt)
      rw [← hlevf_eq a, hyi0] at hmono
      rw [lev_succ] at hpos
      have := levf_nonneg π y hy m
      linarith
  have hw' : ∀ (a : Fin n), (wvec π k - cellPt c' + cellPt c) (π a)
      = (if k ≤ (a : ℕ) then (1 : ℝ) else 0) - ((c' (π a) : ℝ) - (c (π a) : ℝ)) := by
    intro a; rw [wvec_sub_cellPt_apply, wvec_at]; ring
  have hyw' : ∀ (a : Fin n), (y - cellPt c' + cellPt c) (π a)
      = y (π a) - ((c' (π a) : ℝ) - (c (π a) : ℝ)) := by
    intro a; rw [sub_cellPt_apply]; ring
  have h01 : ∀ i, (wvec π k - cellPt c' + cellPt c) i = 0 ∨
      (wvec π k - cellPt c' + cellPt c) i = 1 := by
    intro i
    obtain ⟨a, rfl⟩ : ∃ a, π a = i := ⟨π.symm i, by simp⟩
    rw [hw' a]
    rcases hcases (π a) with hd | hd | hd
    · right
      have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 0 := by
        rw [if_neg (Nat.not_le.mpr (hlt_of_neg a hd))]
      rw [hif, hd]; norm_num
    · rcases lt_or_ge (a : ℕ) k with h | h
      · left
        have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 0 := by
          rw [if_neg (Nat.not_le.mpr h)]
        rw [hif, hd]; norm_num
      · right
        have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 := by rw [if_pos h]
        rw [hif, hd]; norm_num
    · left
      have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 := by
        rw [if_pos (hle_of_one a hd)]
      rw [hif, hd]; norm_num
  have hA : ∀ i, (wvec π k - cellPt c' + cellPt c) i = 1 →
      levf π y k ≤ (y - cellPt c' + cellPt c) i := by
    intro i hv
    obtain ⟨a, rfl⟩ : ∃ a, π a = i := ⟨π.symm i, by simp⟩
    rw [hw' a] at hv
    rw [hyw' a]
    rcases hcases (π a) with hd | hd | hd
    · rw [hd]
      have h0 : 0 ≤ y (π a) := (hy.1 _).1
      linarith [hΛ1]
    · have hv' : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 := by linarith
      have hk' : k ≤ (a : ℕ) := by
        by_contra hnot
        rw [if_neg (Nat.not_le.mpr (Nat.lt_of_not_le hnot))] at hv'
        norm_num at hv'
      rw [hd]
      rw [show y (π a) - 0 = y (π a) from by ring, hlevf_eq a]
      exact levf_mono π y hy hk' (le_of_lt a.isLt)
    · have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 := by
        rw [if_pos (hle_of_one a hd)]
      rw [hif] at hv
      linarith
  have hB : ∀ i, (wvec π k - cellPt c' + cellPt c) i = 0 →
      (y - cellPt c' + cellPt c) i < levf π y k := by
    intro i hv
    obtain ⟨a, rfl⟩ : ∃ a, π a = i := ⟨π.symm i, by simp⟩
    rw [hw' a] at hv
    rw [hyw' a]
    rcases hcases (π a) with hd | hd | hd
    · have hif : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 0 := by
        rw [if_neg (Nat.not_le.mpr (hlt_of_neg a hd))]
      rw [hif] at hv
      linarith
    · have hv' : (if k ≤ (a : ℕ) then (1 : ℝ) else 0) = 0 := by linarith
      have hlt : (a : ℕ) < k := by
        by_contra hnot
        rw [if_pos (Nat.le_of_not_lt hnot)] at hv'
        norm_num at hv'
      rw [hd]
      rw [show y (π a) - 0 = y (π a) from by ring, hlevf_eq a]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · omega
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
        have hmono : levf π y (a : ℕ) ≤ levf π y m := levf_mono π y hy (by omega) (by omega)
        rw [lev_succ] at hpos
        linarith
    · have hy1 : y (π a) = 1 := hy_one (π a) hd
      rw [hd, hy1]
      linarith [hΛpos]
  refine ⟨⟨fun i => ?_, fun a b hab => ?_⟩, h01⟩
  · rcases h01 i with h | h <;> rw [h] <;> norm_num
  · rcases h01 (π' a) with ha | ha <;> rcases h01 (π' b) with hb | hb
    · rw [ha, hb] <;> norm_num
    · rw [ha, hb] <;> norm_num
    · exfalso
      have hu := hy'.2 a b hab
      have h1 := hA (π' a) ha
      have h2 := hB (π' b) hb
      linarith
    · rw [ha, hb] <;> norm_num


/-- The sum of the level weights is `1`. -/
lemma sum_lev_eq_one (π : Equiv.Perm (Fin n)) (y : PL.E n) :
    ∑ k ∈ Finset.range (n + 1), lev π k y = 1 := by
  rw [sum_lev π y n, levf_ge π y (by omega)]

/-- The convex hull of the vertices of the grid cell `c` for the order `π`. -/
lemma convexHull_cellVerts (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    convexHull ℝ (cellVerts c π : Set (PL.E n)) = (fun y => cellPt c + y) '' unitSimp π := by
  have hcoe : (cellVerts c π : Set (PL.E n)) = (fun y => cellPt c + y) '' (unitVerts π : Set _) := by
    rw [cellVerts, Finset.coe_image]
  rw [hcoe, show convexHull ℝ ((fun y => cellPt c + y) '' (unitVerts π : Set _)) =
      (fun y => cellPt c + y) '' convexHull ℝ ((unitVerts π : Finset (PL.E n)) : Set _) from ?_,
    convexHull_unitVerts]
  have := (AffineEquiv.constVAdd ℝ (PL.E n) (cellPt c)).toAffineMap.image_convexHull
    ((unitVerts π : Finset (PL.E n)) : Set _)
  simpa using this.symm


/-- **Two grid simplices meet in a common face.**  The convex hulls of two Freudenthal simplices
(of arbitrary grid cells and orders) intersect exactly in the convex hull of the intersection of
their vertex sets. -/
theorem convexHull_inter_cellVerts (c c' : Fin n → ℕ) (π π' : Equiv.Perm (Fin n)) :
    convexHull ℝ (((cellVerts c π ∩ cellVerts c' π') : Finset (PL.E n)) : Set (PL.E n)) =
      convexHull ℝ (cellVerts c π : Set (PL.E n)) ∩
      convexHull ℝ (cellVerts c' π' : Set (PL.E n)) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine subset_inter ?_ ?_
    · exact convexHull_mono (fun x hx => (Finset.mem_inter.mp (Finset.mem_coe.mp hx)).1)
    · exact convexHull_mono (fun x hx => (Finset.mem_inter.mp (Finset.mem_coe.mp hx)).2)
  · intro z hz
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [convexHull_cellVerts] at hz1 hz2
    obtain ⟨y, hy, hyz⟩ := hz1
    have hy' : y - cellPt c' + cellPt c ∈ unitSimp π' := by
      obtain ⟨y₂, hy₂, hy₂eq⟩ := hz2
      have h1 : cellPt c + y = cellPt c' + y₂ := hyz.trans hy₂eq.symm
      have h2 : y - cellPt c' + cellPt c = y₂ := by
        rw [show y - cellPt c' + cellPt c = (cellPt c + y) - cellPt c' from by abel, h1]
        abel
      rw [h2]; exact hy₂
    have hz_eq : z = ∑ k ∈ Finset.range (n + 1), lev π k y • (cellPt c + wvec π k) := by
      have key : (∑ k ∈ Finset.range (n + 1), lev π k y • (cellPt c + wvec π k))
          = cellPt c + y := by
        rw [Finset.sum_congr rfl (fun k _ => smul_add (lev π k y) (cellPt c) (wvec π k)),
          Finset.sum_add_distrib, ← Finset.sum_smul, sum_lev_eq_one, one_smul,
          sum_lev_smul_wvec π y]
      rw [key, ← hyz]
    have hmem : ∀ k ∈ Finset.range (n + 1), lev π k y ≠ 0 →
        cellPt c + wvec π k ∈
          ((cellVerts c π ∩ cellVerts c' π' : Finset (PL.E n)) : Set (PL.E n)) := by
      intro k hk hne
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpos : 0 < lev π k y := lt_of_le_of_ne (lev_nonneg π y hy hkn) (Ne.symm hne)
      have ht := wvec_sub_mem_unitSimp hy hy' hkn hpos
      have hw' : wvec π k - cellPt c' + cellPt c ∈ unitVerts π' := by
        rw [mem_unitVerts_iff]
        exact ⟨ht.2, ht.1.2⟩
      rw [Finset.mem_coe, Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · rw [cellVerts_eq]
        exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
      · rw [cellVerts]
        refine Finset.mem_image.mpr ⟨wvec π k - cellPt c' + cellPt c, hw', ?_⟩
        abel
    set T := (Finset.range (n + 1)).filter (fun k => lev π k y ≠ 0) with hT
    have hTsub : T ⊆ Finset.range (n + 1) := Finset.filter_subset _ _
    have hsumT : ∑ k ∈ T, lev π k y = 1 := by
      rw [← sum_lev_eq_one π y]
      refine Finset.sum_subset hTsub ?_
      intro x hx hxT
      by_contra h
      exact hxT (Finset.mem_filter.mpr ⟨hx, h⟩)
    have hsumT' : ∑ k ∈ T, lev π k y • (cellPt c + wvec π k)
        = ∑ k ∈ Finset.range (n + 1), lev π k y • (cellPt c + wvec π k) := by
      refine Finset.sum_subset hTsub ?_
      intro x hx hxT
      have : lev π x y = 0 := by
        by_contra h
        exact hxT (Finset.mem_filter.mpr ⟨hx, h⟩)
      rw [this, zero_smul]
    rw [hz_eq, ← hsumT']
    refine Convex.sum_mem (convex_convexHull ℝ _) ?_ ?_ ?_
    · intro k hk
      exact lev_nonneg π y hy (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))
    · exact hsumT
    · intro k hk
      exact subset_convexHull ℝ _ (hmem k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)

end

end Work.PL.Subdiv.Cube
