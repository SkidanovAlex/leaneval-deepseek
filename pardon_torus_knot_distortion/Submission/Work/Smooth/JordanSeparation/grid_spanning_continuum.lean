import Mathlib
import Submission.Work.Smooth.SphereJordan.hexDualityFinite
import Submission.Work.Smooth.JordanSeparation.neighbourhood_continuum
import Submission.Work.Smooth.JordanSeparation.squareGrid

/-!
# A closed separator of the bottom edge from the top edge of the square
contains a continuum joining the left edge to the right edge.

The proof uses the finite `4`/`8` Hex duality (`Work.Smooth.SphereJordan.hexDualityFinite`)
together with `Work.Smooth.JordanSeparation.neighbourhood_continuum`: for every `ε > 0` the Hex
duality produces a compact connected set inside the `ε`-neighbourhood of `Z` meeting both the
left and the right edge, and the Hausdorff limit of these continua gives the desired continuum in
`Z`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric
open scoped Topology

noncomputable section

/-- Two cells of an `N × N` grid share an edge. -/
def gAdj4 {N : ℕ} (a b : Fin N × Fin N) : Prop :=
  (a.1 = b.1 ∧ (a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)) ∨
  (a.2 = b.2 ∧ (a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1))

/-- Two cells of an `N × N` grid share an edge or a corner. -/
def gAdj8 {N : ℕ} (a b : Fin N × Fin N) : Prop :=
  (a.1 = b.1 ∨ a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1) ∧
  (a.2 = b.2 ∨ a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)

theorem gAdj4_imp_gAdj8 {N : ℕ} {a b : Fin N × Fin N} (h : gAdj4 a b) : gAdj8 a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · exact ⟨Or.inl h1, h2.elim (fun x => Or.inr (Or.inl x)) (fun x => Or.inr (Or.inr x))⟩
  · exact ⟨h1.elim (fun x => Or.inr (Or.inl x)) (fun x => Or.inr (Or.inr x)), Or.inl h2⟩

/-- Two unit grid intervals whose indices are equal or differ by one overlap. -/
theorem gridIcc_inter_nonempty {N : ℕ} (hN : 0 < N) {i i' : Fin N}
    (h : i = i' ∨ i.1 + 1 = i'.1 ∨ i'.1 + 1 = i.1) :
    (Icc ((i:ℝ)/N) (((i:ℝ)+1)/N) ∩ Icc ((i':ℝ)/N) (((i':ℝ)+1)/N)).Nonempty := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hle : (i:ℝ) ≤ (i':ℝ) + 1 := by
    rcases h with h | h | h
    · subst h; linarith
    · have := nat_cast_eq_add_one h; linarith
    · have := nat_cast_eq_add_one h; linarith
  have hle' : (i':ℝ) ≤ (i:ℝ) + 1 := by
    rcases h with h | h | h
    · subst h; linarith
    · have := nat_cast_eq_add_one h; linarith
    · have := nat_cast_eq_add_one h; linarith
  have hA : (i:ℝ)/N ≤ ((i':ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  have hB : (i':ℝ)/N ≤ ((i:ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  have hC : (i:ℝ)/N ≤ ((i:ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  have hD : (i':ℝ)/N ≤ ((i':ℝ)+1)/N := by
    rw [div_le_div_iff_of_pos_right hNpos]; linarith
  exact ⟨max ((i:ℝ)/N) ((i':ℝ)/N), ⟨le_max_left _ _, max_le hC hB⟩,
    ⟨le_max_right _ _, max_le hA hD⟩⟩

/-- Two `8`-adjacent cells of the `N × N` grid meet. -/
theorem inter_nonempty_of_gAdj8 {N : ℕ} (hN : 0 < N) {a b : Fin N × Fin N}
    (h : gAdj8 a b) : (cell N a.1 a.2 ∩ cell N b.1 b.2).Nonempty := by
  obtain ⟨hcol, hrow⟩ := h
  obtain ⟨x, hx⟩ := gridIcc_inter_nonempty hN hcol
  obtain ⟨y, hy⟩ := gridIcc_inter_nonempty hN hrow
  refine ⟨(x, y), ?_, ?_⟩ <;> rw [cell, mem_prod]
  · exact ⟨hx.1, hy.1⟩
  · exact ⟨hx.2, hy.2⟩

/-- **A closed separator of the bottom edge from the top edge of the square contains a continuum
joining the left edge to the right edge.**  Here `Z` is a closed subset of the unit square `Q`
disjoint from the bottom edge `[0,1] × {0}` and the top edge `[0,1] × {1}`, and the hypothesis
`hsep` says that no preconnected subset of `Q \ Z` meets both the bottom edge and the top edge
(equivalently, `Z` separates the bottom edge from the top edge inside `Q`). -/
theorem grid_spanning_continuum {Z : Set (ℝ × ℝ)} (hZc : IsClosed Z)
    (hZQ : Z ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (hB : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅)
    (hsep : ∀ P : Set (ℝ × ℝ), P ⊆ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z → IsPreconnected P →
        (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ))).Nonempty →
        (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ))).Nonempty → False) :
    ∃ K : Set (ℝ × ℝ), K ⊆ Z ∧ IsConnected K ∧
      (K ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
      (K ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
  classical
  -- `Z` is nonempty, else the whole square would be a forbidden preconnected set.
  have hZne : Z.Nonempty := by
    rcases Z.eq_empty_or_nonempty with h | h
    · exfalso
      refine hsep (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ?_ ?_ ?_ ?_
      · rw [h, Set.sdiff_empty]
      · exact ((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)).isPreconnected
      · exact ⟨(0,0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩,
          ⟨⟨le_rfl, zero_le_one⟩, rfl⟩⟩
      · exact ⟨(0,1), ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩,
          ⟨⟨le_rfl, zero_le_one⟩, rfl⟩⟩
    · exact h
  -- It suffices to approximate `Z` by continua meeting both vertical edges.
  have hmain : ∀ ε > 0, ∃ U : Set (ℝ × ℝ), U ⊆ {p : ℝ × ℝ | Metric.infDist p Z < ε} ∧
      IsCompact U ∧ IsConnected U ∧
      (U ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
      (U ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
    intro ε hε
    -- a mesh size `1/N` much smaller than `ε`
    obtain ⟨N, hNpos, hNlt⟩ : ∃ N : ℕ, 0 < N ∧ (2:ℝ)/N < ε := by
      obtain ⟨k, hk⟩ := exists_nat_gt (2/ε)
      have hkpos : (0:ℝ) < (k:ℝ) := lt_trans (by positivity) hk
      refine ⟨k, by exact_mod_cast hkpos, ?_⟩
      rw [div_lt_iff₀ hkpos]
      have hmul : (2/ε) * ε < (k:ℝ) * ε := mul_lt_mul_of_pos_right hk hε
      have h2 : (2/ε) * ε = 2 := div_mul_cancel₀ 2 (ne_of_gt hε)
      linarith
    have hNposR : (0:ℝ) < N := by exact_mod_cast hNpos
    have hNle : (0:ℝ) ≤ N := hNposR.le
    set blocked : Fin N × Fin N → Prop := fun c => (cell N c.1 c.2 ∩ Z).Nonempty with hblocked
    rcases Work.Smooth.SphereJordan.hexDualityFinite hNpos blocked with
      ⟨m, f, hfree, hadj4, h0row, hlastrow⟩ | ⟨m, f, hblk, hadj8, h0col, hlastcol⟩
    · -- A free `4`-chain from the bottom row to the top row contradicts `hsep`.
      exfalso
      have hfree' : ∀ i : Fin (m+1), cell N (f i).1 (f i).2 ∩ Z = ∅ := by
        intro i
        have h := hfree i
        rw [hblocked] at h
        exact Set.not_nonempty_iff_eq_empty.mp h
      have hVpre : IsPreconnected (⋃ i : Fin (m+1), cell N (f i).1 (f i).2) :=
        isPreconnected_iUnion_range (fun i => isPreconnected_cell _ _)
          (fun i => inter_nonempty_of_gAdj8 hNpos
            (gAdj4_imp_gAdj8 (show gAdj4 (f i.castSucc) (f i.succ) from hadj4 i)))
      have hVsub : (⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ⊆ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z := by
        intro p hp
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        refine ⟨cell_subset_sqUnit hNpos _ _ hi, ?_⟩
        intro hpZ
        exact (Set.eq_empty_iff_forall_notMem.mp (hfree' i)) p ⟨hi, hpZ⟩
      have hVbot : ((⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ))).Nonempty := by
        have hcell : (((f 0).1.1 : ℝ)/N, (0:ℝ)) ∈ cell N (f 0).1 (f 0).2 := by
          rw [mem_cell_iff]
          have hj : ((f 0).2.1 : ℝ) = 0 := by rw [h0row]; simp
          exact ⟨le_rfl, by rw [div_le_div_iff_of_pos_right hNposR]; linarith,
            by rw [hj]; simp, by rw [hj]; positivity⟩
        refine ⟨_, ⟨mem_iUnion.mpr ⟨0, hcell⟩, ?_⟩⟩
        rw [mem_prod]
        exact ⟨⟨by positivity, by rw [div_le_one hNposR]; exact_mod_cast le_of_lt (f 0).1.2⟩,
          rfl⟩
      have hVtop : ((⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ))).Nonempty := by
        have hrow : ((f (Fin.last m)).2.1 : ℝ) = (N:ℝ) - 1 := by
          have := nat_cast_eq_add_one hlastrow; linarith
        have hcell : (((f (Fin.last m)).1.1 : ℝ)/N, (1:ℝ))
            ∈ cell N (f (Fin.last m)).1 (f (Fin.last m)).2 := by
          rw [mem_cell_iff]
          refine ⟨le_rfl, by rw [div_le_div_iff_of_pos_right hNposR]; linarith,
            by rw [hrow]; rw [div_le_one hNposR]; linarith, ?_⟩
          rw [hrow, show ((N:ℝ) - 1) + 1 = N by ring, div_self (ne_of_gt hNposR)]
        refine ⟨_, ⟨mem_iUnion.mpr ⟨Fin.last m, hcell⟩, ?_⟩⟩
        rw [mem_prod]
        exact ⟨⟨by positivity, by rw [div_le_one hNposR]; exact_mod_cast le_of_lt (f (Fin.last m)).1.2⟩,
          rfl⟩
      exact hsep _ hVsub hVpre hVbot hVtop
    · -- A blocked `8`-chain from the left column to the right column gives the continuum.
      have hblk' : ∀ i : Fin (m+1), (cell N (f i).1 (f i).2 ∩ Z).Nonempty := by
        intro i; have h := hblk i; rwa [hblocked] at h
      have hUpre : IsPreconnected (⋃ i : Fin (m+1), cell N (f i).1 (f i).2) :=
        isPreconnected_iUnion_range (fun i => isPreconnected_cell _ _)
          (fun i => inter_nonempty_of_gAdj8 hNpos
            (show gAdj8 (f i.castSucc) (f i.succ) from hadj8 i))
      have hUcomp : IsCompact (⋃ i : Fin (m+1), cell N (f i).1 (f i).2) := by
        refine isCompact_iUnion (fun i => ?_)
        exact isCompact_Icc.prod isCompact_Icc
      have hUsub : (⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ⊆ {p : ℝ × ℝ | Metric.infDist p Z < ε} := by
        intro p hp
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        obtain ⟨z, hzcell, hzZ⟩ := hblk' i
        have hdist : dist p z < ε := by
          have h2 : dist p z ≤ 2/N :=
            dist_le_of_cells hNpos hi hzcell (by linarith) (by linarith)
              (by linarith) (by linarith)
          linarith
        exact (Metric.infDist_lt_iff hZne).mpr ⟨z, hzZ, hdist⟩
      have hUL : ((⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
        have hcell : (((f 0).1.1 : ℝ)/N, ((f 0).2.1 : ℝ)/N) ∈ cell N (f 0).1 (f 0).2 := by
          rw [mem_cell_iff]
          exact ⟨le_rfl, by rw [div_le_div_iff_of_pos_right hNposR]; linarith,
            le_rfl, by rw [div_le_div_iff_of_pos_right hNposR]; linarith⟩
        refine ⟨_, ⟨mem_iUnion.mpr ⟨0, hcell⟩, ?_⟩⟩
        rw [mem_prod]
        have h0 : ((f 0).1.1 : ℝ) = 0 := by rw [h0col]; simp
        refine ⟨?_, ?_⟩
        · simp [h0]
        · refine ⟨by positivity, ?_⟩
          rw [div_le_one hNposR]; exact_mod_cast le_of_lt (f 0).2.2
      have hUR : ((⋃ i : Fin (m+1), cell N (f i).1 (f i).2)
          ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
        have hcol : ((f (Fin.last m)).1.1 : ℝ) + 1 = N := (nat_cast_eq_add_one hlastcol).symm
        have hcell : ((1:ℝ), ((f (Fin.last m)).2.1 : ℝ)/N)
            ∈ cell N (f (Fin.last m)).1 (f (Fin.last m)).2 := by
          rw [mem_cell_iff]
          refine ⟨by rw [div_le_one hNposR]; exact_mod_cast le_of_lt (f (Fin.last m)).1.2,
            by rw [hcol, div_self (ne_of_gt hNposR)], le_rfl,
            by rw [div_le_div_iff_of_pos_right hNposR]; linarith⟩
        refine ⟨_, ⟨mem_iUnion.mpr ⟨Fin.last m, hcell⟩, ?_⟩⟩
        rw [mem_prod]
        refine ⟨rfl, ?_, ?_⟩
        · positivity
        · rw [div_le_one hNposR]; exact_mod_cast le_of_lt (f (Fin.last m)).2.2
      exact ⟨_, hUsub, hUcomp, ⟨(hUL.mono Set.inter_subset_left), hUpre⟩, hUL, hUR⟩
  obtain ⟨K, hKZ, _, hKconn, hKL, hKR⟩ := neighbourhood_continuum hZc hZne hZQ hmain
  exact ⟨K, hKZ, hKconn, hKL, hKR⟩

end

end Work.Smooth.JordanSeparation
