import Mathlib
import Submission.Work.Whitney.PathTools.exists_arc_of_isPathConnected
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen

/-!
# Reaching, and leaving, a collar

Step 1 of the `(EXIT)` construction of the spine recursion
(`NOTES_pocketFree_collar_SESSION.md` §3).  Let `C` be the routing carrier (in the application the
component of the start point in the complement of the *previous* collar, minus the obstacles), an
open preconnected set whose closure is non-compact, and let `L` be the current collar, contained in
a compact set `K`.  For a start point `s ∈ C ∩ L` there is

* an injective arc `α` from `s` inside `C` to a point `α 1 ∉ L` (possible because `C` is not
  contained in the compact set `K`, and open preconnected sets in manifolds are path connected);
* a time `t` which is the **first exit** of `α` from the closed set `L`: `α u ∈ L` for `u ≤ t`
  and `α t ∈ frontier L`.

The initial piece `α '' [0,t]` is the "inside" part of the level-`ℓ` arc; the point `α t` is where
the arc enters the collar's complement, from which the tip is reached
(`exists_tip_component_of_entry`).
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.Noncompact.CompressionTube

open Set Topology

theorem exists_arc_first_exit_of_collar {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C L K : Set M} (hC : IsOpen C) (hCc : IsPreconnected C) (hLc : IsClosed L)
    (hKc : IsCompact K) (hLK : L ⊆ K) {s : M} (hsC : s ∈ C) (hsL : s ∈ L)
    (hnt : ¬ IsCompact (closure C)) :
    ∃ (α : ℝ → M) (t : ℝ), Continuous α ∧ Set.InjOn α (Set.Icc (0:ℝ) 1) ∧ α 0 = s ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, α u ∈ C) ∧ α 1 ∉ L ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      (∀ u ∈ Set.Icc (0:ℝ) t, α u ∈ L) ∧ α t ∈ frontier L := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  -- a point of `C` outside the compact set `K ⊇ L`
  have hnotsub : ¬ C ⊆ K := by
    intro hsub
    exact hnt (hKc.of_isClosed_subset isClosed_closure (closure_minimal hsub hKc.isClosed))
  obtain ⟨y, hyC, hyK⟩ := Set.not_subset.mp hnotsub
  have hyL : y ∉ L := fun h => hyK (hLK h)
  have hsy : s ≠ y := fun h => hyL (h ▸ hsL)
  -- an arc from `s` to `y` inside `C`
  have hpath : IsPathConnected C :=
    hC.isConnected_iff_isPathConnected.mp ⟨⟨s, hsC⟩, hCc⟩
  obtain ⟨α, hαc, hαinj, hα0, hα1, hαC⟩ :=
    Work.Whitney.PathTools.exists_arc_of_isPathConnected (n := n) hC hpath hsC hyC hsy
  -- the first exit from `L`
  set T : Set ℝ := {u : ℝ | u ∈ Set.Icc (0:ℝ) 1 ∧ α u ∉ L} with hTdef
  have h1T : (1:ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by rw [hα1]; exact hyL⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hlow : ∀ b ∈ T, (0:ℝ) ≤ b := fun b hb => hb.1.1
  have hbdd : BddBelow T := ⟨0, hlow⟩
  have hmem_of : ∀ u, u ∈ Set.Icc (0:ℝ) 1 → α u ∉ L → u ∈ T := fun u h1 h2 => ⟨h1, h2⟩
  have ht0 : (0:ℝ) ≤ sInf T := le_csInf hTne hlow
  have ht1 : sInf T ≤ 1 := csInf_le hbdd h1T
  have hpre : ∀ u ∈ Set.Ico (0:ℝ) (sInf T), α u ∈ L := by
    intro u hu
    by_contra hcon
    exact absurd (csInf_le hbdd (hmem_of u ⟨hu.1, le_trans hu.2.le ht1⟩ hcon)) (not_le.mpr hu.2)
  have htL : α (sInf T) ∈ L := by
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h, hα0]; exact hsL
    · have hcl : sInf T ∈ closure (Set.Ico (0:ℝ) (sInf T)) := by
        have hmono : Set.Ioo (0:ℝ) (sInf T) ⊆ Set.Ico (0:ℝ) (sInf T) :=
          fun u hu => ⟨hu.1.le, hu.2⟩
        exact closure_mono hmono (by
          rw [closure_Ioo (a := (0:ℝ)) (b := sInf T) (ne_of_lt h)]
          exact ⟨ht0, le_rfl⟩)
      have hsub : α '' Set.Ico (0:ℝ) (sInf T) ⊆ L :=
        fun z ⟨u, hu, hzu⟩ => hzu ▸ hpre u hu
      have h1 := image_closure_subset_closure_image hαc ⟨sInf T, hcl, rfl⟩
      exact hLc.closure_eq ▸ closure_mono hsub h1
  have htnotint : α (sInf T) ∉ interior L := by
    intro hint
    rcases lt_or_eq_of_le ht1 with hlt1 | heq1
    · obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp
        (hαc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
      have hmin : (0:ℝ) < min δ (1 - sInf T) := lt_min hδ0 (by linarith)
      obtain ⟨u, huT, hult⟩ := exists_lt_of_csInf_lt hTne (by linarith : sInf T < sInf T + min δ (1 - sInf T))
      have hsu : sInf T ≤ u := csInf_le hbdd huT
      have hb : |u - sInf T| < δ := by
        rw [abs_of_nonneg (by linarith)]
        linarith [min_le_left δ (1 - sInf T)]
      rcases eq_or_lt_of_le hsu with h | h
      · rw [← h] at huT
        exact huT.2 (interior_subset hint)
      · exact huT.2 (interior_subset (hδ (by
          rw [Metric.mem_ball, Real.dist_eq]; exact hb)))
    · rw [heq1, hα1] at hint
      exact hyL (interior_subset hint)
  refine ⟨α, sInf T, hαc, hαinj, hα0, hαC, hα1 ▸ hyL, ⟨ht0, ht1⟩, ?_, ?_⟩
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with h | h
    · exact hpre u ⟨hu.1, h⟩
    · rw [h]; exact htL
  · rw [hLc.frontier_eq]
    exact ⟨htL, htnotint⟩

/-- **The same, avoiding a prescribed finite set.**  The inside piece of a level arc must avoid the
base points of the other strands (`avoids_base`) and the previously chosen tips, which — inside the
compact set `K ⊇ L` — form a finite set `F`; removing `F` from the carrier `C` keeps it path
connected (dimension `≥ 2`), and `C \ F` is still not contained in the compact set `K` (otherwise
`closure C ⊆ K ∪ F` would be compact). -/
theorem exists_arc_first_exit_of_collar_avoiding {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C L K F : Set M} (hC : IsOpen C) (hCc : IsPreconnected C) (hLc : IsClosed L)
    (hKc : IsCompact K) (hLK : L ⊆ K) {s : M} (hsC : s ∈ C) (hsL : s ∈ L)
    (hnt : ¬ IsCompact (closure C)) (hF : F.Finite) (hFC : F ⊆ C) (hsF : s ∉ F) :
    ∃ (α : ℝ → M) (t : ℝ), Continuous α ∧ Set.InjOn α (Set.Icc (0:ℝ) 1) ∧ α 0 = s ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, α u ∈ C) ∧ α 1 ∉ L ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      (∀ u ∈ Set.Icc (0:ℝ) t, α u ∈ L) ∧ α t ∈ frontier L ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, α u ∉ F) := by
  classical
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  have hpath : IsPathConnected C :=
    hC.isConnected_iff_isPathConnected.mp ⟨⟨s, hsC⟩, hCc⟩
  have hpath' : IsPathConnected (C \ F) :=
    Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen hn hC hpath hF hFC
  have hsC' : s ∈ C \ F := ⟨hsC, hsF⟩
  -- `C \ F` is not contained in the compact set `K`
  have hnotsub : ¬ C \ F ⊆ K := by
    intro hsub
    have hcl : closure C ⊆ K ∪ (C ∩ F) := by
      have h1 : C ⊆ (C \ F) ∪ (C ∩ F) := by
        intro x hx
        by_cases hxF : x ∈ F
        · exact Or.inr ⟨hx, hxF⟩
        · exact Or.inl ⟨hx, hxF⟩
      have h2 : closure ((C \ F) ∪ (C ∩ F)) ⊆ K ∪ (C ∩ F) := by
        rw [closure_union]
        exact Set.union_subset
          ((closure_minimal hsub hKc.isClosed).trans Set.subset_union_left)
          ((le_of_eq (hF.subset inter_subset_right).isClosed.closure_eq).trans
            Set.subset_union_right)
      exact (closure_mono h1).trans h2
    exact hnt (IsCompact.union hKc (hF.subset inter_subset_right).isCompact
      |>.of_isClosed_subset isClosed_closure hcl)
  obtain ⟨y, hyC', hyK⟩ := Set.not_subset.mp hnotsub
  have hyL : y ∉ L := fun h => hyK (hLK h)
  have hsy : s ≠ y := fun h => hyL (h ▸ hsL)
  obtain ⟨α, hαc, hαinj, hα0, hα1, hαC'⟩ :=
    Work.Whitney.PathTools.exists_arc_of_isPathConnected (n := n)
      (hC.sdiff hF.isClosed) hpath' hsC' hyC' hsy
  -- the first exit from `L`
  set T : Set ℝ := {u : ℝ | u ∈ Set.Icc (0:ℝ) 1 ∧ α u ∉ L} with hTdef
  have h1T : (1:ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by rw [hα1]; exact hyL⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hlow : ∀ b ∈ T, (0:ℝ) ≤ b := fun b hb => hb.1.1
  have hbdd : BddBelow T := ⟨0, hlow⟩
  have hmem_of : ∀ u, u ∈ Set.Icc (0:ℝ) 1 → α u ∉ L → u ∈ T := fun u h1 h2 => ⟨h1, h2⟩
  have ht0 : (0:ℝ) ≤ sInf T := le_csInf hTne hlow
  have ht1 : sInf T ≤ 1 := csInf_le hbdd h1T
  have hpre : ∀ u ∈ Set.Ico (0:ℝ) (sInf T), α u ∈ L := by
    intro u hu
    by_contra hcon
    exact absurd (csInf_le hbdd (hmem_of u ⟨hu.1, le_trans hu.2.le ht1⟩ hcon)) (not_le.mpr hu.2)
  have htL : α (sInf T) ∈ L := by
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h, hα0]; exact hsL
    · have hcl : sInf T ∈ closure (Set.Ico (0:ℝ) (sInf T)) := by
        have hmono : Set.Ioo (0:ℝ) (sInf T) ⊆ Set.Ico (0:ℝ) (sInf T) :=
          fun u hu => ⟨hu.1.le, hu.2⟩
        exact closure_mono hmono (by
          rw [closure_Ioo (a := (0:ℝ)) (b := sInf T) (ne_of_lt h)]
          exact ⟨ht0, le_rfl⟩)
      have hsub : α '' Set.Ico (0:ℝ) (sInf T) ⊆ L :=
        fun z ⟨u, hu, hzu⟩ => hzu ▸ hpre u hu
      have h1 := image_closure_subset_closure_image hαc ⟨sInf T, hcl, rfl⟩
      exact hLc.closure_eq ▸ closure_mono hsub h1
  have htnotint : α (sInf T) ∉ interior L := by
    intro hint
    rcases lt_or_eq_of_le ht1 with hlt1 | heq1
    · obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp
        (hαc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
      have hmin : (0:ℝ) < min δ (1 - sInf T) := lt_min hδ0 (by linarith)
      obtain ⟨u, huT, hult⟩ := exists_lt_of_csInf_lt hTne
        (by linarith : sInf T < sInf T + min δ (1 - sInf T))
      have hsu : sInf T ≤ u := csInf_le hbdd huT
      have hb : |u - sInf T| < δ := by
        rw [abs_of_nonneg (by linarith)]
        linarith [min_le_left δ (1 - sInf T)]
      rcases eq_or_lt_of_le hsu with h | h
      · rw [← h] at huT
        exact huT.2 (interior_subset hint)
      · exact huT.2 (interior_subset (hδ (by
          rw [Metric.mem_ball, Real.dist_eq]; exact hb)))
    · rw [heq1, hα1] at hint
      exact hyL (interior_subset hint)
  refine ⟨α, sInf T, hαc, hαinj, hα0, fun u hu => (hαC' u hu).1, hα1 ▸ hyL, ⟨ht0, ht1⟩, ?_, ?_,
    fun u hu => (hαC' u hu).2⟩
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with h | h
    · exact hpre u ⟨hu.1, h⟩
    · rw [h]; exact htL
  · rw [hLc.frontier_eq]
    exact ⟨htL, htnotint⟩

end Work.Noncompact.CompressionTube
