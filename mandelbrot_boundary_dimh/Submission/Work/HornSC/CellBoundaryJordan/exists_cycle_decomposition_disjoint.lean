import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.wall_local_even
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph
import Submission.Work.HornSC.CellBoundaryJordan.WallGraph
import Submission.Work.HornSC.CellBoundaryJordan.WallSeg
import Submission.Work.HornSC.CellBoundaryJordan.exists_cycle_decomposition_of_even
import Submission.Work.HornSC.CellBoundaryJordan.wallDarts_deg_even

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The darts of a cycle are exactly the forward and backward steps between consecutive
vertices. -/
lemma mem_darts_iff {α : Type*} [DecidableEq α] {G : DartGraph α} (C : G.Cycle) {e : α × α} :
    e ∈ C.darts ↔ ∃ j, j < C.L ∧ (e = (C.w j, C.w (j + 1)) ∨ e = (C.w (j + 1), C.w j)) := by
  rw [DartGraph.Cycle.darts, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      exact ⟨j, Finset.mem_range.mp hj, Or.inl hje.symm⟩
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      exact ⟨j, Finset.mem_range.mp hj, Or.inr hje.symm⟩
  · rintro ⟨j, hj, h | h⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, h.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, h.symm⟩)

/-- The wall set of a finite family of lattice cells decomposes into finitely many closed grid
cycles whose closed unit segments are pairwise distinct. -/
theorem exists_cycle_decomposition_disjoint (A : Finset (ℤ × ℤ)) :
    ∃ (m : ℕ) (k : Fin m → ℕ) (u : Fin m → ℕ → ℤ × ℤ),
      (∀ i, 3 ≤ k i) ∧
      (∀ i, u i (k i) = u i 0) ∧
      (∀ i, ∀ j, j < k i → IsUnitAdj (u i j) (u i (j + 1))) ∧
      (∀ i, ∀ j j', j < k i → j' < k i → u i j = u i j' → j = j') ∧
      (∀ i i', i ≠ i' → ∀ j j', j < k i → j' < k i' →
        adjSeg (u i j) (u i (j + 1)) ≠ adjSeg (u i' j') (u i' (j' + 1))) ∧
      (⋃ i, ⋃ j ∈ {j : ℕ | j < k i}, adjSeg (u i j) (u i (j + 1))) = wallSet A := by
  obtain ⟨l, hsub, hpair, hcov⟩ :=
    exists_cycle_decomposition_of_even (wallDartGraph A) (wallDarts_deg_even A)
  refine ⟨l.length, fun i => (l.get i).L, fun i => (l.get i).w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (l.get i).hL
  · intro i; exact (l.get i).w_period
  · intro i j hj
    exact wallDarts_isUnitAdj
      (hsub (l.get i) (List.get_mem l i) ((l.get i).mem_darts_forward hj))
  · intro i j j' hj hj' h
    exact (l.get i).inj j j' hj hj' h
  · intro i i' hne j j' hj hj' heq
    have hdisj : Disjoint (l.get i).darts (l.get i').darts := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (List.pairwise_iff_get.mp hpair) i i' h
      · exact ((List.pairwise_iff_get.mp hpair) i' i h).symm
    have hinter : (l.get i).darts ∩ (l.get i').darts = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have hab : IsUnitAdj ((l.get i).w j) ((l.get i).w (j + 1)) :=
      wallDarts_isUnitAdj (hsub (l.get i) (List.get_mem l i) ((l.get i).mem_darts_forward hj))
    have hcd : IsUnitAdj ((l.get i').w j') ((l.get i').w (j' + 1)) :=
      wallDarts_isUnitAdj (hsub (l.get i') (List.get_mem l i') ((l.get i').mem_darts_forward hj'))
    have hpair2 := (adjSeg_eq_iff hab hcd).mp heq
    have hCfwd : ((l.get i).w j, (l.get i).w (j + 1)) ∈ (l.get i).darts :=
      (l.get i).mem_darts_forward hj
    have hnot : ((l.get i).w j, (l.get i).w (j + 1)) ∉ (l.get i').darts := by
      intro hmem
      have : ((l.get i).w j, (l.get i).w (j + 1)) ∈ (l.get i).darts ∩ (l.get i').darts :=
        Finset.mem_inter.mpr ⟨hCfwd, hmem⟩
      rw [hinter] at this
      simpa using this
    apply hnot
    rcases hpair2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hthis : ((l.get i').w j', (l.get i').w (j' + 1)) ∈ (l.get i').darts :=
        (l.get i').mem_darts_forward hj'
      rw [← h1, ← h2] at hthis
      exact hthis
    · have hthis := (l.get i').swap_mem_darts ((l.get i').mem_darts_forward hj')
      rw [← h1, ← h2] at hthis
      exact hthis
  · ext z
    constructor
    · intro hz
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz
      obtain ⟨i, j, hj, hzj⟩ := hz
      exact wallDarts_adjSeg_subset
        (hsub (l.get i) (List.get_mem l i) ((l.get i).mem_darts_forward hj)) hzj
    · intro hz
      obtain ⟨e, heS, hze⟩ := wallSet_subset_wallStepFinset A hz
      have heD : e ∈ (wallDartGraph A).D := mem_wallDarts.mpr (Or.inl heS)
      obtain ⟨C, hCl, heC⟩ := hcov e heD
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hCl
      rw [← hi] at heC
      obtain ⟨j, hjL, hcase⟩ := (mem_darts_iff (l.get i)).mp heC
      have hze' : z ∈ adjSeg e.1 e.2 := by
        rw [adjSeg_stepSeg_of_mem_wallStepFinset heS]; exact hze
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨i, j, hjL, ?_⟩
      rcases hcase with hcase | hcase
      · simp only [hcase, Prod.fst, Prod.snd] at hze'
        exact hze'
      · simp only [hcase, Prod.fst, Prod.snd] at hze'
        rw [← adjSeg_comm ((l.get i).w j) ((l.get i).w (j + 1))] at hze'
        exact hze'

end Work.HornSC.CellBoundaryJordan
