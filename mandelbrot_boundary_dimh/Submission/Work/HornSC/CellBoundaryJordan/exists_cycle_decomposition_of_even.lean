import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph
import Submission.Work.HornSC.CellBoundaryJordan.exists_cycle_of_even
import Submission.Work.HornSC.CellBoundaryJordan.darts_leaving_even

/-!
# Cycle decomposition of a graph with all degrees even

We prove that the dart set of a finite graph `G : DartGraph α` all of whose degrees are even is
covered by finitely many cycles whose dart sets are pairwise disjoint (an edge-disjoint cycle
decomposition).

The induction is on the number of darts: a nonempty even graph contains a cycle `C`
(`exists_cycle_of_even`); deleting the darts of `C` leaves a smaller graph whose degrees are
still even (`darts_leaving_even`), and the induction hypothesis applies to it.

The auxiliary material about deleting a cycle lives in the `DartGraph` namespace.
-/

namespace Work.HornSC.CellBoundaryJordan

namespace DartGraph

variable {α : Type*} [DecidableEq α]

/-- Lift a cycle of a sub-dart-graph `G` to a cycle of a larger dart-graph `G'` whose darts
contain those of `G`.  The darts of the cycle do not change. -/
def Cycle.mono {G G' : DartGraph α} (h : G.D ⊆ G'.D) (C : G.Cycle) : G'.Cycle where
  L := C.L
  hL := C.hL
  w := C.w
  per := C.per
  inj := C.inj
  adj := fun j hj => h (C.adj j hj)

@[simp] lemma Cycle.darts_mono {G G' : DartGraph α} (h : G.D ⊆ G'.D) (C : G.Cycle) :
    (C.mono h).darts = C.darts := rfl

/-- Delete from `G` all darts carried by the cycle `C`; the result is again a `DartGraph`. -/
noncomputable def erase (G : DartGraph α) (C : G.Cycle) : DartGraph α where
  D := G.D \ C.darts
  symm := by
    intro e he
    rw [Finset.mem_sdiff] at he ⊢
    refine ⟨G.symm e he.1, fun hc => he.2 ?_⟩
    simpa using C.swap_mem_darts hc
  noLoop := by
    intro e he
    rw [Finset.mem_sdiff] at he
    exact G.noLoop e he.1

@[simp] lemma erase_D (G : DartGraph α) (C : G.Cycle) : (erase G C).D = G.D \ C.darts := rfl

lemma sdiff_filter (s t : Finset (α × α)) (P : (α × α) → Prop) [DecidablePred P] :
    (s \ t).filter P = (s.filter P) \ (t.filter P) := by
  ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto

/-- Removing the darts of a cycle from `G` lowers the degree at `a` by the number of cycle darts
leaving `a`. -/
lemma erase_deg_eq (G : DartGraph α) (C : G.Cycle) (a : α) :
    (erase G C).deg a = G.deg a - (C.darts.filter (fun e => e.1 = a)).card := by
  unfold DartGraph.deg
  rw [erase_D, sdiff_filter]
  have hsub : C.darts.filter (fun e => e.1 = a) ⊆ G.D.filter (fun e => e.1 = a) :=
    Finset.filter_subset_filter _ C.darts_subset
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

/-- Deleting a cycle from a graph with even degrees leaves even degrees. -/
lemma erase_deg_even (G : DartGraph α) (C : G.Cycle) {a : α} (h : Even (G.deg a))
    (hC : Even ((C.darts.filter (fun e => e.1 = a)).card)) : Even ((erase G C).deg a) := by
  rw [erase_deg_eq]
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := hC
  have hsub : C.darts.filter (fun e => e.1 = a) ⊆ G.D.filter (fun e => e.1 = a) :=
    Finset.filter_subset_filter _ C.darts_subset
  have hle : (C.darts.filter (fun e => e.1 = a)).card ≤ G.deg a := by
    simpa [DartGraph.deg] using Finset.card_le_card hsub
  exact ⟨k - j, by omega⟩

end DartGraph

open DartGraph

/-- A finite graph all of whose degrees are even is the union of edge-disjoint cycles: its dart
set is covered by finitely many cycles whose dart sets are pairwise disjoint.

Proved by strong induction on the number of darts: if `D ≠ ∅`, an even graph contains a cycle
`C`; delete the darts of `C` (degrees stay even) and apply the induction hypothesis to the
smaller graph. -/
theorem exists_cycle_decomposition_of_even {α : Type*} [DecidableEq α] (G : DartGraph α)
    (h : ∀ a, Even (G.deg a)) :
    ∃ l : List G.Cycle,
      (∀ C ∈ l, C.darts ⊆ G.D) ∧
      l.Pairwise (fun C C' => Disjoint C.darts C'.darts) ∧
      (∀ e ∈ G.D, ∃ C ∈ l, e ∈ C.darts) := by
  classical
  have key : ∀ n, ∀ (G : DartGraph α), G.D.card ≤ n → (∀ a, Even (G.deg a)) →
      ∃ l : List G.Cycle,
        (∀ C ∈ l, C.darts ⊆ G.D) ∧
        l.Pairwise (fun C C' => Disjoint C.darts C'.darts) ∧
        (∀ e ∈ G.D, ∃ C ∈ l, e ∈ C.darts) := by
    intro n
    induction n with
    | zero =>
      intro G hc hh
      have hD : G.D = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
      exact ⟨[], by simp, by simp,
        by intro e he; rw [hD] at he; exact absurd he (Finset.notMem_empty e)⟩
    | succ n ih =>
      intro G hc hh
      by_cases hne : G.D.Nonempty
      · obtain ⟨C, hCsub⟩ := exists_cycle_of_even G hh hne
        have hsub' : (DartGraph.erase G C).D ⊆ G.D := Finset.sdiff_subset
        have hCne : C.darts.Nonempty :=
          ⟨(C.w 0, C.w 1), C.mem_darts_forward (by have := C.hL; omega)⟩
        have hcardlt : (DartGraph.erase G C).D.card < G.D.card := by
          rw [DartGraph.erase_D, ← Finset.card_sdiff_add_card_eq_card hCsub]
          have : 0 < C.darts.card := Finset.card_pos.mpr hCne
          omega
        have hcard' : (DartGraph.erase G C).D.card ≤ n := by omega
        have heven' : ∀ a, Even ((DartGraph.erase G C).deg a) := fun a =>
          DartGraph.erase_deg_even G C (hh a) (darts_leaving_even C a)
        obtain ⟨l', hl'sub, hl'pw, hl'cov⟩ := ih (DartGraph.erase G C) hcard' heven'
        refine ⟨C :: l'.map (DartGraph.Cycle.mono hsub'), ?_, ?_, ?_⟩
        · intro C' hC'
          rw [List.mem_cons] at hC'
          rcases hC' with rfl | hC'
          · exact hCsub
          · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC'
            rw [DartGraph.Cycle.darts_mono]
            exact fun e he => hsub' (hl'sub D hD he)
        · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
          · intro C' hC'
            obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC'
            rw [DartGraph.Cycle.darts_mono]
            exact Finset.disjoint_left.mpr
              (fun e he heD => (Finset.mem_sdiff.mp (hl'sub D hD heD)).2 he)
          · rw [List.pairwise_map]
            exact hl'pw.imp fun hDisj => hDisj
        · intro e he
          by_cases heC : e ∈ C.darts
          · exact ⟨C, List.mem_cons_self, heC⟩
          · have he' : e ∈ (DartGraph.erase G C).D := Finset.mem_sdiff.mpr ⟨he, heC⟩
            obtain ⟨D, hD, heD⟩ := hl'cov e he'
            exact ⟨DartGraph.Cycle.mono hsub' D,
              List.mem_cons_of_mem _ (List.mem_map.mpr ⟨D, hD, rfl⟩),
              by rw [DartGraph.Cycle.darts_mono]; exact heD⟩
      · have hD : G.D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        exact ⟨[], by simp, by simp,
          by intro e he; rw [hD] at he; exact absurd he (Finset.notMem_empty e)⟩
  exact key G.D.card G le_rfl h

end Work.HornSC.CellBoundaryJordan
