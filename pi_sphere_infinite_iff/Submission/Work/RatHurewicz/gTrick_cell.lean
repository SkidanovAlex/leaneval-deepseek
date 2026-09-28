import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.RatHurewicz.gTrick

/-!
# The `G`-trick on a cell

`Work.RatHurewicz.gTrick` proves the `G`-trick (push towards `1`) on the standard cube; this file
transports it to a cell `c` of the grid along `cellHomeo c hN`, exactly as `kTrick_cell` does for the
`K`-trick. The "coordinates" of a point `u` of the cell are `invMap c hN u m ∈ [0,1]` and the
relative boundary `cellRelbd c` plays the role of `∂I^d`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.ThomBordism.TwoSet

/-- **The `G`-trick on a cell.** -/
theorem gTrick_cell {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    {Y : Type} [TopologicalSpace Y] (P : ℕ) (hP : P ≤ cellDim c)
    (f : C(cellSet c, Y)) (A : Set Y)
    (h : ∀ u : cellSet c, (u : IC j) ∈ cellRelbd c → f u ∈ A →
      ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, 1 / 2 < ((invMap c hN u m : unitInterval) : ℝ)) :
    ∃ G : C(cellSet c × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : IC j) ∈ cellRelbd c) (t : I), G (u, t) = f u) ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
          ∀ m ∈ L, 1 / 2 < ((invMap c hN u m : unitInterval) : ℝ)) := by
  classical
  set e : C(IC (cellDim c), cellSet c) := ⟨cellHomeo c hN, (cellHomeo c hN).continuous⟩ with hedef
  have hleft : ∀ u : IC (cellDim c), invMap c hN (e u) = u := fun u =>
    cellEquiv c hN |>.left_inv u
  have hright : ∀ u : cellSet c, e (invMap c hN u) = u := fun u =>
    (cellHomeo c hN).apply_symm_apply u
  -- pull the hypothesis back to the cube
  have hcube : ∀ u : IC (cellDim c), u ∈ Cube.boundary (Fin (cellDim c)) →
      (f.comp e) u ∈ A → ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, 1 / 2 < (u m : ℝ) := by
    intro u hu hA
    have hmem : ((e u : cellSet c) : IC j) ∈ cellRelbd c :=
      (invMap_mem_boundary_iff c hN (e u)).mp (by rw [hleft u]; exact hu)
    obtain ⟨L, hL, hLmem⟩ := h (e u) hmem hA
    exact ⟨L, hL, fun m hm => by
      have := hLmem m hm
      rwa [hleft u] at this⟩
  obtain ⟨G', hG'0, hG'bd, hG'1⟩ :=
    Work.RatHurewicz.gTrick P hP (f.comp e) A hcube
  refine ⟨⟨fun p => G' (invMap c hN p.1, p.2), ?_⟩, ?_, ?_, ?_⟩
  · exact G'.continuous.comp
      (Continuous.prodMk ((continuous_invMap c hN).comp continuous_fst) continuous_snd)
  · -- clause 1
    intro u
    show G' (invMap c hN u, (0 : I)) = f u
    rw [hG'0, ContinuousMap.comp_apply, hright u]
  · -- clause 2: relative to the relative boundary
    intro u hu t
    have hub : invMap c hN u ∈ Cube.boundary (Fin (cellDim c)) :=
      (invMap_mem_boundary_iff c hN u).mpr hu
    show G' (invMap c hN u, t) = f u
    rw [hG'bd (invMap c hN u) hub t, ContinuousMap.comp_apply, hright u]
  · -- clause 3
    intro u hA
    exact hG'1 (invMap c hN u) hA

end

end Work.RatHurewicz
