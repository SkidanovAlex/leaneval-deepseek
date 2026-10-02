import Mathlib
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo
import Submission.Work.RatHurewicz.Triad.kTrick

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `K`-trick on a cell

`Triad/kTrick.lean` proves tom Dieck's (6.9.1) on the standard cube `I^d`. This file transports it
to a cell `c` of the grid, using the homeomorphism `cellHomeo c hN : I^{cellDim c} ≃ₜ cellSet c`:
the "coordinates" of a point `u` of the cell are the numbers `invMap c hN u m ∈ [0,1]`, and the
relative boundary `cellRelbd c` plays the role of `∂I^d`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

open Work.ThomBordism.TwoSet

/-- **The `K`-trick on a cell.** -/
theorem kTrick_cell {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    {Y : Type} [TopologicalSpace Y] (P : ℕ) (hP : P ≤ cellDim c)
    (f : C(cellSet c, Y)) (A : Set Y)
    (h : ∀ u : cellSet c, (u : IC j) ∈ cellRelbd c → f u ∈ A →
      ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, ((invMap c hN u m : unitInterval) : ℝ) < 1 / 2) :
    ∃ G : C(cellSet c × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : IC j) ∈ cellRelbd c) (t : I), G (u, t) = f u) ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
          ∀ m ∈ L, ((invMap c hN u m : unitInterval) : ℝ) < 1 / 2) := by
  classical
  -- the cube map `f ∘ e`
  set e : C(IC (cellDim c), cellSet c) := ⟨cellHomeo c hN, (cellHomeo c hN).continuous⟩ with hedef
  have hleft : ∀ u : IC (cellDim c), invMap c hN (e u) = u := fun u =>
    cellEquiv c hN |>.left_inv u
  have hright : ∀ u : cellSet c, e (invMap c hN u) = u := fun u =>
    (cellHomeo c hN).apply_symm_apply u
  -- pull the hypothesis back to the cube
  have hcube : ∀ u : IC (cellDim c), u ∈ Cube.boundary (Fin (cellDim c)) →
      (f.comp e) u ∈ A → ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, (u m : ℝ) < 1 / 2 := by
    intro u hu hA
    have hmem : ((e u : cellSet c) : IC j) ∈ cellRelbd c :=
      (invMap_mem_boundary_iff c hN (e u)).mp (by rw [hleft u]; exact hu)
    obtain ⟨L, hL, hLmem⟩ := h (e u) hmem hA
    exact ⟨L, hL, fun m hm => by
      have := hLmem m hm
      rwa [hleft u] at this⟩
  obtain ⟨G', hG'0, hG'bd, hG'1⟩ :=
    Work.RatHurewicz.Triad.kTrick P hP (f.comp e) A hcube
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
