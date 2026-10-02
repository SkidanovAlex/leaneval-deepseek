import Mathlib
import Submission.Work.RatHurewicz.gTrick
import Submission.Work.RatHurewicz.Triad.kTrick
import Submission.Work.ThomBordism.TwoSet.exists_cellHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `K`/`G` tricks, with the image of the homotopy in the image of the map

The statements of `Triad.kTrick` and `Work.RatHurewicz.gTrick` do not record that the deformed map
(as well as the whole homotopy) factors through the original one: their constructions are
`f ∘ h` for an explicit self-map `h` of the cube.  The triad induction needs that, in order to know
that the values of the treatment of a cell lie in the set into which the current map maps the cell.

This file proves the strengthened forms `kTrickVals`, `gTrickVals` (cube level) and
`gTrickCellVals` (cell level).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

/-- **The `K`-trick**, with the additional clause that all values of the homotopy are values of
`f`. -/
theorem kTrickVals {Y : Type} [TopologicalSpace Y] {d : ℕ} (p : ℕ) (hp : p ≤ d)
    (f : C(ICube d, Y)) (A : Set Y)
    (h : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → f u ∈ A →
        ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2) :
    ∃ G : C(ICube d × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ u (hu : u ∈ Cube.boundary (Fin d)) t, G (u, t) = f u) ∧
      (∀ u t, ∃ u' : ICube d, G (u, t) = f u') ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨f.comp ⟨Prod.fst, continuous_fst⟩, fun u => rfl, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨i, -⟩ := hu
      exact i.elim0
    · intro u t
      exact ⟨u, rfl⟩
    · intro u hA
      exact ⟨∅, by simpa using hp, by simp⟩
  · refine ⟨f.comp (hCM hd), ?_, ?_, ?_, ?_⟩
    · intro u
      show (f.comp (hCM hd)) (u, 0) = f u
      rw [ContinuousMap.comp_apply, hCM_apply, hR_zero]
    · intro u hu t
      show (f.comp (hCM hd)) (u, t) = f u
      rw [ContinuousMap.comp_apply, hCM_apply, hR_wall hd hu t]
    · intro u t
      exact ⟨hR hd (u, t), rfl⟩
    · intro u hA
      by_cases hall : ∃ L : Finset (Fin d), p ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2
      · exact hall
      · exfalso
        push_neg at hall
        have hex : ∃ i : Fin d, (1:ℝ)/2 ≤ (u i : ℝ) := by
          obtain ⟨i, -, hi⟩ := hall (Finset.univ) (by simpa using hp)
          exact ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hex
        have hbd : hR hd (u, 1) ∈ Cube.boundary (Fin d) := hR_one_mem_boundary hd hi
        have hmem : f (hR hd (u, 1)) ∈ A := by
          have h1 : (f.comp (hCM hd)) (u, 1) = f (hR hd (u, 1)) := by
            simp only [ContinuousMap.comp_apply, hCM_apply]
          rwa [h1] at hA
        obtain ⟨L, hL, hLmem⟩ := h (hR hd (u, 1)) hbd hmem
        obtain ⟨j, hjL, hjhalf⟩ := hall L hL
        exact absurd (le_of_hR_one_lt hd u j (hLmem j hjL)) (not_lt.mpr hjhalf)

/-- **The `G`-trick**, with the additional clause that all values of the homotopy are values of
`f`. -/
theorem gTrickVals {Y : Type} [TopologicalSpace Y] {d : ℕ} (P : ℕ) (hP : P ≤ d)
    (f : C(ICube d, Y)) (A : Set Y)
    (h : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → f u ∈ A →
        ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, 1 / 2 < (u i : ℝ)) :
    ∃ G : C(ICube d × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : ICube d) (hu : u ∈ Cube.boundary (Fin d)) (t : I), G (u, t) = f u) ∧
      (∀ u t, ∃ u' : ICube d, G (u, t) = f u') ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, 1 / 2 < (u i : ℝ)) := by
  classical
  set ρ : C(ICube d, ICube d) := ⟨cubeReflect, continuous_cubeReflect⟩ with hρ
  have hρval : ∀ u, ρ u = cubeReflect u := fun u => rfl
  have h' : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) → (f.comp ρ) u ∈ A →
      ∃ L : Finset (Fin d), P ≤ L.card ∧ ∀ i ∈ L, (u i : ℝ) < 1 / 2 := by
    intro u hu hA
    have hA' : f (cubeReflect u) ∈ A := by
      simpa [hρval, ContinuousMap.comp_apply] using hA
    obtain ⟨L, hL, hLi⟩ := h (cubeReflect u) (cubeReflect_mem_boundary hu) hA'
    refine ⟨L, hL, fun i hi => ?_⟩
    have := hLi i hi
    rw [cubeReflect_apply] at this
    linarith
  obtain ⟨G', hG'0, hG'bd, hG'vals, hG'1⟩ := kTrickVals P hP (f.comp ρ) A h'
  refine ⟨⟨fun p => G' (cubeReflect p.1, p.2), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact G'.continuous.comp
      (Continuous.prodMk (continuous_cubeReflect.comp continuous_fst) continuous_snd)
  · intro u
    show G' (cubeReflect u, (0 : I)) = f u
    rw [hG'0, ContinuousMap.comp_apply, hρval (cubeReflect u), cubeReflect_involutive u]
  · intro u hu t
    show G' (cubeReflect u, t) = f u
    rw [hG'bd (cubeReflect u) (cubeReflect_mem_boundary hu) t,
      ContinuousMap.comp_apply, hρval (cubeReflect u), cubeReflect_involutive u]
  · intro u t
    obtain ⟨u', hu'⟩ := hG'vals (cubeReflect u) t
    refine ⟨cubeReflect u', ?_⟩
    show G' (cubeReflect u, t) = f (cubeReflect u')
    rw [hu']
    rfl
  · intro u hA
    have hA' : G' (cubeReflect u, (1 : I)) ∈ A := by
      simpa using hA
    obtain ⟨L, hL, hLi⟩ := hG'1 (cubeReflect u) hA'
    refine ⟨L, hL, fun i hi => ?_⟩
    have := hLi i hi
    rw [cubeReflect_apply] at this
    linarith

open Work.ThomBordism.TwoSet

/-- **The `K`-trick on a cell**, with the additional clause that all values of the homotopy are
values of `f`. -/
theorem kTrickCellVals {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    {Y : Type} [TopologicalSpace Y] (P : ℕ) (hP : P ≤ cellDim c)
    (f : C(cellSet c, Y)) (A : Set Y)
    (h : ∀ u : cellSet c, (u : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c → f u ∈ A →
      ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, ((invMap c hN u m : unitInterval) : ℝ) < 1 / 2) :
    ∃ G : C(cellSet c × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c) (t : I), G (u, t) = f u) ∧
      (∀ u t, ∃ u' : cellSet c, G (u, t) = f u') ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
          ∀ m ∈ L, ((invMap c hN u m : unitInterval) : ℝ) < 1 / 2) := by
  classical
  set e : C(Work.ThomBordism.TwoSet.IC (cellDim c), cellSet c) := ⟨cellHomeo c hN, (cellHomeo c hN).continuous⟩
  have hleft : ∀ u : Work.ThomBordism.TwoSet.IC (cellDim c), invMap c hN (e u) = u := fun u => cellEquiv c hN |>.left_inv u
  have hright : ∀ u : cellSet c, e (invMap c hN u) = u := fun u =>
    (cellHomeo c hN).apply_symm_apply u
  have hcube : ∀ u : Work.ThomBordism.TwoSet.IC (cellDim c), u ∈ Cube.boundary (Fin (cellDim c)) →
      (f.comp e) u ∈ A → ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, (u m : ℝ) < 1 / 2 := by
    intro u hu hA
    have hmem : ((e u : cellSet c) : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c :=
      (invMap_mem_boundary_iff c hN (e u)).mp (by rw [hleft u]; exact hu)
    obtain ⟨L, hL, hLmem⟩ := h (e u) hmem hA
    exact ⟨L, hL, fun m hm => by
      have := hLmem m hm
      rwa [hleft u] at this⟩
  obtain ⟨G', hG'0, hG'bd, hG'vals, hG'1⟩ := kTrickVals P hP (f.comp e) A hcube
  refine ⟨⟨fun p => G' (invMap c hN p.1, p.2), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact G'.continuous.comp
      (Continuous.prodMk ((continuous_invMap c hN).comp continuous_fst) continuous_snd)
  · intro u
    show G' (invMap c hN u, (0 : I)) = f u
    rw [hG'0, ContinuousMap.comp_apply, hright u]
  · intro u hu t
    have hub : invMap c hN u ∈ Cube.boundary (Fin (cellDim c)) :=
      (invMap_mem_boundary_iff c hN u).mpr hu
    show G' (invMap c hN u, t) = f u
    rw [hG'bd (invMap c hN u) hub t, ContinuousMap.comp_apply, hright u]
  · intro u t
    obtain ⟨u', hu'⟩ := hG'vals (invMap c hN u) t
    refine ⟨e u', ?_⟩
    show G' (invMap c hN u, t) = f (e u')
    rw [hu', ContinuousMap.comp_apply]
  · intro u hA
    exact hG'1 (invMap c hN u) hA

/-- **The `G`-trick on a cell**, with the additional clause that all values of the homotopy are
values of `f`. -/
theorem gTrickCellVals {j N : ℕ} (hN : 1 ≤ N) (c : CellIdx j N)
    {Y : Type} [TopologicalSpace Y] (P : ℕ) (hP : P ≤ cellDim c)
    (f : C(cellSet c, Y)) (A : Set Y)
    (h : ∀ u : cellSet c, (u : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c → f u ∈ A →
      ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, 1 / 2 < ((invMap c hN u m : unitInterval) : ℝ)) :
    ∃ G : C(cellSet c × I, Y),
      (∀ u, G (u, 0) = f u) ∧
      (∀ (u : cellSet c) (hu : (u : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c) (t : I), G (u, t) = f u) ∧
      (∀ u t, ∃ u' : cellSet c, G (u, t) = f u') ∧
      (∀ u, G (u, 1) ∈ A →
        ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
          ∀ m ∈ L, 1 / 2 < ((invMap c hN u m : unitInterval) : ℝ)) := by
  classical
  set e : C(Work.ThomBordism.TwoSet.IC (cellDim c), cellSet c) := ⟨cellHomeo c hN, (cellHomeo c hN).continuous⟩
  have hleft : ∀ u : Work.ThomBordism.TwoSet.IC (cellDim c), invMap c hN (e u) = u := fun u => cellEquiv c hN |>.left_inv u
  have hright : ∀ u : cellSet c, e (invMap c hN u) = u := fun u =>
    (cellHomeo c hN).apply_symm_apply u
  have hcube : ∀ u : Work.ThomBordism.TwoSet.IC (cellDim c), u ∈ Cube.boundary (Fin (cellDim c)) →
      (f.comp e) u ∈ A → ∃ L : Finset (Fin (cellDim c)), P ≤ L.card ∧
        ∀ m ∈ L, 1 / 2 < (u m : ℝ) := by
    intro u hu hA
    have hmem : ((e u : cellSet c) : Work.ThomBordism.TwoSet.IC j) ∈ cellRelbd c :=
      (invMap_mem_boundary_iff c hN (e u)).mp (by rw [hleft u]; exact hu)
    obtain ⟨L, hL, hLmem⟩ := h (e u) hmem hA
    exact ⟨L, hL, fun m hm => by
      have := hLmem m hm
      rwa [hleft u] at this⟩
  obtain ⟨G', hG'0, hG'bd, hG'vals, hG'1⟩ := gTrickVals P hP (f.comp e) A hcube
  refine ⟨⟨fun p => G' (invMap c hN p.1, p.2), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact G'.continuous.comp
      (Continuous.prodMk ((continuous_invMap c hN).comp continuous_fst) continuous_snd)
  · intro u
    show G' (invMap c hN u, (0 : I)) = f u
    rw [hG'0, ContinuousMap.comp_apply, hright u]
  · intro u hu t
    have hub : invMap c hN u ∈ Cube.boundary (Fin (cellDim c)) :=
      (invMap_mem_boundary_iff c hN u).mpr hu
    show G' (invMap c hN u, t) = f u
    rw [hG'bd (invMap c hN u) hub t, ContinuousMap.comp_apply, hright u]
  · intro u t
    obtain ⟨u', hu'⟩ := hG'vals (invMap c hN u) t
    refine ⟨e u', ?_⟩
    show G' (invMap c hN u, t) = f (e u')
    rw [hu', ContinuousMap.comp_apply]
  · intro u hA
    exact hG'1 (invMap c hN u) hA

end

end Work.RatHurewicz.Triad
