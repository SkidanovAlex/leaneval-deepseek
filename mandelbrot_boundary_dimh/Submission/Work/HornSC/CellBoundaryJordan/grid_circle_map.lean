import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_basic
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_range
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_injective
import Submission.Work.PlanarSC.exists_circleMap_of_path
import Submission.Lib.Unif2.Commons.Topology.Winding.hasArg_homotopy_invariant

/-!
# The circle map of the polygonal tour

The polygonal tour of a simple closed grid cycle descends to an injective map of the circle whose
image is the cycle, and whose lift is the tour itself.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

open scoped unitInterval Topology

/-- The polygonal tour as a closed path, from `lpt (u 0)` back to itself. -/
noncomputable def cyclePath (k : ℕ) (u : ℕ → ℤ × ℤ) (hper : ∀ i, u (i + k) = u i) :
    Path (lpt (u 0)) (lpt (u 0)) :=
  Path.mk ⟨fun s : unitInterval => tourOn u k (s : ℝ),
      (continuous_tourOn u k).comp continuous_subtype_val⟩
    (tourOn_zero u k) (by
      show tourOn u k ((1 : unitInterval) : ℝ) = lpt (u 0)
      rw [show ((1 : unitInterval) : ℝ) = 1 by norm_num, tourOn_one]
      simpa using congrArg lpt (hper 0))

lemma cyclePath_apply (k : ℕ) (u : ℕ → ℤ × ℤ) (hper : ∀ i, u (i + k) = u i)
    (s : unitInterval) : cyclePath k u hper s = tourOn u k (s : ℝ) := rfl

/-- The range of the cycle path is the polygonal curve. -/
lemma cyclePath_range {k : ℕ} (hk : 0 < k) (u : ℕ → ℤ × ℤ) (hper : ∀ i, u (i + k) = u i) :
    Set.range (cyclePath k u hper) = cycleSet k u := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨s, rfl⟩
    exact tourOn_mem_cycleSet hk u s.2.1 s.2.2
  · intro z hz
    obtain ⟨t, ht, htz⟩ := cycleSet_subset_tourOn_range hk u hz
    exact ⟨⟨t, ht⟩, by rw [cyclePath_apply]; exact htz⟩

/-- **The circle map of a simple closed grid cycle.** -/
theorem exists_circle_map_of_cycle {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1))) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      (∀ t : ℝ, γ (Circle.exp (2 * Real.pi * t)) = tour u k t) ∧
      Set.range γ = cycleSet k u := by
  have hk0 : 0 < k := by omega
  have hsimple : ∀ s t : unitInterval, cyclePath k u hper s = cyclePath k u hper t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t hst
    have hst' : tourOn u k (s : ℝ) = tourOn u k (t : ℝ) := hst
    rcases tourOn_injective hk u hper hinj hstep (s : ℝ) (t : ℝ) s.2.1 s.2.2
      t.2.1 t.2.2 hst' with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
    · exact Or.inr (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  obtain ⟨γ, hγinj, hγval, hγrange⟩ := Work.PlanarSC.exists_circleMap_of_path
    (cyclePath k u hper) hsimple
  have hrange : Set.range γ = cycleSet k u := by rw [hγrange, cyclePath_range hk0 u hper]
  refine ⟨γ, hγinj, ?_, hrange⟩
  have h1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → γ (Circle.exp (2 * Real.pi * t)) = tour u k t := by
    intro t ht0 ht1
    have hbase := hγval ⟨t, ht0, ht1⟩
    rw [cyclePath_apply] at hbase
    rcases eq_or_lt_of_le ht1 with h | h
    · subst h
      rw [hbase, tourOn_one]
      have hz : tour u k 1 = lpt (u 0) := by
        rw [show (1 : ℝ) = 0 + 1 by norm_num, tour_add_one u k 0, tour,
          Int.fract_eq_self.mpr ⟨le_rfl, by norm_num⟩, tourOn_zero]
      rw [hz]
      simpa using congrArg lpt (hper 0)
    · rw [hbase, ← tour_eq_tourOn u ht0 h]
  have h2 : Function.Periodic (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) 1 := by
    intro t
    show γ (Circle.exp (2 * Real.pi * (t + 1))) = γ (Circle.exp (2 * Real.pi * t))
    rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring,
      Circle.periodic_exp]
  have h3 : Function.Periodic (fun t : ℝ => tour u k t) 1 := tour_add_one u k
  intro t
  rw [Commons.Topology.Winding.periodic_eq_fract h2 t,
    Commons.Topology.Winding.periodic_eq_fract h3 t]
  exact h1 (Int.fract t) (Int.fract_nonneg t) (le_of_lt (Int.fract_lt_one t))

end Work.HornSC.CellBoundaryJordan
