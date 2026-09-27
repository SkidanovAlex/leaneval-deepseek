/-
# Auxiliary definitions for `Work.EKLC6Route.exists_window` (L2b, sub-windows)

This module sets up the machinery used in `Submission/Work/EKLC6Route/exists_window.lean`
(the statement `L2b — sub-windows` of `Submission/Work/EKLComp/C6GEOM_ROUTE_LEAD.md` §3.1).

Given a chart `c : Chart μ t` we build a decreasing sequence of subsets of `VtSet t ∩ V c.ρ`:

* `gridCell ρ ℓ d = {k | gridIdx ρ ℓ k = d}` is the level-`ℓ` grid cell of index `d`; its elements
  are entrywise `ρ/2^ℓ`-close to each other;
* `winSel c ℓ C` is a level-`ℓ` cell of `C` of positive mass inside the window `chartW c`, if such a
  cell exists (and `0` otherwise);
* `winCfam c 0 = VtSet t ∩ V c.ρ` and `winCfam c (m+1) = winCfam c m ∩ gridCell c.ρ (m+1) (winSel c (m+1) (winCfam c m))`.

The sequence `winCfam c` is decreasing, consists of Borel sets, and every one of its members meets
the window `chartW c` in a set of positive `μ`-measure (`winCfam_pos`).  The window of
`exists_window` is obtained by passing to a sub-sequence along which the masses of these
intersections decrease dyadically fast (see `subseq_tail_le`).
-/
import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.chartSet_measurable
import Submission.Work.EKLC6Route.exists_grid_cell_pos

noncomputable section
namespace Work.EKLC6Route
open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLComp
open Classical

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

/-! ## The window of a chart and the grid cells -/

/-- The chart set attached to a chart, i.e. the window `W` of the route lead. -/
def chartW (c : Chart μ t) : Set X3 := chartSet t c.z0 c.uc c.θ c.r c.ρ

theorem measurableSet_chartW (c : Chart μ t) : MeasurableSet (chartW c) :=
  chartSet_measurable c.huc c.hθ c.r c.ρ

/-- The level-`ℓ` grid cell of index `d`. -/
def gridCell (ρ : ℝ) (ℓ : ℕ) (d : Fin 3 → Fin 3 → ℤ) : Set SL3 := {k : SL3 | gridIdx ρ ℓ k = d}

theorem measurable_gridIdx (ρ : ℝ) (ℓ : ℕ) :
    Measurable (gridIdx ρ ℓ : SL3 → Fin 3 → Fin 3 → ℤ) := by
  rw [measurable_pi_iff]; intro i
  rw [measurable_pi_iff]; intro j
  have hc : Continuous (fun x : SL3 => ((x : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) * 2 ^ ℓ / ρ) := by fun_prop
  exact Measurable.floor hc.measurable

theorem measurableSet_gridCell (ρ : ℝ) (ℓ : ℕ) (d : Fin 3 → Fin 3 → ℤ) :
    MeasurableSet (gridCell ρ ℓ d) :=
  (measurable_gridIdx ρ ℓ) (measurableSet_singleton d)

theorem measurableSet_V (ρ : ℝ) : MeasurableSet (V ρ : Set SL3) :=
  (isOpen_UballOpen ρ).measurableSet

theorem measurableSet_VtSet_inter_V (ρ : ℝ) : MeasurableSet (VtSet t ∩ V ρ) :=
  (isClosed_VtSet t).measurableSet.inter (measurableSet_V ρ)

/-- `V` is monotone in its radius. -/
theorem V_subset_V {a b : ℝ} (h : a ≤ b) : V a ⊆ V b := fun g hg i j => lt_of_lt_of_le (hg i j) h

/-! ## The selection of positive-mass cells and the nested sequence -/

/-- A level-`ℓ` cell of `C` whose window-mass is positive, if one exists. -/
def winSel (c : Chart μ t) (ℓ : ℕ) (C : Set SL3) : Fin 3 → Fin 3 → ℤ :=
  if h : ∃ d, 0 < μ (chartW c ∩ c.θ ⁻¹' (C ∩ gridCell c.ρ ℓ d)) then Classical.choose h else 0

theorem winSel_spec (c : Chart μ t) {ℓ : ℕ} {C : Set SL3}
    (h : ∃ d, 0 < μ (chartW c ∩ c.θ ⁻¹' (C ∩ gridCell c.ρ ℓ d))) :
    0 < μ (chartW c ∩ c.θ ⁻¹' (C ∩ gridCell c.ρ ℓ (winSel c ℓ C))) := by
  rw [winSel, dif_pos h]
  exact Classical.choose_spec h

/-- The nested sequence of positive-mass cells: `winCfam c 0 = VtSet t ∩ V c.ρ`, and each step
intersects with a level-`(m+1)` cell of positive window-mass. -/
def winCfam (c : Chart μ t) : ℕ → Set SL3 :=
  fun j => Nat.rec (VtSet t ∩ V c.ρ)
    (fun m prev => prev ∩ gridCell c.ρ (m + 1) (winSel c (m + 1) prev)) j

@[simp] theorem winCfam_zero (c : Chart μ t) : winCfam c 0 = VtSet t ∩ V c.ρ := rfl

theorem winCfam_succ (c : Chart μ t) (m : ℕ) :
    winCfam c (m + 1) = winCfam c m ∩ gridCell c.ρ (m + 1) (winSel c (m + 1) (winCfam c m)) := rfl

theorem winCfam_succ_subset (c : Chart μ t) (m : ℕ) : winCfam c (m + 1) ⊆ winCfam c m := by
  rw [winCfam_succ]; exact Set.inter_subset_left

theorem winCfam_antitone (c : Chart μ t) : Antitone (winCfam c) :=
  antitone_nat_of_succ_le (winCfam_succ_subset c)

theorem winCfam_subset_V (c : Chart μ t) (j : ℕ) : winCfam c j ⊆ V c.ρ :=
  (winCfam_antitone c (Nat.zero_le j)).trans (by rw [winCfam_zero c]; exact Set.inter_subset_right)

theorem winCfam_subset_gridCell (c : Chart μ t) {j : ℕ} (hj : 1 ≤ j) :
    winCfam c j ⊆ gridCell c.ρ j (winSel c j (winCfam c (j - 1))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [winCfam_succ]
  exact Set.inter_subset_right

theorem measurableSet_winCfam (c : Chart μ t) : ∀ j, MeasurableSet (winCfam c j) := by
  intro j
  induction j with
  | zero => rw [winCfam_zero]; exact measurableSet_VtSet_inter_V (t := t) c.ρ
  | succ m ih => rw [winCfam_succ]; exact ih.inter (measurableSet_gridCell c.ρ (m + 1) _)

/-- Every member of the nested sequence meets the window in a set of positive measure. -/
theorem winCfam_pos (c : Chart μ t) : ∀ j, 0 < μ (chartW c ∩ c.θ ⁻¹' winCfam c j) := by
  intro j
  induction j with
  | zero =>
      have hsub : chartW c ⊆ c.θ ⁻¹' winCfam c 0 := by
        rw [winCfam_zero]
        exact fun x hx => hx.2.1
      rw [Set.inter_eq_left.mpr hsub]
      exact c.pos
  | succ m ih =>
      rw [winCfam_succ]
      exact winSel_spec c (exists_grid_cell_pos (μ := μ) (ρ := c.ρ) (ℓ := m + 1) (θ := c.θ)
        (W := chartW c) (C := winCfam c m) ih)

end Work.EKLC6Route
