import Mathlib
import Submission.Work.Holonomy3.lowdiscCells

/-!
# The measure of a union of grid cells

The cells `cell d D k = ∏_j [k_j/D, (k_j+1)/D)` of `Work.Holonomy3.lowdiscCells` attached to
distinct exponent vectors `k` are pairwise disjoint, each has `(muP d)`-measure `D^{-d}`, and
`cell_biUnion_measure` records the resulting additivity of the measure over a finset of such `k`.
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open scoped BigOperators
open MeasureTheory

/-- Each grid cell is a product of half-open intervals, hence measurable. -/
lemma cell_measurable (d D : ℕ) (k : Fin d → ℕ) : MeasurableSet (cell d D k) := by
  rw [cell]
  exact MeasurableSet.univ_pi (fun j => measurableSet_Ico)

/-- Cells attached to distinct exponent vectors are disjoint: if `k ≠ k'` there is a coordinate `j`
with `k j ≠ k' j`, and the half-open intervals `[k_j/D, (k_j+1)/D)`, `[k'_j/D, (k'_j+1)/D)` are
then disjoint. -/
lemma cell_disjoint {d D : ℕ} (hD : 0 < D) {k k' : Fin d → ℕ} (h : k ≠ k') :
    Disjoint (cell d D k) (cell d D k') := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext u
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hu hu'
  apply h
  funext j
  rw [mem_cell] at hu hu'
  have hu1 := (hu j).1
  have hu2 := (hu j).2
  have hu'1 := (hu' j).1
  have hu'2 := (hu' j).2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have hDpos : (0:ℝ) < D := by exact_mod_cast hD
    have hcast : ((k j : ℝ) + 1) ≤ (k' j : ℝ) := by
      have : k j + 1 ≤ k' j := hlt
      exact_mod_cast this
    have hdiv : ((k j : ℝ) + 1)/(D:ℝ) ≤ (k' j : ℝ)/(D:ℝ) :=
      div_le_div_of_nonneg_right hcast (le_of_lt hDpos)
    linarith
  · exfalso
    have hDpos : (0:ℝ) < D := by exact_mod_cast hD
    have hcast : ((k' j : ℝ) + 1) ≤ (k j : ℝ) := by
      have : k' j + 1 ≤ k j := hgt
      exact_mod_cast this
    have hdiv : ((k' j : ℝ) + 1)/(D:ℝ) ≤ (k j : ℝ)/(D:ℝ) :=
      div_le_div_of_nonneg_right hcast (le_of_lt hDpos)
    linarith

/-- A single coordinate interval of a cell with `k j < D` lies in `[0,1)` and has `nu`-measure
`D^{-1}`. -/
lemma nu_cell_coord {d D : ℕ} (hD : 0 < D) (k : Fin d → ℕ) (j : Fin d) (hk : k j < D) :
    nu (Set.Ico ((k j : ℝ)/(D:ℝ)) (((k j : ℝ)+1)/(D:ℝ)))
      = ENNReal.ofReal ((D:ℝ)⁻¹) := by
  have hDpos : (0:ℝ) < D := by exact_mod_cast hD
  have hkpos : (0:ℝ) ≤ (k j : ℝ) := Nat.cast_nonneg _
  have h0 : (0:ℝ) ≤ (k j : ℝ)/(D:ℝ) := div_nonneg hkpos (le_of_lt hDpos)
  have h1 : ((k j : ℝ)+1)/(D:ℝ) ≤ 1 := by
    rw [div_le_one hDpos]
    have : k j + 1 ≤ D := hk
    exact_mod_cast this
  rw [nu_Ico h0 h1]
  congr 1
  field_simp
  ring

/-- The `(muP d)`-measure of a grid cell with `k j < D` is `D^{-d}`. -/
lemma muP_cell {d D : ℕ} (hD : 0 < D) {k : Fin d → ℕ} (hk : ∀ j, k j < D) :
    (muP d) (cell d D k) = ENNReal.ofReal (((D:ℝ)^d)⁻¹) := by
  rw [show muP d = Measure.pi (fun _ : Fin d => nu) from rfl]
  rw [cell, Measure.pi_pi]
  rw [Finset.prod_congr rfl (fun j _ => nu_cell_coord hD k j (hk j))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity), inv_pow]

/-- The `(muP d).real`-measure of a grid cell with `k j < D` is `D^{-d}`. -/
lemma muP_cell_real {d D : ℕ} (hD : 0 < D) {k : Fin d → ℕ} (hk : ∀ j, k j < D) :
    (muP d).real (cell d D k) = ((D:ℝ)^d)⁻¹ := by
  rw [MeasureTheory.Measure.real, muP_cell hD hk, ENNReal.toReal_ofReal (by positivity)]

/-- **The measure of a union of grid cells.** The cells `cell d D k` attached to the exponent
vectors `k` of a finset `s`, all of whose coordinates are `< D`, are pairwise disjoint and each has
`(muP d)`-measure `D^{-d}`; hence the union has measure `s.card · D^{-d}`. -/
theorem cell_biUnion_measure {d : ℕ} (hd : 0 < d) (D : ℕ) (hD : 0 < D)
    (s : Finset (Fin d → ℕ)) (hs : ∀ k ∈ s, ∀ j, k j < D) :
    (Submission.CDT.Discrepancy.muP d).real (⋃ k ∈ s, Work.Holonomy3.cell d D k) =
      (s.card : ℝ) * ((D : ℝ) ^ d)⁻¹ := by
  rw [MeasureTheory.measureReal_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun k hk => muP_cell_real hD (hs k hk))]
    rw [Finset.sum_const, nsmul_eq_mul]
  · intro a _ b _ hab
    exact cell_disjoint hD hab
  · intro b _
    exact cell_measurable d D b

end Work.Holonomy3
