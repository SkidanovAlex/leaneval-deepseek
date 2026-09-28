import Mathlib

/-!
# The uniform grid on `[-1,1]` used for the separation-from-measure argument

`hpGrid h j = [j*h - 1, (j+1)*h - 1)` is the `j`-th cell of the uniform grid of mesh `h`
on the real line, indexed so that `hpGrid h 0 = [-1, h-1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.HP.HP2

/-- The half-open interval `[j*h - 1, (j+1)*h - 1)`, the `j`-th cell of the uniform grid of mesh
`h` on the real line, indexed so that `hpGrid h 0` is `[-1, h - 1)`. -/
def hpGrid (h : ℝ) (j : ℕ) : Set ℝ := Set.Ico ((j : ℝ) * h - 1) (((j : ℝ) + 1) * h - 1)

lemma measurableSet_hpGrid (h : ℝ) (j : ℕ) : MeasurableSet (hpGrid h j) :=
  measurableSet_Ico

lemma volume_hpGrid (h : ℝ) (j : ℕ) : volume (hpGrid h j) = ENNReal.ofReal h := by
  rw [hpGrid, Real.volume_Ico]
  congr 1
  ring

lemma hpGrid_disjoint {h : ℝ} (hh : 0 ≤ h) {j j' : ℕ} (hne : j ≠ j') :
    Disjoint (hpGrid h j) (hpGrid h j') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hpGrid, Set.mem_Ico] at hx hx'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hcast : (j : ℝ) + 1 ≤ (j' : ℝ) := by
      have : j + 1 ≤ j' := hlt
      exact_mod_cast this
    have hle : ((j : ℝ) + 1) * h ≤ (j' : ℝ) * h := mul_le_mul_of_nonneg_right hcast hh
    linarith [hx.2, hx'.1]
  · have hcast : (j' : ℝ) + 1 ≤ (j : ℝ) := by
      have : j' + 1 ≤ j := hlt
      exact_mod_cast this
    have hle : ((j' : ℝ) + 1) * h ≤ (j : ℝ) * h := mul_le_mul_of_nonneg_right hcast hh
    linarith [hx'.2, hx.1]

/-- Two points of cells of the grid separated by at least one full cell have distance
at least `h`. -/
lemma hpGrid_abs_sub_ge {h : ℝ} (hh : 0 ≤ h) {j j' : ℕ} (hgap : j + 2 ≤ j')
    {x y : ℝ} (hx : x ∈ hpGrid h j) (hy : y ∈ hpGrid h j') : h ≤ |x - y| := by
  simp only [hpGrid, Set.mem_Ico] at hx hy
  have hcast : (j : ℝ) + 2 ≤ (j' : ℝ) := by exact_mod_cast hgap
  have hle : ((j : ℝ) + 2) * h ≤ (j' : ℝ) * h := mul_le_mul_of_nonneg_right hcast hh
  have hxy : x + h ≤ y := by linarith [hx.2, hy.1]
  have hneg : x - y ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  linarith

end Work.HP.HP2
