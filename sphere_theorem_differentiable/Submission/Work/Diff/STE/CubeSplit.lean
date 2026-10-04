import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Splitting the unit cube along one coordinate

This file contains the elementary object used to split an integral over the unit cube
`unitCube ⊆ (ι → ℝ)` along the `i`-th coordinate: given the remaining coordinates
`y : {j // j ≠ i} → ℝ` and a real `t`, the vector `insertAt i t y : ι → ℝ` has `i`-th
coordinate `t` and the other coordinates copied from `y`.

The two analytic facts about it (Fubini for the cube, and the fundamental theorem of
calculus for a function periodic in the `i`-th coordinate) are stated and proved in the
sibling files `cube_fubini` and `pd_integral_zero`.
-/

noncomputable section

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector obtained from `y : {j // j ≠ i} → ℝ` by inserting `t` in the `i`-th coordinate. -/
def insertAt (i : ι) (t : ℝ) (y : {j : ι // j ≠ i} → ℝ) : ι → ℝ :=
  fun j => if h : j = i then t else y ⟨j, h⟩

@[simp] lemma insertAt_self (i : ι) (t : ℝ) (y : {j : ι // j ≠ i} → ℝ) :
    insertAt i t y i = t := by
  simp [insertAt]

lemma insertAt_of_ne {i j : ι} (h : j ≠ i) (t : ℝ) (y : {j : ι // j ≠ i} → ℝ) :
    insertAt i t y j = y ⟨j, h⟩ := by
  simp [insertAt, h]

/-- `insertAt` is an update of the vector with `0` in the `i`-th coordinate. -/
lemma insertAt_eq_update (i : ι) (t : ℝ) (y : {j : ι // j ≠ i} → ℝ) :
    insertAt i t y = Function.update (insertAt i 0 y) i t := by
  funext j
  by_cases h : j = i
  · subst h; simp [insertAt]
  · simp [insertAt, h, Function.update, h]

/-- `insertAt` is affine in `t`. -/
lemma insertAt_add (i : ι) (t s : ℝ) (y : {j : ι // j ≠ i} → ℝ) :
    insertAt i (t + s) y = insertAt i t y + s • Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [insertAt, Pi.single_eq_same]
  · simp [insertAt, h, Pi.single_eq_of_ne (M := fun _ : ι => ℝ) (by simpa using h),
      Pi.single_eq_of_ne (M := fun _ : ι => ℝ) h]

/-- Shifting the `i`-th coordinate from `0` to `1` is translation by the basic vector `eᵢ`. -/
lemma insertAt_one_eq_insertAt_zero_add (i : ι) (y : {j : ι // j ≠ i} → ℝ) :
    insertAt i 1 y = insertAt i 0 y + Pi.single i 1 := by
  have := insertAt_add i 0 1 y
  simpa using this

/-- `t ↦ insertAt i t y` is affine, with derivative `eᵢ`. -/
lemma hasDerivAt_insertAt (i : ι) (y : {j : ι // j ≠ i} → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => insertAt i s y) (Pi.single i 1) t := by
  have h : (fun s : ℝ => insertAt i s y)
      = fun s : ℝ => insertAt i 0 y + s • (Pi.single i 1 : ι → ℝ) := by
    funext s
    simpa using insertAt_add i 0 s y
  rw [h]
  have h1 : HasDerivAt (fun s : ℝ => s • (Pi.single i 1 : ι → ℝ)) (Pi.single i 1) t := by
    simpa using (hasDerivAt_id t).smul_const (Pi.single i 1 : ι → ℝ)
  simpa using h1.const_add (insertAt i 0 y)

end Work.Diff.STE
