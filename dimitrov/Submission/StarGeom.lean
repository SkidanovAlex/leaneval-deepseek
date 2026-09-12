import Mathlib
import Submission.XTransfer

/-!
# Spike-direction gap geometry of the hedgehog

For the deformation of the integration contour (E2b) one partitions the region
between the big circle and the fattened hedgehog `star S` into annular-sector
cells.  A cell is the exp-image of a w-rectangle

    C := {exp w : Re w ∈ [a, b], Im w ∈ [c, d]}

with `d - c < 2π` (so the cell is a genuine annular sector).  Such a cell
avoids the hedgehog as soon as no *spike endpoint* (an element of
`{z², z⁴ : z ∈ S}`) points into the angular range `[c, d] ⊆ (-π, π]`: every
point of the hedgehog lies on a segment `[0, z²]` or `[0, z⁴]`, i.e. on a ray
in the direction of a spike endpoint, while every point `exp w` of the cell
points in the direction `Im w`.

This module proves that single-gap fact:

    `expRect_avoids_star`:  if no spike endpoint has argument in the closed
    angular interval `[ymin, ymax] ⊆ (-π, π]`, then the exp-image of every
    w-rectangle whose imaginary part ranges over `[ymin, ymax]` avoids
    `star S`.
-/

noncomputable section

open scoped Complex Real Interval
open Complex

namespace Submission.StarGeom

open Submission.XTransfer

/-- `arg (exp (x + y·I)) = y` for `y ∈ (-π, π]`. -/
lemma arg_exp_add_mul_I {x y : ℝ} (hyl : -π < y) (hyu : y ≤ π) :
    Complex.arg (Complex.exp (x + y * Complex.I)) = y := by
  rw [Complex.arg_exp]
  rw [show (x + y * Complex.I).im = y by simp]
  rw [toIocMod_eq_self (p := (2 * π : ℝ)) (a := (-π : ℝ)) (b := y)]
  constructor
  · exact hyl
  · have h : -π + 2 * π = π := by ring
    rw [h]
    exact hyu

/-- `arg (exp w) = Im w` whenever `Im w ∈ (-π, π]`. -/
lemma arg_exp_eq_im {w : ℂ} (hyl : -π < w.im) (hyu : w.im ≤ π) :
    Complex.arg (Complex.exp w) = w.im := by
  rw [Complex.arg_exp]
  rw [toIocMod_eq_self (p := (2 * π : ℝ)) (a := (-π : ℝ)) (b := w.im)]
  constructor
  · exact hyl
  · have h : -π + 2 * π = π := by ring
    rw [h]
    exact hyu

/-- `arg (t • c) = arg c` when `0 < t` (real scalar action on `ℂ`). -/
lemma arg_smul_of_pos {c : ℂ} {t : ℝ} (ht : 0 < t) : Complex.arg (t • c) = Complex.arg c := by
  rw [show t • c = (t : ℂ) * c by rfl]
  exact Complex.arg_real_mul c ht

/-- A nonzero point of the segment `[0, c]` has the same argument as `c`. -/
lemma arg_eq_of_mem_segment_zero_ne_zero {X c : ℂ} (hX : X ∈ segment ℝ 0 c)
    (hX0 : X ≠ 0) : Complex.arg X = Complex.arg c := by
  rcases (mem_segment_zero_iff c X).mp hX with ⟨t, ht01, htX⟩
  have ht : 0 < t := by
    by_contra ht0
    have htle : t ≤ 0 := le_of_not_gt ht0
    have ht0' : t = 0 := le_antisymm htle ht01.1
    have : X = 0 := by
      rw [htX, ht0']
      simp
    exact hX0 this
  calc
    Complex.arg X = Complex.arg (t • c) := by rw [htX]
    _ = Complex.arg c := arg_smul_of_pos ht

/-- **Single-gap cell fact.**  If no spike endpoint `z²`, `z⁴` (`z ∈ S`) has
argument in the closed angular interval `[ymin, ymax] ⊆ (-π, π]`, then the
exp-image of every w-rectangle with imaginary range `[ymin, ymax]` avoids the
hedgehog. -/
lemma expRect_avoids_star {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {xmin xmax ymin ymax : ℝ} (hy : ymin < ymax) (hyl : -π < ymin) (hyu : ymax ≤ π)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc ymin ymax ∧ Complex.arg (z ^ 4) ∉ Set.Icc ymin ymax) :
    ∀ w ∈ ([[xmin, xmax]] ×ℂ [[ymin, ymax]]), Complex.exp w ∉ star S := by
  intro w hw hws
  have hwim : w.im ∈ Set.Icc ymin ymax := by
    have hwim0 := (Complex.mem_reProdIm.mp hw).2
    simpa [Set.uIcc_of_le (le_of_lt hy)] using hwim0
  have hylw : -π < w.im := lt_of_lt_of_le hyl hwim.1
  have hyuw : w.im ≤ π := le_trans hwim.2 hyu
  have hargw : Complex.arg (Complex.exp w) = w.im := arg_exp_eq_im hylw hyuw
  have hstar : ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) := by
    change ∃ z ∈ S, Complex.exp w ∈ segment ℝ 0 (z ^ 2) ∨ Complex.exp w ∈ segment ℝ 0 (z ^ 4) at hws
    exact hws
  rcases hstar with ⟨z, hz, hseg⟩
  have hexp0 : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hz0 : z ≠ 0 := hS0 z hz
  rcases hseg with h2 | h4
  · -- exp w on the segment [0, z²]
    have harg2 : Complex.arg (z ^ 2) = w.im := by
      calc
        Complex.arg (z ^ 2) = Complex.arg (Complex.exp w) :=
          (arg_eq_of_mem_segment_zero_ne_zero h2 hexp0).symm
        _ = w.im := hargw
    exfalso
    exact (hno z hz).1 (by
      rw [harg2]
      exact hwim)
  · -- exp w on the segment [0, z⁴]
    have harg4 : Complex.arg (z ^ 4) = w.im := by
      calc
        Complex.arg (z ^ 4) = Complex.arg (Complex.exp w) :=
          (arg_eq_of_mem_segment_zero_ne_zero h4 hexp0).symm
        _ = w.im := hargw
    exfalso
    exact (hno z hz).2 (by
      rw [harg4]
      exact hwim)

end Submission.StarGeom

end
