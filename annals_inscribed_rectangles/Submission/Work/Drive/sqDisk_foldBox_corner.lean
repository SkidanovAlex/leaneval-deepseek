import Mathlib
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.linShearCharts

/-!
# The four corners of the square map to the boundary line `span {e₀, e₁}` of the linear charts

`Work.Drive.sqDisk` sends the four corners `{0,1}²` of the parameter square to the four points
`(±1 ± i)/√2` of the unit circle, and the fold `Work.Drive.foldBox` fixes those corners
(`foldFun 0 = 0`, `foldFun 1 = 1`).  Since `Work.Drive.linVecC z = ofComplex z (1 - ‖z‖²)` and
`‖sqDisk w‖ = 1` at a corner `w`, the sphere lift of a corner point lies in the **boundary line**
`span {linE0, linE1}` of the linear disk charts (`Work.Drive.linBdry`), and more precisely it is a
non-zero multiple of `linE0 + s • linE1` with `s = ±1`: the lift is `(a t, b t, 0, 0)` with
`a = 2 w 0 - 1 = ±1`, `b = 2 w 1 - 1 = ±1` and `t = sqWeight 1 ≠ 0`, i.e.
`(a t) • (linE0 + (a b) • linE1)`.

This is the corner bookkeeping used when a box presentation is restricted to the boundary square of a
chart: the four corner images of the square all lie on the boundary circle, and their lifts lie on
the boundary *line*.
-/

namespace Work.Drive

/-- `sqWeight` depends only on `|b|`, in particular `sqWeight b = sqWeight 1` for `b = ±1`. -/
lemma sqDiskCorner_sqWeight_eq {b : ℝ} (hb : |b| = 1) : sqWeight b = sqWeight 1 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hb with h | h
  · rw [h]
  · rw [h, sqWeight_even]

lemma sqDiskCorner_sqWeight_one_ne_zero : sqWeight 1 ≠ 0 :=
  ne_of_gt (sqWeight_pos (by norm_num))

/-- **`sqDisk` at a corner of the parameter square**: with `a = 2 w 0 - 1`, `b = 2 w 1 - 1` (both
`±1`) the two weights are equal to `sqWeight 1`, so `sqDisk w = a·t + b·t·I`. -/
lemma sqDiskCorner_sqDisk_eq (w : EuclideanSpace ℝ (Fin 2))
    (hw0 : w 0 = 0 ∨ w 0 = 1) (hw1 : w 1 = 0 ∨ w 1 = 1) :
    sqDisk w = ((2 * w 0 - 1) * sqWeight 1 : ℝ) + ((2 * w 1 - 1) * sqWeight 1 : ℝ) * Complex.I := by
  have ha : |2 * w 0 - 1| = 1 := by rcases hw0 with h | h <;> rw [h] <;> norm_num
  have hb : |2 * w 1 - 1| = 1 := by rcases hw1 with h | h <;> rw [h] <;> norm_num
  conv_lhs => rw [sqDisk]
  rw [sqDiskCorner_sqWeight_eq ha, sqDiskCorner_sqWeight_eq hb]

/-- The lift `ofComplex z 0` of a complex number with vanishing second coordinate is the
`ℝ⁴`-vector `(re z, im z, 0, 0) = re z • linE0 + im z • linE1` of the boundary line. -/
lemma sqDiskCorner_ofComplex_zero_eq (z : ℂ) :
    ofComplex z 0 = z.re • linE0 + z.im • linE1 := by
  ext i
  fin_cases i <;> simp [ofComplex, linE0, linE1]

/-- The real scalar bookkeeping: for `a = ±1` the vector `(a t) • linE0 + (b t) • linE1` is the
multiple `(a t) • (linE0 + (a b) • linE1)`. -/
lemma sqDiskCorner_smul_linE_add (a b t : ℝ) (haa : a * a = 1) :
    (a * t) • linE0 + (b * t) • linE1 = (a * t) • (linE0 + (a * b) • linE1) := by
  rw [smul_add, smul_smul, show (a * t) * (a * b) = b * t by
    have h : (a * t) * (a * b) = (a * a) * (t * b) := by ring
    rw [h, haa, one_mul]; ring]

/-- **The corner statement in the form needed by the charts**: a point of `ℝ²` whose two coordinates
are `0` or `1` has its `sqDisk`-image on the unit circle, and the sphere lift of that image is a
non-zero multiple of `linE0 + s • linE1` with `s = ±1`. -/
lemma sqDiskCorner_exists (w : EuclideanSpace ℝ (Fin 2))
    (hw0 : w 0 = 0 ∨ w 0 = 1) (hw1 : w 1 = 0 ∨ w 1 = 1) :
    ∃ (c s : ℝ), c ≠ 0 ∧ (s = 1 ∨ s = -1) ∧
      linVecC (sqDisk w) = c • (linE0 + s • linE1) := by
  have hmem : w ∈ Submission.Drive.unitBox 1 := fun i => by
    fin_cases i <;> dsimp only
    · rcases hw0 with h | h <;> simp [Set.mem_Icc, h]
    · rcases hw1 with h | h <;> simp [Set.mem_Icc, h]
  have ha : (2 * w 0 - 1) ^ 2 = 1 := by rcases hw0 with h | h <;> rw [h] <;> norm_num
  have hb : (2 * w 1 - 1) ^ 2 = 1 := by rcases hw1 with h | h <;> rw [h] <;> norm_num
  have haa : (2 * w 0 - 1) * (2 * w 0 - 1) = 1 := by rw [← sq]; exact ha
  -- the corner image lies on the unit circle
  have hnorm : ‖sqDisk w‖ = 1 := by
    have hsq : ‖sqDisk w‖ ^ 2 = 1 := by
      rw [norm_sqDisk_sq w hmem, ha, hb]; ring
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · exact absurd h (by linarith [norm_nonneg (sqDisk w)])
  -- hence the sphere lift has vanishing second complex coordinate
  have hlin : linVecC (sqDisk w) = ofComplex (sqDisk w) 0 := by
    unfold linVecC
    rw [show (1 : ℝ) - ‖sqDisk w‖ ^ 2 = 0 by rw [hnorm]; norm_num]
    norm_num
  have hre : (sqDisk w).re = (2 * w 0 - 1) * sqWeight 1 := by
    rw [sqDisk_apply_re,
      sqDiskCorner_sqWeight_eq (by rcases hw1 with h | h <;> rw [h] <;> norm_num)]
  have him : (sqDisk w).im = (2 * w 1 - 1) * sqWeight 1 := by
    rw [sqDisk_apply_im,
      sqDiskCorner_sqWeight_eq (by rcases hw0 with h | h <;> rw [h] <;> norm_num)]
  refine ⟨(2 * w 0 - 1) * sqWeight 1, (2 * w 0 - 1) * (2 * w 1 - 1), ?_, ?_, ?_⟩
  · exact mul_ne_zero (by rcases hw0 with h | h <;> rw [h] <;> norm_num)
      sqDiskCorner_sqWeight_one_ne_zero
  · rcases hw0 with h | h <;> rcases hw1 with h' | h' <;> rw [h, h'] <;> norm_num
  · rw [hlin, sqDiskCorner_ofComplex_zero_eq, hre, him, sqDiskCorner_smul_linE_add _ _ _ haa]

theorem sqDisk_foldBox_corner (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 = 0 ∨ y 0 = 1) (h1 : y 1 = 0 ∨ y 1 = 1) :
    ∃ (c s : ℝ), c ≠ 0 ∧ (s = 1 ∨ s = -1) ∧
      Work.Drive.linVecC (Work.Drive.sqDisk (Work.Drive.foldBox y))
        = c • (Work.Drive.linE0 + s • Work.Drive.linE1) := by
  have hw0 : foldBox y 0 = 0 ∨ foldBox y 0 = 1 := by
    rw [foldBox_apply_zero]
    rcases h0 with h | h <;> rw [h] <;> simp [foldFun_zero, foldFun_one]
  have hw1 : foldBox y 1 = 0 ∨ foldBox y 1 = 1 := by
    rw [foldBox_apply_one]
    rcases h1 with h | h <;> rw [h] <;> simp [foldFun_zero, foldFun_one]
  exact sqDiskCorner_exists (foldBox y) hw0 hw1

end Work.Drive
