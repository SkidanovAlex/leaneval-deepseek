import Mathlib
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.cappingProjCoords

namespace Work.Drive

open scoped Manifold ContDiff

/-! ### Real scaling in the complex coordinates of `ℂ² ≅ ℝ⁴`

The real scalars act componentwise on the coordinates `c₁`, `c₂`, so scaling `linVecC z =
(z, 1 - ‖z‖²)` by a real `a` multiplies both complex coordinates by `(a : ℂ)`. -/

lemma c₁_smul_eucl (a : ℝ) (v : Eucl 3) : c₁ (a • v) = (a : ℂ) * c₁ v := by
  simp [c₁]; ring

lemma c₂_smul_eucl (a : ℝ) (v : Eucl 3) : c₂ (a • v) = (a : ℂ) * c₂ v := by
  simp [c₂]; ring

/-- Real scaling of the coordinate dictionary `ofComplex`. -/
lemma smul_ofComplex (a : ℝ) (z z' : ℂ) :
    a • ofComplex z z' = ofComplex ((a : ℂ) * z) ((a : ℂ) * z') := by
  have h1 : c₁ (a • ofComplex z z') = (a : ℂ) * z := by rw [c₁_smul_eucl, c₁_ofComplex]
  have h2 : c₂ (a • ofComplex z z') = (a : ℂ) * z' := by rw [c₂_smul_eucl, c₂_ofComplex]
  calc a • ofComplex z z'
      = ofComplex (c₁ (a • ofComplex z z')) (c₂ (a • ofComplex z z')) :=
        (ofComplex_c₁_c₂ _).symm
    _ = ofComplex ((a : ℂ) * z) ((a : ℂ) * z') := by rw [h1, h2]

/-- Real scaling of the standard sphere lift `linVecC z = (z, 1 - ‖z‖²)`. -/
lemma smul_linVecC (a : ℝ) (z : ℂ) :
    a • linVecC z = ofComplex ((a : ℂ) * z) (Complex.ofReal (a * (1 - ‖z‖ ^ 2))) := by
  rw [linVecC, smul_ofComplex]
  congr 1
  rw [Complex.ofReal_mul]

/-- The norm of a real number, viewed in `ℂ`. -/
lemma norm_ofReal_eq_abs (a : ℝ) : ‖((a : ℝ) : ℂ)‖ = |a| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]

/-- **A non-zero real root of `X² - t X - n²` that dominates `n`.**  The quadratic
`X² - t X - n²` has discriminant `t² + 4 n² ≥ 0`, hence real roots; choosing the sign of the square
root according to the sign of `t` makes the chosen root `a` satisfy `n ≤ |a|` (and `a ≠ 0` as soon as
`t ≠ 0 ∨ n ≠ 0`). -/
lemma exists_nonzero_root {t n : ℝ} (hn : 0 ≤ n) (htn : t ≠ 0 ∨ n ≠ 0) :
    ∃ a : ℝ, a ≠ 0 ∧ n ≤ |a| ∧ a ^ 2 - t * a - n ^ 2 = 0 := by
  have hD : 0 ≤ t ^ 2 + 4 * n ^ 2 := by positivity
  set r := Real.sqrt (t ^ 2 + 4 * n ^ 2) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = t ^ 2 + 4 * n ^ 2 := Real.sq_sqrt hD
  have h2n : 2 * n ≤ r := by
    have h : (2 * n) ^ 2 ≤ r ^ 2 := by rw [hrsq]; nlinarith [sq_nonneg t]
    have h' : |2 * n| ≤ |r| := sq_le_sq.mp h
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg hr0] at h'
  rcases lt_or_ge t 0 with ht | ht
  · refine ⟨(t - r) / 2, ?_, ?_, ?_⟩
    · intro ha
      have : r ≤ 0 := by linarith
      have : r = 0 := le_antisymm this hr0
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
    · nlinarith [hrsq]
  · refine ⟨(t + r) / 2, ?_, ?_, ?_⟩
    · intro ha
      have ht0 : t = 0 := by linarith
      have hr' : r = 0 := by linarith
      have hn0 : n = 0 := by nlinarith [hrsq]
      rcases htn with h | h
      · exact h ht0
      · exact h hn0
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · nlinarith [hrsq]

open Manifold in
open scoped Manifold ContDiff in
/-- **The standard disk model of `ℝP²` covers its whole projective plane.**  Every vector of the
hyperplane `{v : v 3 = 0}` of `ℂ² ≅ ℝ⁴` (i.e. every vector of the form `(w₁, t)` with `t` real, not
both components zero) is a non-zero real multiple of a standard lift `linVecC z = (z, 1 - ‖z‖²)` with
`‖z‖ ≤ 1`.  Equivalently: the parametrised set `{[linVecC z] : ‖z‖ ≤ 1}` is *all* of
`projLine (linStd) ≅ ℝP²`, so `Work.Drive.linPlaneChart φ c hc` covers the whole projective plane
`φ (linStd)` of the level `c` with parameters in the closed unit disk.

This is the surjectivity companion of `Work.Drive.linPlaneChart_eq_iff`
(`linPlaneChartInjective.lean`, injectivity on the closed disk up to the antipodal identification);
the norm bound `‖z‖ ≤ 1` is part of the statement so that the two can be applied together.

Proof: `a • linVecC z = ofComplex (a * z) (a * (1 - ‖z‖ ^ 2))` for real `a` (the real scalars act
componentwise in the coordinates), so the goal is the system `a * z = w₁`,
`a * (1 - ‖z‖ ^ 2) = t`, i.e. `z = w₁ / a` with `a` a non-zero real root of
`X ^ 2 - t * X - ‖w₁‖ ^ 2` (quadratic formula, discriminant `t ^ 2 + 4 ‖w₁‖ ^ 2 ≥ 0`).  Taking
`a = (t + s √(t ^ 2 + 4 ‖w₁‖ ^ 2)) / 2` with `s = 1` for `0 ≤ t` and `s = -1` for `t < 0` gives
`a ≠ 0` (the roots are `t` and `0` when `w₁ = 0`, and neither is non-zero there, and have non-zero
product when `w₁ ≠ 0`) and `|a| ≥ ‖w₁‖`, whence `‖z‖ = ‖w₁‖ / |a| ≤ 1`. -/
theorem linVecC_smul_surjective {w₁ : ℂ} {t : ℝ} (hw : w₁ ≠ 0 ∨ t ≠ 0) :
    ∃ (z : ℂ) (a : ℝ), a ≠ 0 ∧ ‖z‖ ≤ 1 ∧ a • Work.Drive.linVecC z
      = Work.Drive.ofComplex w₁ ((t : ℝ) : ℂ) := by
  have hn : 0 ≤ ‖w₁‖ := norm_nonneg _
  have htn : t ≠ 0 ∨ ‖w₁‖ ≠ 0 := by
    rcases hw with h | h
    · exact Or.inr (fun h' => h (norm_eq_zero.mp h'))
    · exact Or.inl h
  obtain ⟨a, ha0, han, haeq⟩ := exists_nonzero_root hn htn
  have haC : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0
  refine ⟨w₁ / ((a : ℝ) : ℂ), a, ha0, ?_, ?_⟩
  · rw [norm_div, norm_ofReal_eq_abs]
    exact div_le_one_of_le₀ han (abs_nonneg _)
  · rw [smul_linVecC]
    congr 1
    · rw [← mul_div_assoc, mul_div_cancel_left₀ _ haC]
    · apply congrArg Complex.ofReal
      have hn2 : ‖w₁‖ ^ 2 = a ^ 2 - t * a := by linarith [haeq]
      have hnorm : ‖w₁ / ((a : ℝ) : ℂ)‖ ^ 2 = 1 - t / a := by
        rw [norm_div, norm_ofReal_eq_abs, div_pow, sq_abs, hn2]
        field_simp
      have hkey : (1 : ℝ) - (1 - t / a) = t / a := by ring
      rw [hnorm, hkey, ← mul_div_assoc, mul_div_cancel_left₀ _ ha0]

end Work.Drive
