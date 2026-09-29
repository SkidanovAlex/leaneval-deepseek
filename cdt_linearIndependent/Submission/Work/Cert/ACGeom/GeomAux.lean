import Mathlib
import Submission.Work.Cert.Spec

/-!
# Elementary facts about the scaled complex numbers `cx`

`cx x y = (x/S) + (y/S)·I` (module `Submission.Work.Cert.Spec`).  This file collects the
basic casting/algebra lemmas that the geometric soundness lemmas about `geomOK` need:
positivity of the scale `S`, the real/imaginary parts of `cx`, additivity/subtraction,
the squared norm, and the order isomorphism `iabs (-) : ℤ → ℝ ↦ |·|`.
-/
namespace Work.Cert.ACGeom

open Work.Cert

lemma S_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]

lemma S_ne : (S : ℝ) ≠ 0 := ne_of_gt S_pos

lemma CTOL_pos : (0 : ℝ) < (CTOL : ℝ) := by norm_num [CTOL]

@[simp] lemma cx_re (x y : ℤ) : (cx x y).re = (x : ℝ) / (S : ℝ) := by simp [cx]

@[simp] lemma cx_im (x y : ℤ) : (cx x y).im = (y : ℝ) / (S : ℝ) := by simp [cx]

lemma cx_add (x₁ y₁ x₂ y₂ : ℤ) : cx x₁ y₁ + cx x₂ y₂ = cx (x₁ + x₂) (y₁ + y₂) := by
  apply Complex.ext <;> simp [Int.cast_add, add_div]

lemma cx_sub (x₁ y₁ x₂ y₂ : ℤ) : cx x₁ y₁ - cx x₂ y₂ = cx (x₁ - x₂) (y₁ - y₂) := by
  apply Complex.ext <;> simp [Int.cast_sub, sub_div]

lemma cx_neg (x y : ℤ) : -cx x y = cx (-x) (-y) := by
  apply Complex.ext <;> simp [neg_div]

lemma normSq_cx (x y : ℤ) :
    Complex.normSq (cx x y) = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / (S : ℝ) ^ 2 := by
  rw [Complex.normSq_apply, cx_re, cx_im]
  field_simp

lemma norm_sq_cx (x y : ℤ) :
    ‖cx x y‖ ^ 2 = ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / (S : ℝ) ^ 2 := by
  rw [Complex.sq_norm, normSq_cx]

/-- `iabs` is `|·|` transported to `ℤ`. -/
lemma iabs_cast (a : ℤ) : ((iabs a : ℤ) : ℝ) = |(a : ℝ)| := by
  rw [iabs]
  split_ifs with h
  · rw [Int.cast_neg, abs_of_neg]
    exact_mod_cast h
  · rw [abs_of_nonneg]
    exact_mod_cast (not_lt.mp h)

lemma iabs_nonneg (a : ℤ) : 0 ≤ iabs a := by
  rw [iabs]; split_ifs with h
  · exact neg_nonneg.mpr (le_of_lt h)
  · exact not_lt.mp h

lemma Rk_pos_int (k : ℕ) : 0 < Rk k := by
  unfold Rk; split_ifs <;> decide

lemma Rk_pos_real (k : ℕ) : (0 : ℝ) < (Rk k : ℝ) := by exact_mod_cast Rk_pos_int k

lemma Rk_nonneg_real (k : ℕ) : (0 : ℝ) ≤ (Rk k : ℝ) := le_of_lt (Rk_pos_real k)

/-- The chord bound: two points of the certificate whose scaled distance is at most `chU` are at
distance at most `chU / S`. -/
lemma chord_bound (x₁ y₁ x₂ y₂ chU : ℤ) (hchU : 0 ≤ chU)
    (h : (x₂ - x₁) * (x₂ - x₁) + (y₂ - y₁) * (y₂ - y₁) ≤ chU * chU) :
    ‖cx x₁ y₁ - cx x₂ y₂‖ ≤ (chU : ℝ) / (S : ℝ) := by
  rw [cx_sub]
  have hsq : ‖cx (x₁ - x₂) (y₁ - y₂)‖ ^ 2 ≤ ((chU : ℝ) / (S : ℝ)) ^ 2 := by
    rw [norm_sq_cx, div_pow]
    have hZ : ((x₂ - x₁) * (x₂ - x₁) + (y₂ - y₁) * (y₂ - y₁) : ℝ) ≤ (chU : ℝ) * (chU : ℝ) := by
      exact_mod_cast h
    have hR : ((x₂ - x₁ : ℤ) : ℝ) ^ 2 + ((y₂ - y₁ : ℤ) : ℝ) ^ 2 ≤ (chU : ℝ) ^ 2 := by
      push_cast at hZ ⊢
      nlinarith [hZ]
    have e1 : ((x₁ - x₂ : ℤ) : ℝ) = -(((x₂ - x₁ : ℤ)) : ℝ) := by push_cast; ring
    have e2 : ((y₁ - y₂ : ℤ) : ℝ) = -(((y₂ - y₁ : ℤ)) : ℝ) := by push_cast; ring
    rw [e1, e2]
    rw [div_le_div_iff_of_pos_right (pow_pos S_pos 2)]
    nlinarith [hR]
  have h2 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (div_nonneg (by exact_mod_cast hchU) (le_of_lt S_pos))] at h2

end Work.Cert.ACGeom
