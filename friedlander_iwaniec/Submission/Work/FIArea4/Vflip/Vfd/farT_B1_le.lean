import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarWDefs

namespace Work.FIArea4.Vflip.Vfd

/-- The second bracket term of the `(m,c)`-piece: `m · 16RS/(cD) · √(⌈R/c⌉·S)` is bounded by
`16√2 · m · (RS/c)^{3/2} / D`.  The only input is `⌈R/c⌉ ≤ 2R/c`, which turns the square root
`√(⌈R/c⌉·S)` into `√2 · √(RS/c)`, and the identification `A^{3/2} = A·√A`. -/
theorem farT_B1_le (D R S : ℕ) (H : ℝ) (m c : ℕ)
    (hD : 0 < D) (hR : 1 ≤ R) (hS : 0 < S) (hc : 1 ≤ c) (hc2 : c ≤ 2 * R) :
    (m : ℝ) * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) * Real.sqrt ((cR c R : ℝ) * (S : ℝ))
      ≤ 16 * Real.sqrt 2 * (m : ℝ) * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  set A : ℝ := (R : ℝ) * (S : ℝ) / (c : ℝ) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hcRle : (cR c R : ℝ) ≤ 2 * (R : ℝ) / (c : ℝ) := cR_le_two_mul_div hc hR hc2
  have h1 : (cR c R : ℝ) * (S : ℝ) ≤ 2 * A := by
    rw [hAdef]
    calc (cR c R : ℝ) * (S : ℝ) ≤ (2 * (R : ℝ) / (c : ℝ)) * (S : ℝ) :=
          mul_le_mul_of_nonneg_right hcRle hSpos.le
      _ = 2 * ((R : ℝ) * (S : ℝ) / (c : ℝ)) := by field_simp
  have hsqrt_le : Real.sqrt ((cR c R : ℝ) * (S : ℝ)) ≤ Real.sqrt 2 * Real.sqrt A := by
    calc Real.sqrt ((cR c R : ℝ) * (S : ℝ)) ≤ Real.sqrt (2 * A) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 2 * Real.sqrt A := Real.sqrt_mul (by norm_num) A
  have h16 : (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) = 16 * A / D := by
    rw [hAdef]; field_simp
  have hAsqrt : A * Real.sqrt A = A ^ ((3 : ℝ) / 2) := by
    rcases eq_or_lt_of_le hAnn with hA0 | hApos
    · rw [← hA0]; simp
    · rw [Real.sqrt_eq_rpow]
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hApos, Real.rpow_one]
  calc (m : ℝ) * (16 * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (D : ℝ))) * Real.sqrt ((cR c R : ℝ) * (S : ℝ))
      = (m : ℝ) * (16 * A / D) * Real.sqrt ((cR c R : ℝ) * (S : ℝ)) := by rw [h16]
    _ ≤ (m : ℝ) * (16 * A / D) * (Real.sqrt 2 * Real.sqrt A) := by
        apply mul_le_mul_of_nonneg_left hsqrt_le
        positivity
    _ = 16 * Real.sqrt 2 * (m : ℝ) * (A ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
        rw [show A ^ ((3 : ℝ) / 2) = A * Real.sqrt A from hAsqrt.symm]
        field_simp
    _ = 16 * Real.sqrt 2 * (m : ℝ) * (((R : ℝ) * (S : ℝ) / (c : ℝ)) ^ ((3 : ℝ) / 2)) / (D : ℝ) := by
        rw [hAdef]

end Work.FIArea4.Vflip.Vfd
