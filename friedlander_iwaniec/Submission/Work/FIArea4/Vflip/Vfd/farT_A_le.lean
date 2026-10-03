import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarWDefs

namespace Work.FIArea4.Vflip.Vfd

/-- The first (linear-in-`√`) piece `A` of the bracket `farT` is dominated by the target term
`2√5 · (DHR S/(c m))^{1/2}`.  The two sides differ exactly by the factor `c⌈R/c⌉/(2R) ≤ 1`,
which is the content of `cR_le_two_mul_div`. -/
theorem farT_A_le (D R S : ℕ) (H : ℝ) (m c : ℕ)
    (hD : 0 < D) (hR : 1 ≤ R) (hS : 0 < S) (hH : 0 < H) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hc2 : c ≤ 2 * R) :
    ((m : ℝ) * ((S : ℝ) * (R : ℝ) / (5 * H * (c : ℝ) * (D : ℝ)))) ^ (-(1 : ℝ) / 2)
        * ((cR c R : ℝ) * (S : ℝ))
      ≤ 2 * Real.sqrt 5 * ((D : ℝ) * H * (R : ℝ) * (S : ℝ) / ((c : ℝ) * (m : ℝ))) ^ ((1 : ℝ) / 2) := by
  have hc0 : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have hS0 : (0:ℝ) < (S:ℝ) := by exact_mod_cast hS
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR
  have hH0 : (0:ℝ) < H := hH
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  -- The key numerical input: `c · ⌈R/c⌉ ≤ 2R`.
  have hkey : (c : ℝ) * (cR c R : ℝ) ≤ 2 * (R : ℝ) := by
    have h := cR_le_two_mul_div hc hR hc2
    rw [le_div_iff₀ hc0] at h
    linarith [h]
  have hkey_sq : ((c:ℝ)*(cR c R:ℝ)) * ((c:ℝ)*(cR c R:ℝ)) ≤ (2*(R:ℝ))*(2*(R:ℝ)) :=
    mul_self_le_mul_self (by positivity) hkey
  set A : ℝ := (m:ℝ) * ((S:ℝ)*(R:ℝ)/(5*H*(c:ℝ)*(D:ℝ))) with hAdef
  set B : ℝ := (cR c R : ℝ) * (S:ℝ) with hBdef
  set E : ℝ := (D:ℝ)*H*(R:ℝ)*(S:ℝ)/((c:ℝ)*(m:ℝ)) with hEdef
  set Y : ℝ := 5*H*(c:ℝ)*(D:ℝ)/((m:ℝ)*(S:ℝ)*(R:ℝ)) with hYdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hYnn : 0 ≤ Y := by rw [hYdef]; positivity
  -- `A ^ (-1/2) · B = √(Y · B²)` with `Y = A⁻¹ = 5HcD/(mSR)`.
  have hlhs : A ^ (-(1:ℝ)/2) * B = Real.sqrt (Y * B^2) := by
    have h1 : A ^ (-(1:ℝ)/2) = (A⁻¹) ^ ((1:ℝ)/2) := by
      rw [show -(1:ℝ)/2 = (-1:ℝ) * (1/2) by norm_num, Real.rpow_mul hApos.le, Real.rpow_neg_one]
    rw [h1, show A⁻¹ = Y from by rw [hAdef, hYdef]; field_simp]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hYnn, Real.sqrt_sq hBnn]
  -- `2√5 · E^{1/2} = √(20 E)`.
  have hrhs : 2 * Real.sqrt 5 * E ^ ((1:ℝ)/2) = Real.sqrt (20 * E) := by
    have h20 : (2:ℝ) * Real.sqrt 5 = Real.sqrt 20 := by
      rw [show (20:ℝ) = 4 * 5 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 20), h20]
  -- The comparison of the radicals: `Y · B² ≤ 20 E`.
  have hsq : Y * B^2 ≤ 20 * E := by
    rw [hYdef, hBdef, hEdef]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ)*(S:ℝ)*(R:ℝ))]
    field_simp
    nlinarith [hkey_sq, sq_nonneg ((cR c R:ℝ)), sq_nonneg ((S:ℝ)), sq_nonneg ((R:ℝ)),
      sq_nonneg ((c:ℝ))]
  calc A ^ (-(1:ℝ)/2) * B = Real.sqrt (Y * B^2) := hlhs
    _ ≤ Real.sqrt (20 * E) := Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt 5 * E ^ ((1:ℝ)/2) := hrhs.symm

end Work.FIArea4.Vflip.Vfd
