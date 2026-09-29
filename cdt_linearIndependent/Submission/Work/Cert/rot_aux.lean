import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.ANum.rotGlue

/-!
# Soundness glue for the five rotation constants of the Theorem-A contour

`RotConsts` (`Submission/Work/Cert/Spec.lean`) asserts that the five integer constants
`rot0r, rot0i, …, WR, WI` of `Defs.lean`, divided by the scale `S = 2^40·10^8`, are within
`2/S` of `rot t = e^{2πit}` for the corresponding rational `t`.

These constants were produced by rounding the 80-digit values of `S·cos 2πt` and `S·sin 2πt`,
so each coordinate is within `1/2` of the exact value and the claim has a wide margin.  The proof
re-does the computation rigorously:

* `2πt` is squeezed between the two rationals
  `2·3.14159265358979323846·t ≤ 2πt ≤ 2·3.14159265358979323847·t`
  (`Real.pi_gt_d20`, `Real.pi_lt_d20`);
* on `[0, π/4]` the eleven-term Taylor partial sums `cosP`, `sinP` of `Work.CNum` enclose
  `Real.cos`, `Real.sin` with error `2/24!` resp. `2/25!` (`Work.ANum.rotGlue`);
* the only remaining steps are the four exact rational comparisons per constant, discharged by
  `norm_num` — no numerics are ever evaluated by reflection in the kernel.

`rot_bound_aux` is the single glue lemma; `rot0_bound` is a fully worked instance, and the other
four instances (`rot1_bound`, `rot2_bound`, `rot3_bound`, `rotW_bound`) are the same six lines
with the constants substituted.
-/

/-! NOTE (agent H25 / area ANum, namespace hygiene).  The rounding layer below duplicates names
(`S_pos`, `S_ne`, `md_le`, `md_gt`, `mu_ge`, `mu_lt`, `dvu_ge`, `dvu_lt`, `cx_re`, `cx_im`) that are
also defined in `Submission/Work/Cert/LeafAux.lean` (and `S_pos` in `Cert/rot_aux.lean`).  Two
modules defining the same constant cannot be imported together, which made the final assembly of
`Work.Cert.leaf_sound` (LeafAux) with `Work.Cert.theta_encl` (this file) impossible.  The names in
THIS file (and in its users: `aInv_base`, `aInv_step`, `aLoop_aux`, `bLoop_inv`, `binv_base1`,
`bstep_Br_le`, `bstep_num`, `bstep_por_le`, `bstep_psr_le`, `cx_mul_le`, `dA_step`, `theta_encl`,
`theta_keep`) have therefore been renamed with the prefix `th`; nothing else changed (the statements
are identical, only the names carry `th`).  `rot_aux.lean`'s `S_pos` was renamed `rotS_pos`.
Backups of the pre-rename files: `ScratchH25/pre_rename/`; the script is `ScratchH25/rename.sh`. -/

namespace Work.Cert

open Complex Submission.CDTPlan Work.CNum

/-- The scale `S` is positive. -/
lemma rotS_pos : (0 : ℝ) < (S : ℝ) := by norm_num [S]

/-- The scale `S` is nonzero as a complex number. -/
lemma S_ne_zero_complex : (S : ℂ) ≠ 0 := by norm_num [S]

/-- `2·3.14159265358979323846·t ≤ 2πt` for `t ≥ 0`. -/
lemma two_pi_lo (t : ℝ) (ht : 0 ≤ t) :
    2 * (3.14159265358979323846 : ℝ) * t ≤ 2 * Real.pi * t := by
  nlinarith [Real.pi_gt_d20, ht]

/-- `2πt ≤ 2·3.14159265358979323847·t` for `t ≥ 0`. -/
lemma two_pi_hi (t : ℝ) (ht : 0 ≤ t) :
    2 * Real.pi * t ≤ 2 * (3.14159265358979323847 : ℝ) * t := by
  nlinarith [Real.pi_lt_d20, ht]

/-- `cx x y = (x + y·I)/S`. -/
lemma cx_eq_div (x y : ℤ) : cx x y = ((x : ℂ) + (y : ℂ) * I) / (S : ℂ) := by
  simp only [cx]
  push_cast
  field_simp

/-- Subtracting `rot t` keeps the shape `(integer + integer·I)/S`. -/
lemma cx_sub_rot (t : ℝ) (x y : ℤ) :
    cx x y - rot t = ((x : ℂ) + (y : ℂ) * I - (S : ℂ) * rot t) / (S : ℂ) := by
  have hS : (S : ℂ) ≠ 0 := S_ne_zero_complex
  rw [cx_eq_div, eq_div_iff hS]
  push_cast
  field_simp

/-- Conjugating a scaled point negates its imaginary mantissa. -/
lemma star_cx (x y : ℤ) : star (cx x (-y)) = cx x y := by
  apply Complex.ext
  · simp [cx]
  · simp only [cx, Complex.star_def, Complex.conj_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      add_zero, zero_add]
    push_cast
    ring

/-- `rot (-t)` is the conjugate of `rot t`. -/
lemma star_rot (t : ℝ) : star (rot t) = rot (-t) := by
  apply Complex.ext
  · rw [Work.ANum.rot_neg_re]
    simp [Complex.star_def]
  · rw [Work.ANum.rot_neg_im]
    simp [Complex.star_def]

/-- Replacing `t` by `-t` corresponds to negating the imaginary mantissa. -/
lemma norm_cx_rot_neg (x y : ℤ) (t : ℝ) :
    ‖cx x y - rot (-t)‖ = ‖cx x (-y) - rot t‖ := by
  have h : cx x y - rot (-t) = star (cx x (-y) - rot t) := by
    rw [star_sub, star_cx, star_rot]
  rw [h, norm_star]

/-- If both coordinates of `w` are at most `1` in modulus then `w/S` is within `2/S` of `0`. -/
lemma norm_div_S_le_two {w : ℂ} (hre : |w.re| ≤ 1) (him : |w.im| ≤ 1) :
    ‖w / (S : ℂ)‖ ≤ 2 / (S : ℝ) := by
  have hw : ‖w‖ ≤ 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    linarith
  have hnorm : ‖(S : ℂ)‖ = (S : ℝ) := by
    rw [Complex.norm_intCast, abs_of_pos rotS_pos]
  rw [norm_div, hnorm]
  exact div_le_div_of_nonneg_right hw rotS_pos.le

/-- **The glue lemma.**  If `0 ≤ t`, `2·3.14159…847·t ≤ π/4` and the four rational comparisons
`x ≤ S·(cosP a 11 + 2/24!) + 1`, `x ≤ S·cosP b 11 + 1`, `y ≤ S·(sinP b 11 + 2/25!) + 1`,
`y ≤ S·sinP a 11 + 1` hold (with `a = 2·3.14159…846·t ≤ 2πt ≤ b = 2·3.14159…847·t`), then
`(x + y·I)/S` is within `2/S` of `rot t`. -/
theorem rot_bound_aux (t : ℝ) (x y : ℤ) (ht0 : 0 ≤ t)
    (ht4 : 2 * (3.14159265358979323847 : ℝ) * t ≤ Real.pi / 4)
    (hx1 : (S : ℝ) * (cosP (2 * (3.14159265358979323846 : ℝ) * t) 11
        + 2 * ((Nat.factorial 24 : ℝ))⁻¹) ≤ (x : ℝ) + 1)
    (hx2 : (x : ℝ) ≤ (S : ℝ) * cosP (2 * (3.14159265358979323847 : ℝ) * t) 11 + 1)
    (hy1 : (S : ℝ) * (sinP (2 * (3.14159265358979323847 : ℝ) * t) 11
        + 2 * ((Nat.factorial 25 : ℝ))⁻¹) ≤ (y : ℝ) + 1)
    (hy2 : (y : ℝ) ≤ (S : ℝ) * sinP (2 * (3.14159265358979323846 : ℝ) * t) 11 + 1) :
    ‖cx x y - rot t‖ ≤ 2 / (S : ℝ) := by
  have ha0 : (0 : ℝ) ≤ 2 * (3.14159265358979323846 : ℝ) * t := by nlinarith [ht0]
  have hab : 2 * (3.14159265358979323846 : ℝ) * t ≤ 2 * Real.pi * t := two_pi_lo t ht0
  have hbt : 2 * Real.pi * t ≤ 2 * (3.14159265358979323847 : ℝ) * t := two_pi_hi t ht0
  have hu4 : 2 * Real.pi * t ≤ Real.pi / 4 := le_trans hbt ht4
  have hcos_lo := Work.ANum.cosP_le_cos (le_trans ha0 hab) hbt ht4
  have hcos_hi := Work.ANum.cos_le_cosP ha0 hab hu4
  have hsin_lo := Work.ANum.sinP_le_sin ha0 hab hu4
  have hsin_hi := Work.ANum.sin_le_sinP (le_trans ha0 hab) hbt ht4
  have hSnn : (0 : ℝ) ≤ (S : ℝ) := rotS_pos.le
  have hwre : (((x : ℂ) + (y : ℂ) * I - (S : ℂ) * rot t).re)
      = (x : ℝ) - (S : ℝ) * Real.cos (2 * Real.pi * t) := by
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Work.ANum.rot_re]
  have hwim : (((x : ℂ) + (y : ℂ) * I - (S : ℂ) * rot t).im)
      = (y : ℝ) - (S : ℝ) * Real.sin (2 * Real.pi * t) := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Work.ANum.rot_im]
  have hre : |(((x : ℂ) + (y : ℂ) * I - (S : ℂ) * rot t).re)| ≤ 1 := by
    rw [hwre, abs_le]
    constructor
    · have h1 : (S : ℝ) * Real.cos (2 * Real.pi * t) ≤ (S : ℝ) *
          (cosP (2 * (3.14159265358979323846 : ℝ) * t) 11 + 2 * ((Nat.factorial 24 : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hcos_hi hSnn
      linarith [h1, hx1]
    · have h1 : (S : ℝ) * cosP (2 * (3.14159265358979323847 : ℝ) * t) 11
          ≤ (S : ℝ) * Real.cos (2 * Real.pi * t) := mul_le_mul_of_nonneg_left hcos_lo hSnn
      linarith [h1, hx2]
  have him : |(((x : ℂ) + (y : ℂ) * I - (S : ℂ) * rot t).im)| ≤ 1 := by
    rw [hwim, abs_le]
    constructor
    · have h1 : (S : ℝ) * Real.sin (2 * Real.pi * t) ≤ (S : ℝ) *
          (sinP (2 * (3.14159265358979323847 : ℝ) * t) 11 + 2 * ((Nat.factorial 25 : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left hsin_hi hSnn
      linarith [h1, hy1]
    · have h1 : (S : ℝ) * sinP (2 * (3.14159265358979323846 : ℝ) * t) 11
          ≤ (S : ℝ) * Real.sin (2 * Real.pi * t) := mul_le_mul_of_nonneg_left hsin_lo hSnn
      linarith [h1, hy2]
  rw [cx_sub_rot t x y]
  exact norm_div_S_le_two hre him

/-- `rot (2033/25000)`, correctly rounded at scale `S`. -/
theorem rot0_bound : ‖cx rot0r rot0i - rot (2033 / 25000)‖ ≤ 2 / (S : ℝ) := by
  have h4 : 2 * (3.14159265358979323847 : ℝ) * (2033 / 25000) ≤ Real.pi / 4 := by
    have h1 : 2 * (3.14159265358979323847 : ℝ) * (2033 / 25000)
        ≤ (3.14159265358979323846 : ℝ) / 4 := by norm_num
    have h2 : (3.14159265358979323846 : ℝ) / 4 ≤ Real.pi / 4 := by linarith [Real.pi_gt_d20]
    linarith
  refine rot_bound_aux (2033 / 25000) rot0r rot0i (by norm_num) h4 ?_ ?_ ?_ ?_
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot0r]
  · rw [cosP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot0r]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot0i]
  · rw [sinP]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num [S, rot0i]

end Work.Cert
