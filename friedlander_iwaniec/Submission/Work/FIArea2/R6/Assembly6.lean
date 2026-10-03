/-
# `FIArea2/R6/Assembly6.lean` — the geometric and logarithmic bookkeeping of (9.10)

The §9 aggregate `sec9Psum_le_of_Lsum_six` produces the bound

  `sec9Psum6 Pa β ≤ C ϑ⁻¹ τ² · (H²+1)(2R+1)² · (log(H+R+2))^{K}`,

`H = Hscale M N = M^{-1/4}N^{3/4}`, `R = radN Pa`.  To reach the right-hand side of (9.10),
`Cb ϑ⁻¹ τ² N² (log N)^{bFun η}`, one has to

* convert `√(M/N)·(H²+1)(2R+1)²` into `O(N²)` — `geom_le_six` (this is where the paper's
  `N²` comes from: `√(M/N)·H²·(2R+1)² = N·(2R+1)² ≍ N²`, and the leftover
  `√(M/N)(2R+1)² ≤ √(MN) ≤ N²` uses `M ≤ N³`, i.e. `MN ≤ x` (4.19) and `N > x^{1/4+η}` (4.6));
* convert `log(H+R+2)` into `2 log N` — `log_pow_le_six` (with `N ≥ 8`).
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `x < N⁴` and `M ≤ N³` -/

/-- **(4.6)+(4.19)**: `x < N⁴`, since `N > x^{1/4+η}`. -/
theorem x_lt_N_pow_four6 (Pa : Work.FITop.Params) : (Pa.x : ℝ) < Pa.N ^ (4 : ℕ) := by
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
    have h : (1 : ℕ) < Pa.x := Nat.lt_of_lt_of_le (by norm_num) Pa.hx
    exact_mod_cast h
  have hx0 : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hpos : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) := Real.rpow_pos_of_pos hx0 _
  have h3 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ (4 : ℕ) < Pa.N ^ (4 : ℕ) :=
    pow_lt_pow_left₀ Pa.hNlo hpos.le (by norm_num)
  have h4 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ (4 : ℕ)
      = (Pa.x : ℝ) ^ ((1 : ℝ) + 4 * Pa.η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have h6 : (1 : ℝ) < (1 : ℝ) + 4 * Pa.η := by linarith [Pa.hη]
  have h7 : (Pa.x : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) + 4 * Pa.η) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hx1 h6
    rwa [Real.rpow_one] at h
  rw [h4] at h3
  linarith

/-- **(4.6)+(4.19)**: `M ≤ N³`. -/
theorem M_le_N_cube6 (Pa : Work.FITop.Params) : Pa.M ≤ Pa.N ^ (3 : ℕ) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hkey : Pa.M * Pa.N < Pa.N ^ (3 : ℕ) * Pa.N := by
    calc Pa.M * Pa.N ≤ (Pa.x : ℝ) := Pa.hMNx
      _ < Pa.N ^ (4 : ℕ) := x_lt_N_pow_four6 Pa
      _ = Pa.N ^ (3 : ℕ) * Pa.N := by ring
  exact le_of_lt (lt_of_mul_lt_mul_right hkey hNpos.le)

/-! ## 2. The radius of the outer box -/

/-- `radN Pa ≤ 2√N + 3`. -/
theorem radN_toNat_le6 (Pa : Work.FITop.Params) :
    (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) ≤ 2 * Real.sqrt Pa.N + 3 := by
  have h1 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4 : ℝ) * Pa.N = (2 : ℝ) ^ 2 * Pa.N by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h2 : ((Work.FITop.radN Pa).toNat : ℕ) = Nat.ceil (Real.sqrt (4 * Pa.N)) := by
    unfold Work.FITop.radN
    exact Int.toNat_natCast _
  have h4 : ((Nat.ceil (Real.sqrt (4 * Pa.N)) : ℕ) : ℝ) < Real.sqrt (4 * Pa.N) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  rw [h1] at h4
  rw [h2, h1]
  linarith

/-! ## 3. The geometric conversion `√(M/N)(H²+1)(2R+1)² ≤ 128N²` -/

/-- **The geometric conversion of (9.10)**: with `H = M^{-1/4}N^{3/4}` and `R = radN Pa`,

  `√(M/N)·(H²+1)·(2R+1)² ≤ 128 N²`   for `N ≥ 4`.

Indeed `√(M/N)·H² = N` exactly, `√(M/N) ≤ N` (⟸ `M·N ≤ x < N⁴`) and `(2R+1)² ≤ 57N`. -/
theorem geom_le_six (Pa : Work.FITop.Params) (hN4 : 4 ≤ Pa.N) :
    Real.sqrt Pa.M / Real.sqrt Pa.N
        * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2 + 1)
        * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
      ≤ 128 * Pa.N ^ 2 := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hMpos : (0 : ℝ) < Pa.M := by linarith [Pa.hM1]
  have hsqrtNpos : (0 : ℝ) < Real.sqrt Pa.N := Real.sqrt_pos.mpr hNpos
  have hHsq : (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2
      = Pa.M ^ (-(1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) := by
    have hMm : (Pa.M ^ (-(1 : ℝ) / 4)) ^ 2 = Pa.M ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le]; norm_num
    have hNn : (Pa.N ^ ((3 : ℝ) / 4)) ^ 2 = Pa.N ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    rw [Work.FIPlan.Hscale, mul_pow, hMm, hNn]
  have hsc : Real.sqrt Pa.M / Real.sqrt Pa.N * (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2 = Pa.N := by
    rw [hHsq]
    have hsc1 : Real.sqrt Pa.M * Pa.M ^ (-(1 : ℝ) / 2) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMpos]; norm_num
    have hsc2 : Pa.N ^ ((3 : ℝ) / 2) / Real.sqrt Pa.N = Pa.N := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hNpos]; norm_num
    rw [div_mul_eq_mul_div, ← mul_assoc, hsc1, one_mul, hsc2]
  have hdiv : Real.sqrt Pa.M / Real.sqrt Pa.N ≤ Pa.N := by
    rw [div_le_iff₀ hsqrtNpos]
    have h2 : Real.sqrt Pa.M ≤ Real.sqrt (Pa.N ^ 3) := Real.sqrt_le_sqrt (M_le_N_cube6 Pa)
    have h3 : Real.sqrt (Pa.N ^ 3) = Pa.N * Real.sqrt Pa.N := by
      rw [show Pa.N ^ 3 = Pa.N ^ 2 * Pa.N by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hNpos.le]
    rwa [h3] at h2
  have hRnn : (0 : ℝ) ≤ 2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1 := by positivity
  have hR : (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 ≤ 57 * Pa.N := by
    have h1 := radN_toNat_le6 Pa
    have h2 : 2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1 ≤ 4 * Real.sqrt Pa.N + 7 := by
      linarith
    have h4 : (2 : ℝ) ≤ Real.sqrt Pa.N := by
      have h5 : (2 : ℝ) = Real.sqrt 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h5]
      exact Real.sqrt_le_sqrt hN4
    have h5 : 4 * Real.sqrt Pa.N + 7 ≤ (15 / 2) * Real.sqrt Pa.N := by nlinarith [h4]
    have h6 : (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
        ≤ ((15 / 2) * Real.sqrt Pa.N) ^ 2 := pow_le_pow_left₀ hRnn (le_trans h2 h5) 2
    have h7 : ((15 / 2) * Real.sqrt Pa.N) ^ 2 = (225 / 4) * Pa.N := by
      rw [mul_pow, Real.sq_sqrt hNpos.le]; norm_num
    rw [h7] at h6
    linarith
  have hRnn2 : (0 : ℝ) ≤ (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 := sq_nonneg _
  calc Real.sqrt Pa.M / Real.sqrt Pa.N
        * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2 + 1)
        * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2
      = (Real.sqrt Pa.M / Real.sqrt Pa.N * (Work.FIPlan.Hscale Pa.M Pa.N) ^ 2
          + Real.sqrt Pa.M / Real.sqrt Pa.N)
          * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 := by ring
    _ = (Pa.N + Real.sqrt Pa.M / Real.sqrt Pa.N)
          * (2 * (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 1) ^ 2 := by rw [hsc]
    _ ≤ (Pa.N + Pa.N) * (57 * Pa.N) := by
        apply mul_le_mul
        · linarith
        · exact hR
        · exact hRnn2
        · linarith
    _ ≤ 128 * Pa.N ^ 2 := by nlinarith [hNpos]

/-! ## 4. The logarithmic conversion -/

/-- **`(log(H+R+2))^E ≤ (log N)^{2E}`** for `N ≥ 8`: `H = M^{-1/4}N^{3/4} ≤ N` and `R ≤ 2√N+3`,
so `H+R+2 ≤ 8N`, and `log 8 ≤ log N` with `log N ≥ 2`. -/
theorem log_pow_le_six (Pa : Work.FITop.Params) (hN8 : 8 ≤ Pa.N) (E : ℕ) :
    (Real.log (Work.FIPlan.Hscale Pa.M Pa.N + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ E
      ≤ (Real.log Pa.N) ^ (2 * E) := by
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hN1 : (1 : ℝ) ≤ Pa.N := by linarith
  have hMpos : (0 : ℝ) < Pa.M := by linarith [Pa.hM1]
  have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := by
    rw [Work.FIPlan.Hscale]
    exact mul_pos (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hNpos _)
  have hRadnn : (0 : ℝ) ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by positivity
  have hH : Work.FIPlan.Hscale Pa.M Pa.N ≤ Pa.N := by
    rw [Work.FIPlan.Hscale]
    have h1 : Pa.M ^ (-(1 : ℝ) / 4) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos Pa.hM1
      norm_num
    have h2 : Pa.N ^ ((3 : ℝ) / 4) ≤ Pa.N := by
      have h3 : Pa.N ^ ((3 : ℝ) / 4) ≤ Pa.N ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        norm_num
      rwa [Real.rpow_one] at h3
    calc Pa.M ^ (-(1 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) ≤ 1 * Pa.N :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hNpos.le _) (by norm_num)
      _ = Pa.N := by ring
  have hRad : (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 ≤ 5 * Pa.N := by
    have h1 := radN_toNat_le6 Pa
    have hsqrt : Real.sqrt Pa.N ≤ Pa.N := by
      have h2 : Real.sqrt Pa.N ≤ Real.sqrt (Pa.N ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hN1])
      rwa [Real.sqrt_sq hNpos.le] at h2
    linarith
  have hargpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by linarith
  have hlog2 : (2 : ℝ) ≤ Real.log Pa.N := by
    have h8 : Real.log 8 ≤ Real.log Pa.N := Real.log_le_log (by norm_num) (by exact_mod_cast hN8)
    have h9 : (2 : ℝ) ≤ Real.log 8 := by
      have hlt : ((2 : ℝ) / 3) < Real.log 2 := by
        have hnum : ((2 : ℝ) / 3) < (6931471803 : ℝ) / 10000000000 := by norm_num
        have hd := Real.log_two_gt_d9
        rw [show (0.6931471803 : ℝ) = (6931471803 : ℝ) / 10000000000 by norm_num] at hd
        exact lt_trans hnum hd
      have h8' : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [h8']
      linarith
    linarith
  have hlogpos : (0 : ℝ) < Real.log Pa.N := by linarith
  have hmain : Real.log (Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2) ≤ 2 * Real.log Pa.N := by
    have h8N : Real.log (Work.FIPlan.Hscale Pa.M Pa.N
          + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2) ≤ Real.log (8 * Pa.N) := by
      apply Real.log_le_log hargpos
      linarith
    have hsplit : Real.log (8 * Pa.N) = Real.log 8 + Real.log Pa.N :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hlog8 : Real.log 8 ≤ Real.log Pa.N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN8)
    linarith
  have hargnn : (0 : ℝ) ≤ Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2) := by
    apply Real.log_nonneg
    linarith
  calc (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
          + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ E
      ≤ (2 * Real.log Pa.N) ^ E := pow_le_pow_left₀ hargnn hmain E
    _ = 2 ^ E * (Real.log Pa.N) ^ E := by rw [mul_pow]
    _ ≤ (Real.log Pa.N) ^ E * (Real.log Pa.N) ^ E := by
        have h : 2 ^ E ≤ (Real.log Pa.N) ^ E := pow_le_pow_left₀ (by norm_num) hlog2 E
        nlinarith [h, pow_nonneg hlogpos.le E]
    _ = (Real.log Pa.N) ^ (2 * E) := by rw [← pow_add, ← two_mul]

end

end Work.FIArea2.R6
