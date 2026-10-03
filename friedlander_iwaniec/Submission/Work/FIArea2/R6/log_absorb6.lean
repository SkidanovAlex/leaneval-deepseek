import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.Hscale_bounds

namespace Work.FIArea2.R6

/-- The box radius `radN Pa = ⌈√(4N)⌉₊` dominates `2√N`: the ceiling of a nonnegative real is at
least that real, and `√(4N) = 2√N`. -/
lemma radN_toNat_ge_sqrt (Pa : Work.FITop.Params) :
    2 * Real.sqrt Pa.N ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) := by
  have h4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    have hsq : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Pa.N, hsq]
  have hceil : Real.sqrt (4 * Pa.N) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hcast : (((Work.FITop.radN Pa).toNat : ℕ) : ℝ)
      = ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := by
    rw [show Work.FITop.radN Pa = ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℤ) from rfl,
      Int.toNat_natCast]
  rw [hcast, ← h4]
  exact hceil

/-- Absorption of a power of `log N + 2` into a power of the `(9.2)`-scale logarithm `log(H + R + 2)`
(with `R = radN Pa ≥ 2√N`): `(log N + 2)^KZ * B^KL ≤ 4^KZ * B^(KZ + KL + 4)`.

Indeed `H + R + 2 ≥ 2√N`, so `B ≥ log(2√N) = log 2 + (log N)/2`, hence
`4B ≥ 4 log 2 + 2 log N ≥ 2 + log N =: L` (as `log N ≥ 0` and `4 log 2 > 2`), and `B ≥ log 4 > 1`
since `H > 0` and `R ≥ 2`.  Then `L^KZ ≤ (4B)^KZ = 4^KZ B^KZ` and `B^(KZ+KL) ≤ B^(KZ+KL+4)`. -/
lemma log_absorb6 (Pa : Work.FITop.Params) (KZ KL : ℕ) :
    (Real.log Pa.N + 2) ^ KZ
      * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
          + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ KL
    ≤ 4 ^ KZ * (Real.log (Work.FIPlan.Hscale Pa.M Pa.N
          + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2)) ^ (KZ + KL + 4) := by
  set B : ℝ := Real.log (Work.FIPlan.Hscale Pa.M Pa.N
      + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2) with hBdef
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hHpos : (0 : ℝ) < Work.FIPlan.Hscale Pa.M Pa.N := Work.FIArea2.Hscale_pos Pa
  have hr : 2 * Real.sqrt Pa.N ≤ (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) :=
    radN_toNat_ge_sqrt Pa
  have harg : 2 * Real.sqrt Pa.N
      ≤ Work.FIPlan.Hscale Pa.M Pa.N + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by
    linarith
  have h2sN : 0 < 2 * Real.sqrt Pa.N := by
    have := Real.sqrt_pos_of_pos hNpos; linarith
  have hle1 : Real.log (2 * Real.sqrt Pa.N) ≤ B := by
    rw [hBdef]
    exact Real.log_le_log h2sN harg
  have hlog2 : Real.log (2 * Real.sqrt Pa.N) = Real.log 2 + Real.log Pa.N / 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.sqrt_pos_of_pos hNpos)),
      Real.log_sqrt hNpos.le]
  have hlogN0 : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hLB : Real.log Pa.N + 2 ≤ 4 * B := by
    have h := hle1
    rw [hlog2] at h
    nlinarith [h, Real.log_two_gt_d9, hlogN0]
  have hB1 : 1 ≤ B := by
    have h2 : (2 : ℝ) ≤ 2 * Real.sqrt Pa.N := by
      have := Real.one_le_sqrt.mpr hN1; linarith
    have harg4 : (4 : ℝ) ≤ Work.FIPlan.Hscale Pa.M Pa.N
        + (((Work.FITop.radN Pa).toNat : ℕ) : ℝ) + 2 := by linarith
    have hlog4 : Real.log 4 ≤ B := by
      rw [hBdef]
      exact Real.log_le_log (by norm_num) harg4
    have h14 : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      nlinarith [Real.exp_one_lt_three]
    linarith
  have hL0 : 0 ≤ Real.log Pa.N + 2 := by linarith
  have hBnn : 0 ≤ B := by linarith
  calc (Real.log Pa.N + 2) ^ KZ * B ^ KL
      ≤ (4 * B) ^ KZ * B ^ KL :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0 hLB KZ) (pow_nonneg hBnn KL)
    _ = 4 ^ KZ * (B ^ KZ * B ^ KL) := by rw [mul_pow]; ring
    _ = 4 ^ KZ * B ^ (KZ + KL) := by rw [pow_add]
    _ ≤ 4 ^ KZ * B ^ (KZ + KL + 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) KZ)
        exact pow_le_pow_right₀ hB1 (by omega)

end Work.FIArea2.R6
