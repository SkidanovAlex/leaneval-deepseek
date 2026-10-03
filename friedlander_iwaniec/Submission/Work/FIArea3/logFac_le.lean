import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

namespace Work.FIArea3

/-! ## Elementary numeric inputs

The (7.10) log-factor is bounded below by the size of `N` through two numeric facts: `N` is large
enough that `N³ ≥ 11/5` (from `N > x^{1/4+η} ≥ 3^{1/4}`, (4.6)) and `θ = (log x)^{-A'}` is
*small*, because `A' ≥ 2^{20}` and `log x ≥ log 3 ≥ 17/16`.  We only need `θ ≤ 1/10`, which gives
`2(1 + θ) ≤ 11/5 ≤ N³`. -/

/-- `log 3 ≥ 17/16`: `3 = e · (3/e)` and `1 - 1/y ≤ log y` at `y = 3/e`, with `e < 2.7182818286`. -/
lemma log_three_ge : (17 : ℝ) / 16 ≤ Real.log 3 := by
  have hmul : Real.exp 1 * (3 / Real.exp 1) = 3 := by field_simp
  have hlog : Real.log 3 = 1 + Real.log (3 / Real.exp 1) := by
    conv_lhs => rw [← hmul]
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hinv : (3 / Real.exp 1)⁻¹ = Real.exp 1 / 3 := by field_simp
  have h1 : 1 - (Real.exp 1 / 3) ≤ Real.log (3 / Real.exp 1) := by
    simpa [hinv] using Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / Real.exp 1 by positivity)
  rw [hlog]
  linarith

/-- `11/5 ≤ (3^{1/4})³`: raise to the fourth power, `(11/5)^4 = 23.4256 < 27 = 3³`. -/
lemma three_quarter_ge : (11 : ℝ) / 5 ≤ ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 := by
  have hkey : (((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 3) ^ 4 = 27 := by
    rw [← pow_mul, ← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 4)) (3 * 4),
      ← Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    norm_num
  have hlt : ((11 : ℝ) / 5) ^ 4 < (((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 3) ^ 4 := by rw [hkey]; norm_num
  exact le_of_lt ((pow_lt_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp hlt)

/-- The smoothing parameter is tiny: `θ = (log x)^{-A'} ≤ 1/10`.

Indeed `log x ≥ log 3 ≥ 17/16 > 1` and `A' ≥ 2^{20} =: n`, so
`θ ≤ (log x)^{-n} = ((log x)^n)^{-1} ≤ 10^{-1}`, since `(log x)^n ≥ (17/16)^n ≥ 1 + n/16 ≥ 10`. -/
lemma theta_le_tenth (Pa : Work.FITop.Params) : Pa.θ ≤ (1 : ℝ) / 10 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hb : (17 : ℝ) / 16 ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [log_three_ge]
  have hlx : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by linarith
  set n : ℕ := 2 ^ 20 with hn
  have hA'lo : (n : ℝ) ≤ Pa.A' := by
    have h := Pa.hA'
    have hn' : (n : ℝ) = (2 : ℝ) ^ (20 : ℕ) := by rw [hn]; norm_num
    rw [← hn'] at h
    linarith [Pa.hA]
  have hbign : (10 : ℝ) ≤ (Real.log (Pa.x : ℝ)) ^ n := by
    have h2 : ((17 : ℝ) / 16) ^ n ≤ (Real.log (Pa.x : ℝ)) ^ n :=
      pow_le_pow_left₀ (by norm_num) hb n
    have h3 : 1 + (n : ℝ) * (1 / 16) ≤ (1 + 1 / 16 : ℝ) ^ n := one_add_mul_le_pow (by norm_num) n
    have h4 : ((1 : ℝ) + 1 / 16) = (17 : ℝ) / 16 := by norm_num
    rw [h4] at h3
    have h5 : (10 : ℝ) ≤ 1 + (n : ℝ) * (1 / 16) := by
      simp only [hn]; norm_num
    exact le_trans h5 (le_trans h3 h2)
  have hpos : (0 : ℝ) < (Real.log (Pa.x : ℝ)) ^ n := by
    have : (0 : ℝ) < Real.log (Pa.x : ℝ) := by linarith
    positivity
  have hstep : (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hlx (by linarith)
  have hconv : (Real.log (Pa.x : ℝ)) ^ (-(n : ℝ)) = ((Real.log (Pa.x : ℝ)) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ Real.log (Pa.x : ℝ)), Real.rpow_natCast]
  have hfin : ((Real.log (Pa.x : ℝ)) ^ n)⁻¹ ≤ (1 : ℝ) / 10 := by
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 1 / 10)]
    have : ((1 : ℝ) / 10)⁻¹ = 10 := by norm_num
    rw [this]
    exact hbign
  rw [Pa.hθ]
  exact hstep.trans (hconv.le.trans hfin)

/-- `2(1 + θ) ≤ N³`: `2(1 + θ) ≤ 2(1 + 1/10) = 11/5` by `theta_le_tenth`, and
`11/5 ≤ (3^{1/4})³ ≤ (x^{1/4})³ ≤ (x^{1/4+η})³ < N³` by (4.6) and `x ≥ 3`. -/
lemma two_mul_one_add_theta_le_cube (Pa : Work.FITop.Params) :
    2 * (1 + Pa.θ) ≤ Pa.N ^ (3 : ℕ) := by
  have h2 : 2 * (1 + Pa.θ) ≤ (11 : ℝ) / 5 := by linarith [theta_le_tenth Pa]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by linarith
  have hu : (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by norm_num) hx3 (by norm_num)
  have hcube : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 ≤ ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hu 3
  have hxpow : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
  have hcube2 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 ≤ ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hxpow 3
  have hcube3 : ((Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)) ^ 3 < Pa.N ^ 3 :=
    pow_lt_pow_left₀ Pa.hNlo (Real.rpow_nonneg (by positivity) _) (by norm_num)
  linarith [three_quarter_ge, hcube, hcube2, hcube3]

/-- `gnorm z = |z|²` is multiplicative. -/
lemma gnorm_mul' (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- For `z₁, z₂` in the polar box (5.14) at scale `N` the (7.10) log-factor
`logFac z₁ z₂ = log(2|z₁z₂|/|Δ(z₁,z₂)|)` is at most `4 log N`.  (`|Δ| = 0` gives `logFac = 0`, and
`|Δ| ≥ 1` gives `2√(n₁n₂)/|Δ| ≤ 2(1+θ)N ≤ N⁴`.) -/
theorem logFac_le {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    Work.FITop3.logFac z1 z2 ≤ 4 * Real.log Pa.N := by
  obtain ⟨-, hN1lo, hN1hi, -, -⟩ := h1
  obtain ⟨-, hN2lo, hN2hi, -, -⟩ := h2
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hlogN : 0 ≤ Real.log Pa.N := Real.log_nonneg hN1
  have hg1pos : (0 : ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by linarith
  -- `√(n₁n₂) ≤ (1+θ)N`
  have hsqrt : Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) ≤ (1 + Pa.θ) * Pa.N := by
    rw [Real.sqrt_le_left (by nlinarith [Pa.hθ0, hN1])]
    rw [gnorm_mul', Nat.cast_mul]
    nlinarith [hN1hi, hN2hi, Pa.hθ0, hN1]
  rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
  · -- `|Δ| = 0`: the logarithm is `log 0 = 0`
    have hz : Work.FITop3.logFac z1 z2 = 0 := by
      unfold Work.FITop3.logFac
      rw [h0]
      simp
    rw [hz]; linarith
  · -- `|Δ| ≥ 1`
    have hΔ1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hgpos : (0 : ℝ) < ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
      simp only [gnorm_mul', Nat.cast_mul]
      nlinarith [hg1pos, hN2lo, hNpos]
    have hargpos : (0 : ℝ) < 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / (Work.FIPlan.absDelta z1 z2 : ℝ) := by
      apply div_pos _ (by linarith)
      have : 0 < Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := Real.sqrt_pos.mpr hgpos
      linarith
    have hgle : 2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        / (Work.FIPlan.absDelta z1 z2 : ℝ) ≤ 2 * ((1 + Pa.θ) * Pa.N) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hsqrt, Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))]
    -- `2(1+θ)N ≤ N⁴`
    have hN4 : 2 * ((1 + Pa.θ) * Pa.N) ≤ Pa.N ^ 4 := by
      have hN3 := two_mul_one_add_theta_le_cube Pa
      have h := mul_le_mul_of_nonneg_right hN3 (le_of_lt hNpos)
      calc 2 * ((1 + Pa.θ) * Pa.N) = (2 * (1 + Pa.θ)) * Pa.N := by ring
        _ ≤ Pa.N ^ 3 * Pa.N := h
        _ = Pa.N ^ 4 := by ring
    calc Work.FITop3.logFac z1 z2
        = Real.log (2 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
            / (Work.FIPlan.absDelta z1 z2 : ℝ)) := rfl
      _ ≤ Real.log (2 * ((1 + Pa.θ) * Pa.N)) := Real.log_le_log hargpos hgle
      _ ≤ Real.log (Pa.N ^ 4) := Real.log_le_log (by nlinarith [Pa.hθ0, hNpos]) hN4
      _ = 4 * Real.log Pa.N := by rw [Real.log_pow]; norm_num

end Work.FIArea3
