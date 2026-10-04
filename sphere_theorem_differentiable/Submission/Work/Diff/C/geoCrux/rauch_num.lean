import Mathlib
import Submission.Work.Diff.C.geoCrux.rauch_B_mid
import Submission.Work.Diff.C.geoCrux.rauch_exp_seven_four
import Submission.Work.Diff.C.geoCrux.rauch_exp_rpow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The small-radius numerical step of the Rauch sphere-size assembly

`Work.Diff.C.geoCrux.rauch_sphere_map_core` (`geoCrux/rauch_sphere_map.lean`) splits on
`ρ ≤ √(c/4)`.  In the case `ρ ≤ √(c/4)` the modulus bound of the radial Jacobi field,
`‖Z ρ‖ ≤ 3 (ε₁ (1 + log (2/ρ))² + ρ²) ρ`, is already within the required additive error
`40 (√c + ε₁ π)`; this is the purely numerical estimate proved here:

`3 (ε₁ (1 + log (2/ρ)²) + ρ²) ρ ≤ 40 (√c + ε₁ π)`   for `0 < ρ ≤ √(c/4)`.

Route: `ρ ≤ √c / 2 ≤ 1/2`; `log x ≤ 2 √x` for `x > 0` (from `log y ≤ y - 1` at `y = √x`) gives
`log (2/ρ)² ≤ 8/ρ`, hence `ρ log (2/ρ)² ≤ 8`; the three summands are then bounded by
`3ε₁/2`, `24ε₁` and `(3/8) c √c ≤ 40 √c`.
-/

namespace Work.Diff.C.geoCrux

/-- `log x ≤ 2 √x` for `x > 0` (the only calculus input, from `log y ≤ y - 1`). -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hy : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hy
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]
    ring
  linarith [Real.sqrt_nonneg x]

/-- **The small-`ρ` numerical step** of `rauch_sphere_map_core`. -/
theorem rauch_num_small_rho {c ε₁ ρ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hρ : 0 < ρ) (hρc : ρ ≤ Real.sqrt (c / 4)) :
    3 * (ε₁ * (1 + (Real.log (2 / ρ)) ^ 2) + ρ ^ 2) * ρ
      ≤ 40 * (Real.sqrt c + ε₁ * Real.pi) := by
  have hc4 : (0 : ℝ) < c / 4 := by linarith
  have hs4 : Real.sqrt (c / 4) = Real.sqrt c / 2 := by
    rw [Real.sqrt_div' c (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
  have hρs : ρ ≤ Real.sqrt c / 2 := hs4 ▸ hρc
  have hsq : ρ ^ 2 ≤ c / 4 := by
    have h2 : (Real.sqrt c / 2) ^ 2 = c / 4 := by
      rw [div_pow, Real.sq_sqrt hc.le]
      norm_num
    rw [← h2]
    exact pow_le_pow_left₀ hρ.le hρs 2
  have hρhalf : ρ ≤ 1 / 2 := by
    have h1 : Real.sqrt c ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    linarith
  -- the logarithmic term
  have hpos : 0 < 2 / ρ := by positivity
  have hlog : Real.log (2 / ρ) ≤ 2 * Real.sqrt (2 / ρ) := log_le_two_sqrt hpos
  have hlog0 : 0 ≤ Real.log (2 / ρ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hρ]
    linarith
  have hsq2 : (Real.log (2 / ρ)) ^ 2 ≤ 8 / ρ := by
    have h2 : (Real.log (2 / ρ)) ^ 2 ≤ (2 * Real.sqrt (2 / ρ)) ^ 2 := by
      apply pow_le_pow_left₀ hlog0
      exact hlog
    have h3 : (2 * Real.sqrt (2 / ρ)) ^ 2 = 8 / ρ := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
      ring
    linarith [h2, h3.le, h3.ge]
  have hρlog : ρ * (Real.log (2 / ρ)) ^ 2 ≤ 8 := by
    have h := mul_le_mul_of_nonneg_left hsq2 hρ.le
    rw [mul_div_cancel₀ _ hρ.ne'] at h
    linarith
  -- assemble the three summands
  have h1 : 3 * ε₁ * ρ ≤ 3 * ε₁ * (1 / 2) := by
    have := mul_le_mul_of_nonneg_left hρhalf (by positivity : (0 : ℝ) ≤ 3 * ε₁)
    linarith
  have h2 : 3 * ε₁ * (ρ * (Real.log (2 / ρ)) ^ 2) ≤ 3 * ε₁ * 8 :=
    mul_le_mul_of_nonneg_left hρlog (by positivity : (0 : ℝ) ≤ 3 * ε₁)
  have h3 : 3 * ρ ^ 3 ≤ (3 / 8) * c * Real.sqrt c := by
    have h4 : 3 * (ρ * ρ ^ 2) ≤ 3 * (Real.sqrt c / 2 * (c / 4)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul hρs hsq (by positivity) (by positivity)
    have h5 : Real.sqrt c / 2 * (c / 4) = (1 / 8) * c * Real.sqrt c := by ring
    rw [← pow_succ' ρ 2] at h4
    simp only [pow_succ'] at h4 ⊢
    rw [h5] at h4
    linarith [h4]
  have hmain : 3 * (ε₁ * (1 + (Real.log (2 / ρ)) ^ 2) + ρ ^ 2) * ρ
      = 3 * ε₁ * ρ + 3 * ε₁ * (ρ * (Real.log (2 / ρ)) ^ 2) + 3 * ρ ^ 3 := by ring
  have hε : (3 : ℝ) * ε₁ * (1 / 2) + 3 * ε₁ * 8 ≤ 40 * (ε₁ * Real.pi) := by
    nlinarith [Real.pi_gt_three, hε₁]
  have hc' : (3 / 8) * c * Real.sqrt c ≤ 40 * Real.sqrt c := by
    have h6 : (3 / 8) * c ≤ 40 := by linarith
    have := mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg c)
    linarith [this]
  have hsum : 3 * ε₁ * (1 / 2) + 3 * ε₁ * 8 + (3 / 8) * c * Real.sqrt c
      ≤ 40 * (ε₁ * Real.pi) + 40 * Real.sqrt c := by linarith
  rw [hmain]
  linarith

/-! ## The two `B`-constants of the Rauch chain (`rauch_B_large`, `rauch_B_tiny`)

`Work.Diff.C.geoCrux.rauch_B_large` / `rauch_B_tiny` (`geoCrux/rauch_B_large.lean`,
`geoCrux/rauch_B_tiny.lean`) are the numeric inputs of the *large-`t`* and *small-`t`* branches of
the Rauch/modulus comparison; both are pure real-analysis estimates.  Reproduced here (with `_alt`
names so that no file importing both copies clashes):

* `c ≥ 1/16`: the logarithms are bounded by `log 16` and `log 128`, and `ε₁ < c/(4π)`;
* `c ≤ 1/4`: `log x ≤ 2 √x` twice, giving `log (4/√c)² ≤ 16/√c` and
  `(c/4) log (8/c) ≤ (√8/2) √c`.
-/

/-- `log 16 < 2.78`. -/
lemma log16_lt : Real.log 16 < 2.78 := by
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

/-- `log 128 < 4.86`. -/
lemma log128_lt : Real.log 128 < 4.86 := by
  have h : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

/-- **The large-`c` branch**: `6 (ε₁ (1 + log (4/√c)²) + c/4) + (c/4) log (8/c) ≤ 7 c` for
`c ≥ 1/16`. -/
theorem rauch_B_large_alt {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (h16 : 1 / 16 ≤ c) :
    6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
      + (c / 4) * Real.log (8 / c) ≤ 7 * c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
  have hsc4 : (1 : ℝ) / 4 ≤ Real.sqrt c := by
    have h : ((1 : ℝ) / 4) ^ 2 ≤ c := by norm_num; linarith
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)]
    exact Real.sqrt_le_sqrt h
  -- `ε₁ < c/(4π) < c/12.5`
  have hε : ε₁ ≤ c / 12.5 := by
    have hden : (0 : ℝ) < 4 * Real.pi := by positivity
    have h1 : ε₁ < c / (4 * Real.pi) := by rw [lt_div_iff₀ hden]; linarith
    have h2 : c / (4 * Real.pi) ≤ c / 12.5 := by
      apply div_le_div_of_nonneg_left hc.le (by norm_num)
      nlinarith [Real.pi_gt_d20]
    linarith
  -- the logs
  have h4sc : 4 / Real.sqrt c ≤ 16 := by
    rw [div_le_iff₀ hsc]
    linarith [hsc4]
  have hlog1 : Real.log (4 / Real.sqrt c) ≤ Real.log 16 :=
    Real.log_le_log (by positivity) h4sc
  have hlog2 : Real.log (8 / c) ≤ Real.log 128 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hc]
    nlinarith [h16]
  have hsc2 : Real.sqrt c ≤ 1 / 2 := by
    have h2 : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show ((1 : ℝ) / 4) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [Real.sqrt_le_sqrt hc1, h2.le, h2.ge]
  have hone : 1 ≤ 4 / Real.sqrt c := by
    rw [le_div_iff₀ hsc]
    linarith
  have hL0 : 0 ≤ Real.log (4 / Real.sqrt c) := Real.log_nonneg hone

  have hLsq : (Real.log (4 / Real.sqrt c)) ^ 2 ≤ (Real.log 16) ^ 2 :=
    pow_le_pow_left₀ hL0 hlog1 2
  have hL2 : (Real.log (4 / Real.sqrt c)) ^ 2 ≤ 7.73 := by
    have h := log16_lt
    nlinarith [hLsq]
  have hlog2' : Real.log (8 / c) ≤ 4.86 := by linarith [hlog2, log128_lt]
  -- term-by-term assembly
  have t1 : 6 * ε₁ ≤ 6 * (c / 12.5) := by linarith
  have t2 : 6 * (ε₁ * (Real.log (4 / Real.sqrt c)) ^ 2) ≤ 6 * (ε₁ * 7.73) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hε₁) (by norm_num)
  have t3 : (c / 4) * Real.log (8 / c) ≤ (c / 4) * 4.86 :=
    mul_le_mul_of_nonneg_left hlog2' (by positivity)
  have key : 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
      + (c / 4) * Real.log (8 / c)
      ≤ 6 * (c / 12.5) + 6 * (ε₁ * 7.73) + 6 * (c / 4) + (c / 4) * 4.86 := by
    nlinarith [t1, t2, t3]
  have hA : 6 * (c / 12.5) = 0.48 * c := by ring
  have hB : 6 * (ε₁ * 7.73) ≤ 6 * ((c / 12.5) * 7.73) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_right hε (by norm_num)
  have hC : (c / 4) * 4.86 = 1.215 * c := by ring
  have hB2 : 6 * ((c / 12.5) * 7.73) = 3.7104 * c := by ring
  have key2 : 6 * (c / 12.5) + 6 * (ε₁ * 7.73) + 6 * (c / 4) + (c / 4) * 4.86 ≤ 7 * c := by
    rw [hA, hC] at *
    linarith [hB, hB2, hc.le]
  linarith

/-- **The small-`c` branch**: `6 (ε₁ (1 + log (4/√c)²) + c/4) + (c/4) log (8/c) ≤ 10.05 √c`
for `c ≤ 1/4`.

Proof: multiply the goal by `√c > 0` and use `log x ≤ 2 √x` twice:
`√c log (4/√c)² ≤ 16` and `√c log (8/c) ≤ 2 √8` (the second via `√c · √(8/c) = √8`).  The four
terms are then bounded by `0.2389 c`, `7.6433 c`, `0.75 c` and `1.4143 c`. -/
theorem rauch_B_tiny_alt {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) :
    6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
      + (c / 4) * Real.log (8 / c) ≤ 10.05 * Real.sqrt c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
  have hsc2 : Real.sqrt c ≤ 1 / 2 := by
    have h2 : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show ((1 : ℝ) / 4) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [Real.sqrt_le_sqrt hc1, h2.le, h2.ge]
  have hε : ε₁ ≤ c / 12.56 := by
    have h1 : ε₁ < c / (4 * Real.pi) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)]
      linarith
    have h2 : c / (4 * Real.pi) ≤ c / 12.56 := by
      apply div_le_div_of_nonneg_left hc.le (by norm_num)
      nlinarith [Real.pi_gt_d20]
    linarith
  -- (F1) `√c · log (4/√c)² ≤ 16`
  have hlog1 : Real.log (4 / Real.sqrt c) ≤ 2 * Real.sqrt (4 / Real.sqrt c) :=
    log_le_two_sqrt (by positivity)
  have hL0 : 0 ≤ Real.log (4 / Real.sqrt c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hsc]
    nlinarith [hsc2]
  have hF1 : Real.sqrt c * (Real.log (4 / Real.sqrt c)) ^ 2 ≤ 16 := by
    have h1 : (Real.log (4 / Real.sqrt c)) ^ 2 ≤ (2 * Real.sqrt (4 / Real.sqrt c)) ^ 2 :=
      pow_le_pow_left₀ hL0 hlog1 2
    have h2 : (2 * Real.sqrt (4 / Real.sqrt c)) ^ 2 = 16 / Real.sqrt c := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 / Real.sqrt c)]
      ring
    have h3 : Real.sqrt c * (16 / Real.sqrt c) = 16 := by field_simp
    have h4 : Real.sqrt c * (Real.log (4 / Real.sqrt c)) ^ 2
        ≤ Real.sqrt c * (16 / Real.sqrt c) :=
      mul_le_mul_of_nonneg_left (by rw [← h2]; exact h1) hsc.le
    linarith [h4, h3.le, h3.ge]
  -- (F2) `√c · log (8/c) ≤ 2 √8`
  have hlog8 : Real.log (8 / c) ≤ 2 * Real.sqrt (8 / c) := log_le_two_sqrt (by positivity)
  have hid : Real.sqrt c * Real.sqrt (8 / c) = Real.sqrt 8 := by
    rw [← Real.sqrt_mul hc.le]
    congr 1
    field_simp
  have hF2 : Real.sqrt c * Real.log (8 / c) ≤ 2 * Real.sqrt 8 := by
    have h1 : Real.sqrt c * Real.log (8 / c) ≤ Real.sqrt c * (2 * Real.sqrt (8 / c)) :=
      mul_le_mul_of_nonneg_left hlog8 hsc.le
    have h2 : Real.sqrt c * (2 * Real.sqrt (8 / c)) = 2 * Real.sqrt 8 := by
      rw [← hid]; ring
    linarith [h1, h2.le, h2.ge]
  have h8 : Real.sqrt 8 ≤ 2.8285 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.8285)]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- multiply by `√c`
  refine (mul_le_mul_iff_of_pos_right hsc).mp ?_
  have hsq : Real.sqrt c * Real.sqrt c = c := by
    rw [← pow_two, Real.sq_sqrt hc.le]
  have hrhs : 10.05 * Real.sqrt c * Real.sqrt c = 10.05 * c := by
    rw [mul_assoc, hsq]
  rw [hrhs]
  have e1 : 6 * ε₁ * Real.sqrt c ≤ 0.2389 * c := by
    have h : 6 * ε₁ ≤ 6 * (c / 12.56) := by linarith
    have h2 : 6 * ε₁ * Real.sqrt c ≤ (6 * (c / 12.56)) * (1 / 2) :=
      mul_le_mul h hsc2 (by positivity) (by positivity)
    have h3 : (6 * (c / 12.56)) * (1 / 2) ≤ 0.2389 * c := by
      have hnum : (6 * ((1 : ℝ) / 12.56)) * (1 / 2) ≤ 0.2389 := by
        rw [show (12.56 : ℝ) = 314 / 25 by norm_num,
          show (0.2389 : ℝ) = 2389 / 10000 by norm_num]
        norm_num
      have hc0 : 0 ≤ c := hc.le
      have h5 : (6 * (c / 12.56)) * (1 / 2) = ((6 * ((1 : ℝ) / 12.56)) * (1 / 2)) * c := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_right hnum hc0
    linarith [h2, h3]
  have e2 : 6 * (ε₁ * (Real.sqrt c * (Real.log (4 / Real.sqrt c)) ^ 2)) ≤ 7.6434 * c := by
    have h2 : ε₁ * (Real.sqrt c * (Real.log (4 / Real.sqrt c)) ^ 2) ≤ ε₁ * 16 :=
      mul_le_mul_of_nonneg_left hF1 hε₁
    have h3 : ε₁ * 16 ≤ (c / 12.56) * 16 := by
      have h4 := mul_le_mul_of_nonneg_right hε (by norm_num : (0 : ℝ) ≤ 16)
      linarith [h4]
    have h4 : 6 * ((c / 12.56) * 16) ≤ 7.6434 * c := by
      have hnum : 6 * (((1 : ℝ) / 12.56) * 16) ≤ 7.6434 := by
        rw [show (12.56 : ℝ) = 314 / 25 by norm_num,
          show (7.6434 : ℝ) = 38217 / 5000 by norm_num]
        norm_num
      have hc0 : 0 ≤ c := hc.le
      have h5 : 6 * ((c / 12.56) * 16) = (6 * (((1 : ℝ) / 12.56) * 16)) * c := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_right hnum hc0
    linarith [h2, h3, h4]
  have e3 : 1.5 * (c * Real.sqrt c) ≤ 0.75 * c := by
    have h : c * Real.sqrt c ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left hsc2 hc.le
    linarith
  have e4 : (c / 4) * (Real.sqrt c * Real.log (8 / c)) ≤ 1.4143 * c := by
    have h1 : (c / 4) * (Real.sqrt c * Real.log (8 / c)) ≤ (c / 4) * (2 * Real.sqrt 8) :=
      mul_le_mul_of_nonneg_left hF2 (by positivity)
    have h2 : (c / 4) * (2 * Real.sqrt 8) ≤ (c / 4) * (2 * 2.8285) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [h8]
    have h3 : (c / 4) * (2 * 2.8285) = 1.41425 * c := by ring
    linarith [h1, h2, h3.le, h3.ge]

  have hexp : (6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4)
      + (c / 4) * Real.log (8 / c)) * Real.sqrt c
      = 6 * ε₁ * Real.sqrt c
        + 6 * (ε₁ * (Real.sqrt c * (Real.log (4 / Real.sqrt c)) ^ 2))
        + 1.5 * (c * Real.sqrt c)
        + (c / 4) * (Real.sqrt c * Real.log (8 / c)) := by ring
  rw [hexp]
  linarith [e1, e2, e3, e4]

/-! ## The assembled arithmetic input `rauch_arith` (with the two `B`-bounds supplied here)

`Work.Diff.C.geoCrux.rauch_arith` (`geoCrux/rauch_arith.lean`) is the `harith` hypothesis of
`rauch_sphere_map_core` — the last step of `Work.Diff.C.geoCrux.rauch_sphere_map`.  Its proof calls
`rauch_B_large`, `rauch_B_mid` and `rauch_B_tiny`; the first and third are still `sorry` in the
workspace, while `rauch_B_large_alt` / `rauch_B_tiny_alt` above prove them.  For robustness the full
statement is reproduced here (same name `+_alt`), so that the chain can use it without editing any
other file.  The proof is the one from `geoCrux/rauch_arith.lean`, with the two `B`-bounds replaced
by the versions proved above. -/

theorem rauch_arith_alt {c ε₁ A R s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hA : A ≤ 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4))
    (hR : R ≤ 8 / c) (hR1 : 1 ≤ R) :
    Real.exp A * R ^ (c / 4) * s ≤ s + 40 * (Real.sqrt c + ε₁ * Real.pi) := by
  set B := 6 * (ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) + c / 4) + (c / 4) * Real.log (8 / c)
    with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ ε₁ * (1 + (Real.log (4 / Real.sqrt c)) ^ 2) := by positivity
    have h2 : 0 ≤ Real.log (8 / c) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hc]; linarith
    nlinarith
  have hK : Real.exp A * R ^ (c / 4) ≤ Real.exp B := by
    rw [hBdef]; exact rauch_exp_rpow_le hc hR hR1 hA
  have hfin : Real.exp B - 1 ≤ 40 * Real.sqrt c := by
    rcases le_or_gt (1 / 16 : ℝ) c with h16 | h16
    · have h7 : B ≤ 7 * c := by rw [hBdef]; exact rauch_B_large_alt hc hc1 hε₁ hnum2 h16
      have hB74 : B ≤ 7 / 4 := by linarith
      have hexp : Real.exp B ≤ 7 := le_trans (Real.exp_le_exp_of_le hB74) rauch_exp_seven_four
      have hs16 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hsqrt : (1 / 4 : ℝ) ≤ Real.sqrt c := by
        have := Real.sqrt_le_sqrt h16; rwa [hs16] at this
      linarith [Real.exp_pos B]
    · rcases le_or_gt (1 / 121 : ℝ) c with h121 | h121
      · have h12 : B ≤ 12 * c := by rw [hBdef]; exact rauch_B_mid hc hc1 hε₁ hnum2 h121
        have hB1 : B ≤ 1 := by linarith
        have habs : |Real.exp B - 1| ≤ 2 * B := by
          have h := Real.abs_exp_sub_one_le (show |B| ≤ 1 by rwa [abs_of_nonneg hBnn])
          rwa [abs_of_nonneg hBnn] at h
        have hle : Real.exp B - 1 ≤ 2 * B := le_trans (le_abs_self _) habs
        have hs121 : Real.sqrt (1 / 121 : ℝ) = 1 / 11 := by
          rw [show (1 / 121 : ℝ) = (1 / 11) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrt : (1 / 11 : ℝ) ≤ Real.sqrt c := by
          have := Real.sqrt_le_sqrt h121; rwa [hs121] at this
        linarith
      · have h10 : B ≤ 10.05 * Real.sqrt c := by
          rw [hBdef]; exact rauch_B_tiny_alt hc hc1 hε₁ hnum2
        have hs121 : Real.sqrt (1 / 121 : ℝ) = 1 / 11 := by
          rw [show (1 / 121 : ℝ) = (1 / 11) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hsqrt_l : Real.sqrt c ≤ 1 / 11 := by
          have := Real.sqrt_le_sqrt h121.le; rwa [hs121] at this
        have hB1 : B ≤ 1 := by nlinarith
        have habs : |Real.exp B - 1| ≤ 2 * B := by
          have h := Real.abs_exp_sub_one_le (show |B| ≤ 1 by rwa [abs_of_nonneg hBnn])
          rwa [abs_of_nonneg hBnn] at h
        have hle : Real.exp B - 1 ≤ 2 * B := le_trans (le_abs_self _) habs
        linarith
  have hKnn : 0 ≤ Real.exp A * R ^ (c / 4) := by positivity
  have hKs : Real.exp A * R ^ (c / 4) * s ≤ s + (Real.exp B - 1) := by
    rcases le_or_gt (Real.exp A * R ^ (c / 4)) 1 with h | h
    · have h1 : Real.exp A * R ^ (c / 4) * s ≤ s := by nlinarith
      have h2 : 0 ≤ Real.exp B - 1 := by have := Real.one_le_exp hBnn; linarith
      linarith
    · have h3 : Real.exp A * R ^ (c / 4) * s ≤ s + (Real.exp A * R ^ (c / 4) - 1) := by
        nlinarith
      linarith
  have hep : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
  linarith


end Work.Diff.C.geoCrux
