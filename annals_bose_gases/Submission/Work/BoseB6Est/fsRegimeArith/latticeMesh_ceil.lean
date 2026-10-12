import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `latticeMesh_ceil`

For `0 < X ≤ 1/10` and the mode count `n = ⌈10⁶·X^{-1/4}⌉`, the lattice mesh error
`latticeMeshErr (8π) n` of the Bogoliubov zero-point mode-lattice comparison is
dominated by `X^{1/4}·156·log X⁻¹`.

The proof is the explicit Riemann estimate.  With the mesh `δ = meshD n = 2π/(n+1)`
and `m = n+1`:

* `n = ⌈10⁶X^{-1/4}⌉` gives `10⁶X^{-1/4} ≤ n < 10⁶X^{-1/4}+1`, hence `m > 10⁶X^{-1/4}`
  and, since `X^{-1/4} ≥ 1`, the upper bound `m ≤ 1000002·X^{-1/4}`;
* therefore `δ ≤ (2π/10⁶)X^{1/4}`, `1/m ≤ X^{1/4}/10⁶` and
  `log (gridD n) = 2 log m ≤ 2 log 1000002 + ½ log X⁻¹`;
* inserting the crude `π ≤ 3.15`, `√3 ≤ 2` into the four terms of `latticeMeshErr`
  leaves `latticeMeshErr (8π) n ≤ X^{1/4}·(246 + 2·log X⁻¹)`;
* and `log X⁻¹ ≥ log 10 ≥ 2`, so `246 + 2 log X⁻¹ ≤ 156 log X⁻¹`.
-/

namespace Work.BoseB6Est.fsRegimeArith

/-- `2 ≤ log 10`, from `exp 2 = (exp 1)² < 3² < 10`. -/
lemma log_ten_ge_two : (2 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)]
  have h : Real.exp 2 < 10 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  linarith

/-- `log 10 < 4`, from `exp 4 = (exp 1)⁴ > 2⁴ > 10`. -/
lemma log_ten_lt_four : Real.log 10 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10)]
  have h5 : (Real.exp 1) ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul (1 : ℝ) 4]; norm_num
  have h4 : (10 : ℝ) < (2 : ℝ) ^ 4 := by norm_num
  have h6 : (2 : ℝ) ^ 4 < (Real.exp 1) ^ 4 :=
    pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
  linarith [h5 ▸ h6]

/-- `log 1000002 ≤ 28`, from `1000002 < 10⁷` and `log 10 < 4`. -/
lemma log_1000002_le : Real.log 1000002 ≤ 28 := by
  have h1 : Real.log 1000002 ≤ Real.log ((10 : ℝ) ^ 7) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith [log_ten_lt_four]

theorem latticeMesh_ceil (X : ℝ) (hX0 : 0 < X) (hX1 : X ≤ 1 / 10) :
    Work.BoseB6.latticeMeshErr (8 * Real.pi) (Nat.ceil (10 ^ 6 * X ^ (-(1 / 4) : ℝ)))
      ≤ X ^ (1 / 4 : ℝ) * 156 * Real.log X⁻¹ := by
  set n : ℕ := Nat.ceil (10 ^ 6 * X ^ (-(1 / 4) : ℝ)) with hn
  set t : ℝ := X ^ (1 / 4 : ℝ) with ht
  set L : ℝ := Real.log X⁻¹ with hL
  -- elementary bounds on `t = X^{1/4}` and `L = log X⁻¹`
  have ht_pos : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos hX0 _
  have ht_nn : 0 ≤ t := ht_pos.le
  have ht_le_one : t ≤ 1 := by
    rw [ht]
    exact Real.rpow_le_one hX0.le (by linarith) (by norm_num)
  have hLge : 2 ≤ L := by
    rw [hL]
    have h10 : (10 : ℝ) ≤ X⁻¹ := by
      have h := one_div_le_one_div_of_le hX0 hX1
      norm_num at h
      exact h
    exact le_trans log_ten_ge_two (Real.log_le_log (by norm_num) h10)
  -- the ceiling `n` against the real number `10⁶·X^{-1/4}`
  have hXinv : X ^ (-(1 / 4) : ℝ) = t⁻¹ := by rw [ht, Real.rpow_neg hX0.le]
  have hp_pos : 0 < X ^ (-(1 / 4) : ℝ) := by rw [hXinv]; positivity
  have hn_ge : (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) ≤ (n : ℝ) := by
    rw [hn]; exact Nat.le_ceil _
  have hn_lt : (n : ℝ) < (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) + 1 := by
    rw [hn]; exact Nat.ceil_lt_add_one (mul_pos (by norm_num) hp_pos).le
  have hm_gt : (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) < (n : ℝ) + 1 := by linarith
  have hm_pos : 0 < (n : ℝ) + 1 := by linarith [hp_pos]
  have hp1 : 1 ≤ X ^ (-(1 / 4) : ℝ) := by
    rw [hXinv]
    exact (one_le_inv₀ ht_pos).mpr ht_le_one
  have hm_le : (n : ℝ) + 1 ≤ 1000002 * X ^ (-(1 / 4) : ℝ) := by
    have h2 : (10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ) + 2
        ≤ 1000002 * X ^ (-(1 / 4) : ℝ) := by
      nlinarith [hp1]
    linarith
  -- the mesh, the log of the grid size, and the reciprocal of the mode count
  have hmesh : Work.BoseB6.meshD n ≤ (2 * Real.pi / 10 ^ 6) * t := by
    have h1 : 2 * Real.pi / ((n : ℝ) + 1)
        ≤ 2 * Real.pi / ((10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hp_pos) hm_gt.le
    have heq : 2 * Real.pi / ((10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ))
        = (2 * Real.pi / 10 ^ 6) * t := by
      rw [hXinv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    rw [Work.BoseB6.meshD]
    rw [heq] at h1
    exact h1
  have hgrid : ((Work.BoseB6.gridD n : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
    simp only [Work.BoseB6.gridD]; push_cast; ring
  have hlogD : Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
      ≤ 2 * Real.log 1000002 + (1 / 2) * L := by
    have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (1000002 * X ^ (-(1 / 4) : ℝ)) :=
      Real.log_le_log hm_pos hm_le
    rw [Real.log_mul (by norm_num)
      ((Real.rpow_ne_zero hX0.le (by norm_num : (-(1 / 4) : ℝ) ≠ 0)).mpr hX0.ne')] at h1
    have h2 : Real.log (X ^ (-(1 / 4) : ℝ)) = (1 / 4) * L := by
      rw [Real.log_rpow hX0, hL, Real.log_inv]; ring
    rw [hgrid, Real.log_pow]
    push_cast
    linarith
  have hinv : 1 / ((n : ℝ) + 1) ≤ t / 10 ^ 6 := by
    have h1 : 1 / ((n : ℝ) + 1)
        ≤ 1 / ((10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ)) :=
      one_div_le_one_div_of_le (mul_pos (by norm_num) hp_pos) hm_gt.le
    have heq : 1 / ((10 : ℝ) ^ 6 * X ^ (-(1 / 4) : ℝ)) = t / 10 ^ 6 := by
      rw [hXinv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    rw [heq] at h1
    exact h1
  -- the mesh is at most `6.3·10⁻⁶·X^{1/4}`
  have hπ : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hδ0 : 0 ≤ Work.BoseB6.meshD n := by rw [Work.BoseB6.meshD]; positivity
  have hδ_le : Work.BoseB6.meshD n ≤ ((63 : ℝ) / 10 ^ 7) * t := by
    have h2 : 2 * Real.pi / 10 ^ 6 ≤ (63 : ℝ) / 10 ^ 7 := by nlinarith [hπ]
    calc Work.BoseB6.meshD n ≤ (2 * Real.pi / 10 ^ 6) * t := hmesh
      _ ≤ ((63 : ℝ) / 10 ^ 7) * t := mul_le_mul_of_nonneg_right h2 ht_nn
  have hδ3 : (Work.BoseB6.meshD n) ^ 3 ≤ ((63 : ℝ) / 10 ^ 7) ^ 3 * t := by
    have h1 : (Work.BoseB6.meshD n) ^ 3 ≤ (((63 : ℝ) / 10 ^ 7) * t) ^ 3 :=
      pow_le_pow_left₀ hδ0 hδ_le 3
    have h2 : (((63 : ℝ) / 10 ^ 7) * t) ^ 3 = ((63 : ℝ) / 10 ^ 7) ^ 3 * t ^ 3 := by ring
    have h3 : t ^ 3 ≤ t := by
      simpa using pow_le_pow_of_le_one ht_nn ht_le_one (show (1 : ℕ) ≤ 3 by norm_num)
    rw [h2] at h1
    have h4 : ((63 : ℝ) / 10 ^ 7) ^ 3 * t ^ 3 ≤ ((63 : ℝ) / 10 ^ 7) ^ 3 * t :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  -- the four terms of `latticeMeshErr (8π) n`
  have hT1 : 512 * Real.pi * Real.sqrt 3 * (8 * Real.pi) * (Work.BoseB6.meshD n) ^ 3
      ≤ 1 * t := by
    have hA : 512 * Real.pi * Real.sqrt 3 * (8 * Real.pi) * (Work.BoseB6.meshD n) ^ 3
        ≤ 512 * 3.15 * 2 * (8 * 3.15) * (((63 : ℝ) / 10 ^ 7) ^ 3 * t) := by
      gcongr
    have hB : 512 * 3.15 * 2 * (8 * 3.15) * (((63 : ℝ) / 10 ^ 7) ^ 3 * t) ≤ 1 * t := by
      have hc : 512 * 3.15 * 2 * (8 * 3.15) * ((63 : ℝ) / 10 ^ 7) ^ 3 ≤ 1 := by norm_num
      calc 512 * 3.15 * 2 * (8 * 3.15) * (((63 : ℝ) / 10 ^ 7) ^ 3 * t)
          = (512 * 3.15 * 2 * (8 * 3.15) * ((63 : ℝ) / 10 ^ 7) ^ 3) * t := by ring
        _ ≤ 1 * t := mul_le_mul_of_nonneg_right hc ht_nn
    linarith
  have hT2 : 520 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
      ≤ 20 * t := by
    have hA : 520 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
        ≤ 520 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t) := by
      gcongr
    have hB : 520 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t) ≤ 20 * t := by
      have hc : 520 * 3.15 * 2 * (8 * 3.15) ^ 2 * ((63 : ℝ) / 10 ^ 7) ≤ 20 := by norm_num
      calc 520 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t)
          = (520 * 3.15 * 2 * (8 * 3.15) ^ 2 * ((63 : ℝ) / 10 ^ 7)) * t := by ring
        _ ≤ 20 * t := mul_le_mul_of_nonneg_right hc ht_nn
    linarith
  have hT3 : 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
        * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
      ≤ 4 * t * (2 * Real.log 1000002 + (1 / 2) * L) := by
    have hA : 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
          * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
        ≤ 128 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t)
          * (2 * Real.log 1000002 + (1 / 2) * L) := by
      gcongr
    have hB : 128 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t)
          * (2 * Real.log 1000002 + (1 / 2) * L)
        ≤ 4 * t * (2 * Real.log 1000002 + (1 / 2) * L) := by
      have hc : 128 * 3.15 * 2 * (8 * 3.15) ^ 2 * ((63 : ℝ) / 10 ^ 7) ≤ 4 := by norm_num
      have h0 : 0 ≤ 2 * Real.log 1000002 + (1 / 2) * L := by
        have hp : 0 ≤ Real.log 1000002 := Real.log_nonneg (by norm_num)
        linarith [hLge, hp]
      calc 128 * 3.15 * 2 * (8 * 3.15) ^ 2 * (((63 : ℝ) / 10 ^ 7) * t)
            * (2 * Real.log 1000002 + (1 / 2) * L)
          = (128 * 3.15 * 2 * (8 * 3.15) ^ 2 * ((63 : ℝ) / 10 ^ 7) * t)
            * (2 * Real.log 1000002 + (1 / 2) * L) := by ring
        _ ≤ (4 * t) * (2 * Real.log 1000002 + (1 / 2) * L) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ht_nn) h0
    linarith
  have hT4 : 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1) ≤ 1 * t := by
    have hA : 4 * (8 * Real.pi) ^ 3 ≤ 4 * (8 * 3.15) ^ 3 := by
      gcongr
    have h1 : 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1) ≤ 4 * (8 * 3.15) ^ 3 * (t / 10 ^ 6) := by
      rw [show 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1)
          = 4 * (8 * Real.pi) ^ 3 * (1 / ((n : ℝ) + 1)) by ring]
      exact mul_le_mul hA hinv (by positivity) (by positivity)
    have hc : (4 : ℝ) * (8 * 3.15) ^ 3 / 10 ^ 6 ≤ 1 := by norm_num
    refine le_trans h1 ?_
    calc 4 * (8 * 3.15) ^ 3 * (t / 10 ^ 6)
        = ((4 : ℝ) * (8 * 3.15) ^ 3 / 10 ^ 6) * t := by ring
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right hc ht_nn
  -- the constant is absorbed by `156·log X⁻¹`
  have hT3b : 4 * t * (2 * Real.log 1000002 + (1 / 2) * L) ≤ 4 * t * (56 + (1 / 2) * L) := by
    have h56 : 2 * Real.log 1000002 ≤ 56 := by linarith [log_1000002_le]
    have h4t : 0 ≤ 4 * t := by linarith
    exact mul_le_mul_of_nonneg_left (by linarith) h4t
  have hkey : (246 : ℝ) + 2 * L ≤ 156 * L := by linarith [hLge]
  have hfinal : (1 : ℝ) * t + 20 * t + 4 * t * (56 + (1 / 2) * L) + 1 * t ≤ t * 156 * L := by
    have h : (1 : ℝ) * t + 20 * t + 4 * t * (56 + (1 / 2) * L) + 1 * t
        = t * (246 + 2 * L) := by ring
    rw [h]
    calc t * (246 + 2 * L) ≤ t * (156 * L) := mul_le_mul_of_nonneg_left hkey ht_nn
      _ = t * 156 * L := by ring
  rw [Work.BoseB6.latticeMeshErr]
  linarith [hT1, hT2, hT3, hT3b, hT4, hfinal]

end Work.BoseB6Est.fsRegimeArith
