import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel

/-!
# The lower bound `ω ≥ (1/18)·L^4·√D` for the naive-colouring expectation

This module proves `Work.Deep.Sparse.ncp_omega_lower`: the arithmetic step which combines the
two saturation hypotheses of the concentration proof into the quantitative lower bound

`(1/10) (log (D+2))^4 √D ≤ (1/18) ω`,   `ω = ncpOmega G k D v`,

on the expectation of the class-sum statistic of the naive colouring procedure.

Writing `L = log (D+2)`, `N = |nonAdjPairs G v|`, `ω = (N/2)·(1/k)·((k-1)/k)^{2D}`, the two
saturation hypotheses read

* `hsp`  : `δ D^2/4 ≤ N/2` (the neighbourhood carries enough non-adjacent pairs),
* `hbig` : `10^6 L^8 ≤ δ^2 D` (which, squared and rooted, gives `10^3 L^4 √D ≤ δ D`),

and `hL : 44 ≤ L` is used only to place `D ≥ 43` (hence `k ≥ 22`), which is what the power
estimates below need.

The one genuinely two-sided estimate is the *correlated* bound

`(1/k)·((k-1)/k)^{2D} ≥ 1/(128 D)`   (`D ≤ 2k`, `k ≤ 2D`, `k ≥ 12`),

whose proof splits on `k ≤ D`.  The single analytic input is

`(1 - 1/k)^k ≥ exp (-12/11)`   (`k ≥ 12`),

which follows from `Real.one_sub_inv_le_log_of_pos` (`log (1-1/k) ≥ -1/(k-1)`) together with
`k/(k-1) ≤ 12/11`.  Raising it to the fourth (resp. second) power and using
`exp (48/11) ≤ 128` (resp. `exp (24/11) ≤ 64`) -- both instances of `log 2 > 0.6931`
(`Real.log_two_gt_d9`) -- gives `(1 - 1/k)^(4k) ≥ 1/128`, used when `k ≤ D`, and
`(1 - 1/k)^(2k) ≥ 1/64`, used when `D < k` together with `D/k ≥ 1/2`.

Everything else is the bookkeeping of `δ D/512 ≤ ω` and `921.6 · L^4 √D ≤ 1000 · L^4 √D ≤ δ D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The numeric inputs -/

/-- `1/128 ≤ exp (-48/11)`, i.e. `exp (48/11) ≤ 128`: from `log 128 = 7 log 2 > 7 · 0.6931`. -/
lemma one_div_128_le_exp_neg_48_div_11 : (1 / 128 : ℝ) ≤ Real.exp (-(48 / 11 : ℝ)) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 128)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have h2 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  rw [h2]
  linarith [Real.log_two_gt_d9]

/-- `1/64 ≤ exp (-24/11)`, i.e. `exp (24/11) ≤ 64`: from `log 64 = 6 log 2 > 6 · 0.6931`. -/
lemma one_div_64_le_exp_neg_24_div_11 : (1 / 64 : ℝ) ≤ Real.exp (-(24 / 11 : ℝ)) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 64)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [h2]
  linarith [Real.log_two_gt_d9]

/-- **The power lower bound.**  For `12 ≤ k`, `(1 - 1/k)^k ≥ exp (-12/11) ≥ 1/3`.

The exponential bound `k log (1-1/k) ≥ -12/11` is `log (1-1/k) ≥ -1/(k-1)` multiplied by `k`,
and `k/(k-1) ≤ 12/11` for `k ≥ 12`. -/
lemma exp_neg_le_one_sub_inv_pow {k : ℕ} (hk : 12 ≤ k) :
    Real.exp (-(12 / 11 : ℝ)) ≤ (1 - 1 / (k : ℝ)) ^ k := by
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hk2 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hbase : 0 < 1 - 1 / (k : ℝ) := by
    have h : 1 / (k : ℝ) < 1 := by rw [div_lt_one hkpos]; exact hk1
    linarith
  have hlog1 : 1 - (1 - 1 / (k : ℝ))⁻¹ ≤ Real.log (1 - 1 / (k : ℝ)) :=
    Real.one_sub_inv_le_log_of_pos hbase
  have hlog2 : 1 - (1 - 1 / (k : ℝ))⁻¹ = -(1 / ((k : ℝ) - 1)) := by
    field_simp
    ring
  have hmul : (k : ℝ) * (-(1 / ((k : ℝ) - 1))) ≤ (k : ℝ) * Real.log (1 - 1 / (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlog1, hlog2]) (Nat.cast_nonneg k)
  have hquot : (k : ℝ) * (1 / ((k : ℝ) - 1)) ≤ 12 / 11 := by
    rw [mul_one_div, div_le_iff₀ hk2]
    have hkR : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hlog : -(12 / 11 : ℝ) ≤ (k : ℝ) * Real.log (1 - 1 / (k : ℝ)) := by
    have heq : (k : ℝ) * (-(1 / ((k : ℝ) - 1))) = -((k : ℝ) * (1 / ((k : ℝ) - 1))) := by ring
    linarith [hmul, hquot, heq]
  calc Real.exp (-(12 / 11 : ℝ)) ≤ Real.exp ((k : ℝ) * Real.log (1 - 1 / (k : ℝ))) :=
        Real.exp_le_exp.mpr hlog
    _ = (1 - 1 / (k : ℝ)) ^ k := by rw [Real.exp_nat_mul, Real.exp_log hbase]

/-- `(1 - 1/k)^(4k) ≥ 1/128` for `k ≥ 12`. -/
lemma one_sub_inv_pow_four_ge {k : ℕ} (hk : 12 ≤ k) :
    (1 / 128 : ℝ) ≤ (1 - 1 / (k : ℝ)) ^ (4 * k) := by
  have hb := exp_neg_le_one_sub_inv_pow hk
  have h3 : (Real.exp (-(12 / 11 : ℝ))) ^ 4 ≤ ((1 - 1 / (k : ℝ)) ^ k) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hb 4
  have he : (Real.exp (-(12 / 11 : ℝ))) ^ 4 = Real.exp (-(48 / 11 : ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he, ← pow_mul, mul_comm k 4] at h3
  exact le_trans one_div_128_le_exp_neg_48_div_11 h3

/-- `(1 - 1/k)^(2k) ≥ 1/64` for `k ≥ 12`. -/
lemma one_sub_inv_pow_two_ge {k : ℕ} (hk : 12 ≤ k) :
    (1 / 64 : ℝ) ≤ (1 - 1 / (k : ℝ)) ^ (2 * k) := by
  have hb := exp_neg_le_one_sub_inv_pow hk
  have h3 : (Real.exp (-(12 / 11 : ℝ))) ^ 2 ≤ ((1 - 1 / (k : ℝ)) ^ k) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hb 2
  have he : (Real.exp (-(12 / 11 : ℝ))) ^ 2 = Real.exp (-(24 / 11 : ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he, ← pow_mul, mul_comm k 2] at h3
  exact le_trans one_div_64_le_exp_neg_24_div_11 h3

/-! ## 2. The correlated bound `(1/k)·((k-1)/k)^{2D} ≥ 1/(128 D)` -/

/-- **The correlated power bound.**  If `0 < D`, `D ≤ 2k`, `k ≤ 2D` and `12 ≤ k` then
`(1/k)·((k-1)/k)^(2D) ≥ 1/(128 D)`.

Split on `k ≤ D`: if `k ≤ D` then `1/k ≥ 1/D` while `2D ≤ 4k` gives
`((k-1)/k)^(2D) ≥ (1-1/k)^(4k) ≥ 1/128`; if `D < k` then `D/k ≥ 1/2` (as `k ≤ 2D`) while
`2D ≤ 2k` gives `((k-1)/k)^(2D) ≥ (1-1/k)^(2k) ≥ 1/64`. -/
lemma one_div_mul_pow_lower {k D : ℕ} (hD : 0 < D) (hDk : D ≤ 2 * k)
    (hkD : (k : ℝ) ≤ 2 * (D : ℝ)) (hk : 12 ≤ k) :
    (1 : ℝ) / (128 * (D : ℝ)) ≤ (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hrew : (((k : ℝ) - 1) / (k : ℝ)) = 1 - 1 / (k : ℝ) := by
    field_simp
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hbase1 : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    linarith
  rw [hrew]
  rcases le_or_gt k D with hkle | hklt
  · -- `k ≤ D`
    have hexp : 2 * D ≤ 4 * k := by omega
    have hmono : (1 - 1 / (k : ℝ)) ^ (4 * k) ≤ (1 - 1 / (k : ℝ)) ^ (2 * D) :=
      pow_le_pow_of_le_one hbase0 hbase1 hexp
    have hone : (1 : ℝ) / (D : ℝ) ≤ 1 / (k : ℝ) :=
      one_div_le_one_div_of_le hkpos (by exact_mod_cast hkle)
    calc (1 : ℝ) / (128 * (D : ℝ)) = (1 / (D : ℝ)) * (1 / 128) := by
          field_simp
        _ ≤ (1 / (k : ℝ)) * (1 - 1 / (k : ℝ)) ^ (2 * D) :=
          mul_le_mul hone (le_trans (one_sub_inv_pow_four_ge hk) hmono)
            (by norm_num) (by positivity)
  · -- `D < k`
    have hDle : D ≤ k := le_of_lt hklt
    have hexp : 2 * D ≤ 2 * k := by omega
    have hmono : (1 - 1 / (k : ℝ)) ^ (2 * k) ≤ (1 - 1 / (k : ℝ)) ^ (2 * D) :=
      pow_le_pow_of_le_one hbase0 hbase1 hexp
    have hhalf : (1 : ℝ) / 2 ≤ (D : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]
      linarith [hkD]
    have hinner : (1 / 2) * (1 / 64) ≤ (D : ℝ) / (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (2 * D) :=
      mul_le_mul hhalf (le_trans (one_sub_inv_pow_two_ge hk) hmono) (by norm_num) (by positivity)
    calc (1 : ℝ) / (128 * (D : ℝ)) = (1 / (D : ℝ)) * ((1 / 2) * (1 / 64)) := by
          field_simp
          ring
        _ ≤ (1 / (D : ℝ)) * ((D : ℝ) / (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (2 * D)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = (1 / (k : ℝ)) * (1 - 1 / (k : ℝ)) ^ (2 * D) := by
          field_simp

/-! ## 3. The main theorem -/

theorem ncp_omega_lower {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D) (v : V) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((nonAdjPairs G v).card : ℝ) / 2) (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) (hL : 44 ≤ ncpL D) : (1 / 10 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ) ≤ (1 / 18) * ncpOmega G k D v := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- `hL` as a statement about `log (D+2)`
  have hL' : 44 ≤ Real.log ((D : ℝ) + 2) := by simpa [ncpL] using hL
  -- `D ≥ 43`, hence `k ≥ 22 ≥ 12`
  have hexp44 : Real.exp 44 ≤ (D : ℝ) + 2 :=
    (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (D : ℝ) + 2)).mp hL'
  have hD43 : 43 ≤ D := by
    have h45 : (45 : ℝ) ≤ (D : ℝ) + 2 := by linarith [Real.add_one_le_exp 44, hexp44]
    have : (43 : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast this
  have hk12 : 12 ≤ k := by omega
  -- the correlated bound
  have hcrux : (1 : ℝ) / (128 * (D : ℝ)) ≤
      (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D) :=
    one_div_mul_pow_lower hD hDk hkD hk12
  -- `δ D²/4 ≤ N/2`
  have hN : δ * (D : ℝ) ^ 2 / 4 ≤ ((nonAdjPairs G v).card : ℝ) / 2 := by
    have := hsp; ring_nf at this ⊢; linarith
  -- `ω ≥ δ D/512`
  have hΩ : δ * (D : ℝ) / 512 ≤ ncpOmega G k D v := by
    have hΩval : ncpOmega G k D v
        = (((nonAdjPairs G v).card : ℝ) / 2)
          * ((1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) := rfl
    rw [hΩval]
    have h1 : (δ * (D : ℝ) ^ 2 / 4) * (1 / (128 * (D : ℝ)))
        ≤ (((nonAdjPairs G v).card : ℝ) / 2)
          * ((1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) :=
      mul_le_mul hN hcrux (by positivity) (by positivity)
    have h2 : (δ * (D : ℝ) ^ 2 / 4) * (1 / (128 * (D : ℝ))) = δ * (D : ℝ) / 512 := by
      field_simp
      ring
    rw [← h2]
    exact h1
  -- `δ D ≥ 10^3 L^4 √D`
  have hbig' : (10 : ℝ) ^ 3 * (ncpL D) ^ 4 * Real.sqrt (D : ℝ) ≤ δ * (D : ℝ) := by
    have hLnn : (0 : ℝ) ≤ (ncpL D) ^ 4 := by positivity
    have h1 : Real.sqrt ((10 : ℝ) ^ 6 * (ncpL D) ^ 8) ≤ Real.sqrt (δ ^ 2 * (D : ℝ)) :=
      Real.sqrt_le_sqrt hbig
    have h2 : Real.sqrt ((10 : ℝ) ^ 6 * (ncpL D) ^ 8) = (10 : ℝ) ^ 3 * (ncpL D) ^ 4 := by
      rw [show (10 : ℝ) ^ 6 * (ncpL D) ^ 8 = ((10 : ℝ) ^ 3 * (ncpL D) ^ 4) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h3 : Real.sqrt (δ ^ 2 * (D : ℝ)) = δ * Real.sqrt (D : ℝ) := by
      rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ0.le]
    rw [h2, h3] at h1
    have h4 : (10 : ℝ) ^ 3 * (ncpL D) ^ 4 * Real.sqrt (D : ℝ)
        ≤ (δ * Real.sqrt (D : ℝ)) * Real.sqrt (D : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    have h5 : (δ * Real.sqrt (D : ℝ)) * Real.sqrt (D : ℝ) = δ * (D : ℝ) := by
      rw [mul_assoc, ← sq, Real.sq_sqrt hDpos.le]
    linarith [h4, h5]
  -- final arithmetic
  have hXnn : (0 : ℝ) ≤ (ncpL D) ^ 4 * Real.sqrt (D : ℝ) := by positivity
  have hkey : 9216 * ((1 / 10 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ)) ≤ δ * (D : ℝ) := by
    nlinarith [hbig', hXnn]
  have hfin : (1 / 10 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ) ≤ δ * (D : ℝ) / 9216 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 9216)]
    linarith [hkey]
  calc (1 / 10 : ℝ) * (ncpL D) ^ 4 * Real.sqrt (D : ℝ) ≤ δ * (D : ℝ) / 9216 := hfin
    _ = (1 / 18) * (δ * (D : ℝ) / 512) := by ring
    _ ≤ (1 / 18) * ncpOmega G k D v := mul_le_mul_of_nonneg_left hΩ (by norm_num)

end Work.Deep.Sparse
