import Mathlib
import Submission.Work.Haupt.qp_defs

/-!
# Convergence of the `n ≥ 0` part of the semi-finite sum

We prove that for `‖q‖ < 1` the series

`∑_{n≥0} q^{n(n-1)/2} z^n / (q^{m+1};q)_n`

converges (absolutely), for *every* `z : ℂ`.  The proof is the ratio test:
writing `f n = qhalf q n * z^n / qpNat (q^(m+1)) q n` we have the exact recursion

`f (n+1) = f n * (q^n z / (1 - q^{m+1+n}))`,

so `‖f (n+1)‖ = ‖f n‖ · ‖q^n z‖ / ‖1 - q^{m+1+n}‖`.  Since `‖q‖ < 1` we have
`‖q^n z‖ ≤ 1/4` and `‖q^{m+1+n}‖ ≤ 1/2` for all large `n`, whence
`‖1 - q^{m+1+n}‖ ≥ 1 - ‖q^{m+1+n}‖ ≥ 1/2` and therefore
`‖f (n+1)‖ ≤ (1/2) · ‖f n‖` eventually.  Mathlib's ratio test finishes the job.
-/

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-- The exact one-step recursion for the summand `q^{n(n-1)/2} z^n / (a;q)_n`.
It is valid without any non-vanishing hypothesis: when `(a;q)_n = 0` both
sides are `0` because then `(a;q)_{n+1} = 0` too. -/
lemma qhalf_qpNat_ratio (a q z : ℂ) (n : ℕ) :
    qhalf q (n + 1) * z ^ (n + 1) / qpNat a q (n + 1)
      = (qhalf q n * z ^ n / qpNat a q n) * (q ^ n * z / (1 - a * q ^ n)) := by
  rw [qhalf_succ, qpNat_succ, pow_succ]
  rw [div_mul_div_comm]
  congr 1
  ring

/-- For `‖q‖ < 1` the `n ≥ 0` part of the semi-finite sum converges, for every `z`.
(Indeed the summands decay faster than any geometric sequence: the ratio test gives
`‖f (n+1)‖ ≤ (1/2)‖f n‖` eventually.) -/
theorem sf_summable_nat {q z : ℂ} (hq : ‖q‖ < 1) (m : ℕ) :
    Summable fun n : ℕ => qhalf q n * z ^ n / qpNat (q ^ ((m : ℤ) + 1)) q n := by
  set a : ℂ := q ^ ((m : ℤ) + 1) with ha
  -- rewrite the (integer) exponent `m+1` as a natural exponent
  have haz : a = q ^ (m + 1) := by
    rw [ha, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  -- `‖q‖^n → 0`
  have hqpow : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq
  have hevz : ∀ᶠ n : ℕ in atTop, ‖q‖ ^ n * ‖z‖ ≤ 1 / 4 :=
    (hqpow.mul_const ‖z‖).eventually_le_const (by norm_num)
  have hevq : ∀ᶠ n : ℕ in atTop, ‖q‖ ^ n ≤ 1 / 2 :=
    hqpow.eventually_le_const (by norm_num)
  -- ratio test
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hevz, hevq] with n hnz hnq
  rw [qhalf_qpNat_ratio a q z n, norm_mul, norm_div, norm_div]
  -- `‖q^n z‖ ≤ 1/4`
  have hB : ‖q ^ n * z‖ ≤ 1 / 4 := by
    rw [norm_mul, norm_pow]
    exact hnz
  -- `‖1 - a q^n‖ ≥ 1/2`
  have hD : (1 : ℝ) / 2 ≤ ‖1 - a * q ^ n‖ := by
    have h1 : ‖a * q ^ n‖ ≤ 1 / 2 := by
      rw [haz, ← pow_add, norm_pow]
      calc ‖q‖ ^ (m + 1 + n) ≤ ‖q‖ ^ n :=
            pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega)
        _ ≤ 1 / 2 := hnq
    calc (1 : ℝ) / 2 = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - ‖a * q ^ n‖ := by linarith
      _ = ‖(1 : ℂ)‖ - ‖a * q ^ n‖ := by simp
      _ ≤ ‖1 - a * q ^ n‖ := norm_sub_norm_le _ _
  have hDpos : (0 : ℝ) < ‖1 - a * q ^ n‖ := by linarith
  have hBD : ‖q ^ n * z‖ / ‖1 - a * q ^ n‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hDpos]
    nlinarith [hB, hD]
  calc ‖qhalf q n * z ^ n‖ / ‖qpNat a q n‖ * (‖q ^ n * z‖ / ‖1 - a * q ^ n‖)
      ≤ ‖qhalf q n * z ^ n‖ / ‖qpNat a q n‖ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hBD (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 1 / 2 * (‖qhalf q n * z ^ n‖ / ‖qpNat a q n‖) := by ring

end Work.Haupt
