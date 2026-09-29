import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.qcoeff

/-!
# Euler's `q`-exponential

The classical identity

`∏'_{n≥0} (1 + w q^n) = ∑'_{n≥0} q^{n(n-1)/2} w^n / (q;q)_n`

for `‖q‖ < 1` and arbitrary `w : ℂ`.  The right hand side is the `q`-exponential
`qexp q w = ∑' n, qcoeff q n * w^n`.

The proof is the standard one: both sides satisfy the same functional equation
`F w = (1 + w) * F (q * w)`; the series satisfies it by the coefficient recurrence
(`qcoeff_rec_add`), and the product is the limit of finite products, so the series
equals the limit of the products.
-/

open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000

namespace Work.Haupt

/-- Euler's `q`-exponential: `∑' n, q^{n(n-1)/2} w^n / (q;q)_n`. -/
noncomputable def qexp (q w : ℂ) : ℂ := ∑' n : ℕ, qcoeff q n * w ^ n

@[simp] lemma qexp_zero (q : ℂ) : qexp q 0 = 1 := by
  rw [qexp, tsum_eq_single 0]
  · simp
  · intro n hn
    rw [zero_pow hn, mul_zero]

/-- The summand of `qexp` is summable for every `w` when `‖q‖ < 1`. -/
lemma summable_qcoeff_mul_pow {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    Summable (fun n : ℕ => qcoeff q n * w ^ n) := by
  have hden : 0 < 1 - ‖q‖ := by linarith [norm_nonneg q, hq]
  have hqpow : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := (‖q‖ : ℝ)) (by simpa using hq)
    simpa using h
  have htend : Tendsto (fun n : ℕ => ‖w‖ * ‖q‖ ^ n) atTop (𝓝 0) := by
    simpa using hqpow.const_mul ‖w‖
  have hev : ∀ᶠ n : ℕ in atTop, ‖w‖ * ‖q‖ ^ n ≤ (1 - ‖q‖) / 2 :=
    ((tendsto_order.mp htend).2 ((1 - ‖q‖) / 2) (by linarith)).mono (fun n hn => hn.le)
  have hstep : ∀ n : ℕ, qcoeff q (n + 1) * w ^ (n + 1)
      = (qcoeff q n * w ^ n) * (q ^ n * w / (1 - q ^ (n + 1))) := by
    intro n
    rw [qcoeff_rec_div hq n]
    ring
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hev] with n hn
  have hX : ‖q ^ n * w / (1 - q ^ (n + 1))‖ ≤ 1 / 2 := by
    rw [norm_div, norm_mul, norm_pow]
    have h1 : (1 : ℝ) - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (n + 1)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (q ^ (n + 1))
      rw [norm_one] at h
      have h2 : ‖q ^ (n + 1)‖ ≤ ‖q‖ := by
        rw [norm_pow]
        simpa using pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega : 1 ≤ n + 1)
      linarith
    have hnum : 0 ≤ ‖q‖ ^ n * ‖w‖ := by positivity
    calc ‖q‖ ^ n * ‖w‖ / ‖(1 : ℂ) - q ^ (n + 1)‖ ≤ ‖q‖ ^ n * ‖w‖ / (1 - ‖q‖) :=
          div_le_div_of_nonneg_left hnum hden h1
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ hden]
          linarith [hn, mul_comm (‖q‖ ^ n) ‖w‖]
  rw [hstep n, norm_mul]
  calc ‖qcoeff q n * w ^ n‖ * ‖q ^ n * w / (1 - q ^ (n + 1))‖
      ≤ ‖qcoeff q n * w ^ n‖ * (1 / 2) := by gcongr
    _ = 1 / 2 * ‖qcoeff q n * w ^ n‖ := by ring

/-- The functional equation of Euler's `q`-exponential. -/
lemma qexp_rec {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    qexp q w = (1 + w) * qexp q (q * w) := by
  have hA : Summable (fun n : ℕ => qcoeff q n * w ^ n) := summable_qcoeff_mul_pow hq w
  have hB : Summable (fun n : ℕ => qcoeff q n * (q * w) ^ n) := summable_qcoeff_mul_pow hq (q * w)
  have hW : Summable (fun n : ℕ => qcoeff q n * q ^ n * w ^ (n + 1)) := by
    refine (hB.mul_left w).congr (fun n => ?_)
    rw [mul_pow, pow_succ']
    ring
  have hB' : Summable (fun n : ℕ => qcoeff q (n + 1) * (q * w) ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hB
  have key : ∀ n : ℕ, qcoeff q (n + 1) * w ^ (n + 1)
      = qcoeff q (n + 1) * (q * w) ^ (n + 1) + qcoeff q n * q ^ n * w ^ (n + 1) := by
    intro n
    have h := qcoeff_rec_add hq n
    rw [mul_pow]
    nth_rewrite 1 [← h]
    ring
  have hsplit : (∑' n : ℕ, qcoeff q (n + 1) * w ^ (n + 1))
      = (∑' n : ℕ, qcoeff q (n + 1) * (q * w) ^ (n + 1))
        + ∑' n : ℕ, qcoeff q n * q ^ n * w ^ (n + 1) := by
    rw [tsum_congr key, Summable.tsum_add hB' hW]
  have hAdecomp : qexp q w = 1 + ∑' n : ℕ, qcoeff q (n + 1) * w ^ (n + 1) := by
    rw [qexp, Summable.tsum_eq_zero_add hA]
    simp
  have hBdecomp : qexp q (q * w) = 1 + ∑' n : ℕ, qcoeff q (n + 1) * (q * w) ^ (n + 1) := by
    rw [qexp, Summable.tsum_eq_zero_add hB]
    simp
  have hWsum : (∑' n : ℕ, qcoeff q n * q ^ n * w ^ (n + 1)) = w * qexp q (q * w) := by
    rw [qexp, ← Summable.tsum_mul_left w hB]
    refine tsum_congr (fun n => ?_)
    rw [mul_pow, pow_succ']
    ring
  rw [hAdecomp, hsplit, hWsum, hBdecomp]
  ring

/-- The tail estimate for `qexp`: `‖qexp q x - 1‖ ≤ C ‖x‖` for `‖x‖ ≤ 1`. -/
lemma qexp_norm_sub_one_le {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖qexp q x - 1‖ ≤ (∑' n : ℕ, ‖qcoeff q (n + 1)‖) * ‖x‖ := by
  have hS : Summable (fun n : ℕ => qcoeff q n * x ^ n) := summable_qcoeff_mul_pow hq x
  have hs : Summable (fun n : ℕ => ‖qcoeff q n‖) := by
    have h := (summable_qcoeff_mul_pow hq 1).norm
    simpa using h
  have h1 : Summable (fun n : ℕ => ‖qcoeff q (n + 1)‖) := (summable_nat_add_iff 1).mpr hs
  have hS' : Summable (fun n : ℕ => qcoeff q (n + 1) * x ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hS
  have hsub : qexp q x - 1 = ∑' n : ℕ, qcoeff q (n + 1) * x ^ (n + 1) := by
    rw [qexp, Summable.tsum_eq_zero_add hS]
    simp
  rw [hsub]
  have h2 : Summable (fun n : ℕ => ‖qcoeff q (n + 1) * x ^ (n + 1)‖) := hS'.norm
  refine (norm_tsum_le_tsum_norm h2).trans ?_
  rw [← Summable.tsum_mul_right ‖x‖ h1]
  refine Summable.tsum_le_tsum (fun n => ?_) h2 (h1.mul_right ‖x‖)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simpa using pow_le_pow_of_le_one (norm_nonneg x) hx (by omega : 1 ≤ n + 1)

/-- `qexp q` is continuous at `0`, with value `1`. -/
lemma qexp_tendsto_zero {q : ℂ} (hq : ‖q‖ < 1) : Tendsto (qexp q) (𝓝 0) (𝓝 1) := by
  have hb : Tendsto (fun x : ℂ => (∑' n : ℕ, ‖qcoeff q (n + 1)‖) * ‖x‖) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℂ => ‖x‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : ℂ)
    simpa using h1.const_mul (∑' n : ℕ, ‖qcoeff q (n + 1)‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards with x using norm_nonneg _
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with x hx
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact qexp_norm_sub_one_le hq x hx.le

/-- Iterating the functional equation: `qexp q w` equals a finite product times the
`qexp` at `q^N w`. -/
lemma qexp_iterate {q w : ℂ} (hq : ‖q‖ < 1) (N : ℕ) :
    qexp q w = (∏ k ∈ Finset.range N, (1 + w * q ^ k)) * qexp q (q ^ N * w) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [ih, qexp_rec hq (q ^ n * w), Finset.prod_range_succ]
    have harg : q * (q ^ n * w) = q ^ (n + 1) * w := by
      rw [← mul_assoc, ← pow_succ']
    rw [harg]
    ring_nf

/-- **Euler's identity**: `∏'_{n≥0} (1 + w q^n) = ∑'_{n≥0} q^{n(n-1)/2} w^n/(q;q)_n`. -/
theorem euler_qexp {q : ℂ} (hq : ‖q‖ < 1) (w : ℂ) :
    ∏' n : ℕ, (1 + w * q ^ n) = ∑' n : ℕ, qhalf q n * w ^ n / qpNat q q n := by
  have hsum : Summable (fun n : ℕ => w * q ^ n) := (summable_geometric_of_norm_lt_one hq).mul_left w
  have hM : Multipliable (fun n : ℕ => 1 + w * q ^ n) := Complex.multipliable_one_add_of_summable hsum
  have hlim1 : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, (1 + w * q ^ k)) atTop
      (𝓝 (∏' n : ℕ, (1 + w * q ^ n))) := hM.tendsto_prod_tprod_nat
  have hlim2 : Tendsto (fun N : ℕ => qexp q (q ^ N * w)) atTop (𝓝 1) :=
    (qexp_tendsto_zero hq).comp (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const w)
  have hlim3 : Tendsto
      (fun N : ℕ => (∏ k ∈ Finset.range N, (1 + w * q ^ k)) * qexp q (q ^ N * w)) atTop
      (𝓝 ((∏' n : ℕ, (1 + w * q ^ n)) * 1)) := hlim1.mul hlim2
  have hlim4 : Tendsto
      (fun N : ℕ => (∏ k ∈ Finset.range N, (1 + w * q ^ k)) * qexp q (q ^ N * w)) atTop
      (𝓝 (qexp q w)) := by
    have heq : (fun N : ℕ => (∏ k ∈ Finset.range N, (1 + w * q ^ k)) * qexp q (q ^ N * w))
        = fun _ : ℕ => qexp q w := funext (fun N => (qexp_iterate hq N).symm)
    rw [heq]
    exact tendsto_const_nhds
  have huniq := tendsto_nhds_unique hlim3 hlim4
  rw [mul_one] at huniq
  rw [huniq, qexp]
  exact tsum_congr (fun n => qcoeff_mul_pow q w n)

end Work.Haupt
