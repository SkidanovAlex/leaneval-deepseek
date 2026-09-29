import Mathlib
import Submission.Work.ALift.bridge

/-!
# Area ALift — term-by-term differentiation with a rate-`ρ` coefficient bound

Let `c : ℕ → ℂ` have coefficients dominated by `C * (k+1)^d * ρ^k` with `ρ > 1` (so the power
series has radius of convergence at least `1/ρ`).  Then for every `x` with `‖x‖ < 1/ρ` the function
`z ↦ ∑' k, c k * z^k` is complex differentiable at `x` with derivative the termwise-differentiated
series `∑' k, ((k:ℂ)+1) * c (k+1) * x^k`.

The proof is the generalisation of `Work.CLift.hasDerivAt_tsum_pow` (which treats `ρ = 3/2` and
`‖x‖ < 2/3`) to an arbitrary rate: choose `r` with `‖x‖ < r < 1/ρ` and dominate the termwise
derivatives on the disc `‖z‖ < r` by the summable majorant `C * r⁻¹ * 2^d * n^{d+1} * (ρr)^n`,
using `ρr < 1`.
-/

namespace Work.ALift

open scoped BigOperators

theorem hasDerivAt_tsum_pow_rate (c : ℕ → ℂ) (C ρ : ℝ) (hC : 0 ≤ C) (hρ : 1 < ρ) (d : ℕ)
    (hbound : ∀ k : ℕ, ‖c k‖ ≤ C * ((k : ℝ) + 1) ^ d * ρ ^ k) {x : ℂ} (hx : ‖x‖ < 1 / ρ) :
    HasDerivAt (fun z : ℂ => ∑' k : ℕ, c k * z ^ k)
      (∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * x ^ k) x := by
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  -- `((n:ℝ)+1)^d ≤ 2^d * (n:ℝ)^d` for `n ≥ 1`
  have hkey : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) + 1) ^ d ≤ (2:ℝ)^d * (n:ℝ)^d := by
    intro n hn1
    have h2n : (n:ℝ) + 1 ≤ 2 * (n:ℝ) := by
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      linarith
    calc ((n : ℝ) + 1) ^ d ≤ (2 * (n:ℝ)) ^ d := pow_le_pow_left₀ (by positivity) h2n d
      _ = (2:ℝ)^d * (n:ℝ)^d := by rw [mul_pow]
  -- the radius of the disc on which we dominate, strictly between `‖x‖` and `1/ρ`
  let r : ℝ := (‖x‖ + 1 / ρ) / 2
  have hxr : ‖x‖ < r := by
    show ‖x‖ < (‖x‖ + 1 / ρ) / 2
    linarith [norm_nonneg x]
  have hrr : r < 1 / ρ := by
    show (‖x‖ + 1 / ρ) / 2 < 1 / ρ
    linarith [norm_nonneg x]
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hrne : r ≠ 0 := ne_of_gt hr0
  let q : ℝ := ρ * r
  have hq0 : 0 ≤ q := by
    show 0 ≤ ρ * r
    exact mul_nonneg hρ0.le hr0.le
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    have hlt : ρ * r < ρ * (1 / ρ) := mul_lt_mul_of_pos_left hrr hρ0
    rwa [mul_one_div, div_self hρne] at hlt
  -- summable majorant
  have huQ : Summable (fun n : ℕ => (n : ℝ) ^ (d + 1) * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (d + 1) hq1
  have hu : Summable (fun n : ℕ => C * r⁻¹ * (2:ℝ) ^ d * (n : ℝ) ^ (d + 1) * q ^ n) := by
    refine (huQ.mul_left (C * r⁻¹ * (2:ℝ)^d)).congr (fun n => ?_)
    ring
  -- the algebraic identity expressing the majorant
  have hpow : ∀ n : ℕ, 1 ≤ n →
      C * ((2:ℝ)^d * (n:ℝ)^d) * ρ^n * ((n:ℝ) * r^(n-1))
        = C * r⁻¹ * (2:ℝ)^d * (n:ℝ)^(d+1) * q^n := by
    intro n hn1
    have hrn : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [pow_succ]
    have hqn : q ^ n = ρ ^ n * (r ^ (n - 1) * r) := by
      rw [show q = ρ * r from rfl, mul_pow, hrn]
    rw [hqn, pow_succ]
    field_simp
  -- uniform bound on the termwise derivatives on the disc of radius `r`
  have hbound' : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖c n * ((n : ℂ) * y ^ (n - 1))‖ ≤ C * r⁻¹ * (2:ℝ)^d * (n : ℝ) ^ (d + 1) * q ^ n := by
    intro n y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [zero_pow (Nat.succ_ne_zero d)]
    · have hn1 : 1 ≤ n := hn
      have hyn : ‖y‖ ^ (n - 1) ≤ r ^ (n - 1) :=
        pow_le_pow_left₀ (norm_nonneg y) hy.le (n - 1)
      calc ‖c n * ((n : ℂ) * y ^ (n - 1))‖
          = ‖c n‖ * ((n:ℝ) * ‖y‖^(n-1)) := by
            rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
        _ ≤ (C * ((n:ℝ)+1)^d * ρ^n) * ((n:ℝ) * r^(n-1)) :=
            mul_le_mul (hbound n) (mul_le_mul_of_nonneg_left hyn (by positivity))
              (by positivity) (by positivity)
        _ ≤ (C * ((2:ℝ)^d * (n:ℝ)^d) * ρ^n) * ((n:ℝ) * r^(n-1)) := by
            gcongr
            exact hkey n hn1
        _ = C * r⁻¹ * (2:ℝ)^d * (n:ℝ)^(d+1) * q^n := hpow n hn1
  have hxball : x ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hxr
  -- term-by-term differentiation on the disc
  have hderiv : HasDerivAt (fun z : ℂ => ∑' k : ℕ, c k * z ^ k)
      (∑' k : ℕ, c k * ((k : ℂ) * x ^ (k - 1))) x := by
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0:ℂ) r) (y₀ := 0)
      (u := fun n : ℕ => C * r⁻¹ * (2:ℝ) ^ d * (n : ℝ) ^ (d + 1) * q ^ n)
      hu Metric.isOpen_ball Metric.isPreconnected_ball ?_ hbound' ?_ ?_ hxball
    · intro n y _
      exact (hasDerivAt_pow n y).const_mul (c n)
    · simpa using hr0
    · refine summable_of_ne_finset_zero (s := {0}) ?_
      intro n hn
      simp only [Finset.mem_singleton] at hn
      rw [zero_pow hn, mul_zero]
  -- summability of the derivative series at `x`, needed for the reindexing
  have hf : Summable fun n : ℕ => c n * ((n : ℂ) * x ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hbound' n x hxball)
  -- reindex the derivative series
  have h2 : (∑' k : ℕ, c k * ((k : ℂ) * x ^ (k - 1))) =
      ∑' k : ℕ, ((k : ℂ) + 1) * c (k + 1) * x ^ k := by
    rw [Work.CLift.tsum_succ_of_zero hf (by simp)]
    apply tsum_congr
    intro n
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  simpa only [h2] using hderiv

end Work.ALift
