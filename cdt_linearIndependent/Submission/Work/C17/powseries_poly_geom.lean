/-
# Power series with polynomial × geometric growth are summable and holomorphic

For `k : ℕ → ℂ` whose norms grow at most like `(n+1)^4 · θ^n`, the series

`f(z) = ∑' n, k n * z^n`

converges on the disc `θ·‖z‖ < 1` and is holomorphic there.  The only analytic input
is the comparison test for series plus the standard convergence of `∑ (n+1)^4 r^n`
for `0 ≤ r < 1`; holomorphy comes from `Complex.differentiableOn_tsum_of_summable_norm`
with the majorant `C · (n+1)^4 · (θ R)^n` on the ball of radius `R`.
-/
import Mathlib

namespace Work.C17

open scoped BigOperators

set_option linter.unusedVariables false

/-- `∑ ((n:ℝ)+1)^4 r^n` converges for `0 ≤ r < 1`: compare with
`16·∑ n^4 r^n + 16·∑ r^n`, both summable, using `(n+1)^4 ≤ 16(n^4+1)`. -/
lemma summable_pow4_succ_mul_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * r ^ n) := by
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 4 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 hr
  have h2 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hg : Summable (fun n : ℕ => 16 * ((n : ℝ) ^ 4 * r ^ n) + 16 * r ^ n) :=
    ((h1.mul_left 16).add (h2.mul_left 16))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
  · exact mul_nonneg (by positivity) (pow_nonneg hr0 n)
  · have hrn : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
    have hb : ((n : ℝ) + 1) ^ 4 ≤ 16 * ((n : ℝ) ^ 4 + 1) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; norm_num
      · have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        have h2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
        calc ((n : ℝ) + 1) ^ 4 ≤ (2 * (n : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h2n 4
          _ = 16 * (n : ℝ) ^ 4 := by ring
          _ ≤ 16 * ((n : ℝ) ^ 4 + 1) := by nlinarith [(by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)]
    calc ((n : ℝ) + 1) ^ 4 * r ^ n
        ≤ (16 * ((n : ℝ) ^ 4 + 1)) * r ^ n := mul_le_mul_of_nonneg_right hb hrn
      _ = 16 * ((n : ℝ) ^ 4 * r ^ n) + 16 * r ^ n := by ring

/-- Summability of `∑ k n z^n` under the growth bound `‖k n‖ ≤ C (n+1)^4 θ^n`,
whenever `θ ‖z‖ < 1`. -/
lemma summable_of_growth (k : ℕ → ℂ) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hk : ∀ n : ℕ, ‖k n‖ ≤ C * ((n : ℝ) + 1) ^ 4 * θ ^ n)
    (z : ℂ) (hz : θ * ‖z‖ < 1) :
    Summable (fun n : ℕ => k n * z ^ n) := by
  have hr0 : 0 ≤ θ * ‖z‖ := mul_nonneg hθ (norm_nonneg z)
  have hsum : Summable (fun n : ℕ => C * (((n : ℝ) + 1) ^ 4 * (θ * ‖z‖) ^ n)) :=
    (summable_pow4_succ_mul_geometric (θ * ‖z‖) hr0 hz).mul_left C
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  calc ‖k n * z ^ n‖ = ‖k n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ (C * ((n : ℝ) + 1) ^ 4 * θ ^ n) * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (hk n) (pow_nonneg (norm_nonneg z) n)
    _ = C * (((n : ℝ) + 1) ^ 4 * (θ * ‖z‖) ^ n) := by rw [mul_pow]; ring

/-- Holomorphy of `z ↦ ∑' n, k n z^n` on the ball of radius `R` when `θ R < 1`. -/
lemma differentiableOn_of_growth (k : ℕ → ℂ) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hk : ∀ n : ℕ, ‖k n‖ ≤ C * ((n : ℝ) + 1) ^ 4 * θ ^ n)
    (R : ℝ) (hR : θ * R < 1) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, k n * z ^ n) (Metric.ball (0 : ℂ) R) := by
  rcases le_or_gt R 0 with hR0 | hR0
  · -- the ball is empty, so the majorant `0` suffices
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n : ℕ => fun w : ℂ => k n * w ^ n) (u := fun _ => (0 : ℝ))
      (U := Metric.ball (0 : ℂ) R) summable_zero ?_ Metric.isOpen_ball ?_
    · intro n; fun_prop
    · intro n w hw
      have hw' : ‖w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      exact absurd hw' (not_lt.mpr (le_trans hR0 (norm_nonneg w)))
  · have hr0 : 0 ≤ θ * R := mul_nonneg hθ hR0.le
    have hsum : Summable (fun n : ℕ => C * (((n : ℝ) + 1) ^ 4 * (θ * R) ^ n)) :=
      (summable_pow4_succ_mul_geometric (θ * R) hr0 hR).mul_left C
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n : ℕ => fun w : ℂ => k n * w ^ n)
      (u := fun n => C * (((n : ℝ) + 1) ^ 4 * (θ * R) ^ n)) (U := Metric.ball (0 : ℂ) R)
      hsum ?_ Metric.isOpen_ball ?_
    · intro n; fun_prop
    · intro n w hw
      have hwR : ‖w‖ ≤ R := by
        have : ‖w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        exact le_of_lt this
      calc ‖k n * w ^ n‖ = ‖k n‖ * ‖w‖ ^ n := by rw [norm_mul, norm_pow]
        _ ≤ (C * ((n : ℝ) + 1) ^ 4 * θ ^ n) * ‖w‖ ^ n :=
              mul_le_mul_of_nonneg_right (hk n) (pow_nonneg (norm_nonneg w) n)
        _ ≤ (C * ((n : ℝ) + 1) ^ 4 * θ ^ n) * R ^ n := by
              apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwR n)
              exact mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg hθ n)
        _ = C * (((n : ℝ) + 1) ^ 4 * (θ * R) ^ n) := by rw [mul_pow]; ring

theorem powseries_poly_geom (k : ℕ → ℂ) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hk : ∀ n : ℕ, ‖k n‖ ≤ C * ((n : ℝ) + 1) ^ 4 * θ ^ n) :
    (∀ z : ℂ, θ * ‖z‖ < 1 → Summable fun n : ℕ => k n * z ^ n) ∧
      (∀ R : ℝ, θ * R < 1 →
        DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, k n * z ^ n) (Metric.ball (0 : ℂ) R)) := by
  exact ⟨fun z hz => summable_of_growth k C θ hC hθ hk z hz,
    fun R hR => differentiableOn_of_growth k C θ hC hθ hk R hR⟩

end Work.C17
