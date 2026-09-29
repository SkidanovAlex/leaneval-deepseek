import Mathlib
import Submission.Work.CPull.tsum_mul_pow_pred
import Submission.Work.CPull.summable_norm_mul_pow_pred

namespace Work.CPull

/-- If `∑ ‖aₙ‖ n sⁿ` converges with `s > 0`, then the power series `∑ aₙ zⁿ` is complex
differentiable at every `w` with `‖w‖ < s`, with derivative the termwise-differentiated series
`∑ (n+1) aₙ₊₁ wⁿ`. -/
theorem powSeries_hasDerivAt_of_majorant {a : ℕ → ℂ} {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * n * s ^ n)) (w : ℂ) (hw : ‖w‖ < s) :
    HasDerivAt (fun z : ℂ => ∑' n : ℕ, a n * z ^ n)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * w ^ n) w := by
  -- A radius `r` strictly between `‖w‖` and `s`; the derivative series is uniformly dominated
  -- on the disc `‖z‖ < r` by `u n = ‖a n‖ * n * rⁿ⁻¹`.
  set r : ℝ := (‖w‖ + s) / 2 with hrdef
  have hwltr : ‖w‖ < r := by rw [hrdef]; linarith
  have hrpos : 0 < r := by rw [hrdef]; linarith [norm_nonneg w]
  have hrnonneg : 0 ≤ r := hrpos.le
  have hrlt : r < s := by rw [hrdef]; linarith
  have hu : Summable (fun n : ℕ => ‖a n‖ * (n : ℝ) * r ^ (n - 1)) :=
    summable_norm_mul_pow_pred hs hrnonneg hrlt hsum
  -- termwise differentiability of `z ↦ a n * zⁿ`
  have hg : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun y : ℂ => a n * y ^ n) ((n : ℂ) * a n * z ^ (n - 1)) z := by
    intro n z _
    simpa only [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_pow n z).const_mul (a n)
  -- uniform bound for the derivatives on the disc
  have hg' : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖(n : ℂ) * a n * z ^ (n - 1)‖ ≤ ‖a n‖ * (n : ℝ) * r ^ (n - 1) := by
    intro n z hz
    have hzr : ‖z‖ < r := by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
    rcases n with _ | k
    · simp
    · rw [Nat.add_sub_cancel, norm_mul, norm_mul, norm_natCast, norm_pow]
      have hpow : ‖z‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg z) hzr.le k
      calc ((k + 1 : ℕ) : ℝ) * ‖a (k + 1)‖ * ‖z‖ ^ k
          ≤ ((k + 1 : ℕ) : ℝ) * ‖a (k + 1)‖ * r ^ k :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ‖a (k + 1)‖ * ((k + 1 : ℕ) : ℝ) * r ^ k := by ring
  have hg0 : Summable (fun n : ℕ => a n * (0 : ℂ) ^ n) :=
    (hasSum_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])).summable
  have hwball : w ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwltr
  -- sum the derivatives: the series is differentiable on the disc with derivative the sum
  have hderiv := hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * z ^ n)
      (g' := fun n z => (n : ℂ) * a n * z ^ (n - 1)) hu Metric.isOpen_ball
      Metric.isPreconnected_ball hg hg' (y₀ := 0)
      (by rw [Metric.mem_ball, dist_self]; exact hrpos) hg0 hwball
  -- reindex `∑ n aₙ wⁿ⁻¹ = ∑ (n+1) aₙ₊₁ wⁿ`
  have hsum' : Summable (fun n : ℕ => (n : ℂ) * a n * w ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hg' n w hwball)
  rw [tsum_mul_pow_pred a w hsum'] at hderiv
  exact hderiv

end Work.CPull
