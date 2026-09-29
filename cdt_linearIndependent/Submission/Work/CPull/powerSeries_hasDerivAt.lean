import Mathlib
import Submission.Work.CPull.summable_geom_bound
import Submission.Work.CPull.tsum_mul_pow_pred

/-!
# Differentiability of a power series with coefficients in a geometric box

If `‖c n‖ ≤ C * (1 / 4) ^ n`, then the power series `f z = ∑' n, c n * z ^ n` is
absolutely convergent, together with its termwise-derivative series, on the disc
`‖z‖ < 4`, and `f` is complex differentiable there with derivative
`∑' n, ((n + 1 : ℕ) : ℂ) * c (n + 1) * z ^ n`.
-/

namespace Work.CPull

theorem powerSeries_hasDerivAt (c : ℕ → ℂ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (1 / 4 : ℝ) ^ n) :
    (∀ y : ℂ, ‖y‖ < 4 → Summable fun n : ℕ => c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 4 → Summable fun n : ℕ => (n : ℂ) * c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 4 → Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 4 → HasDerivAt (fun z : ℂ => ∑' n : ℕ, c n * z ^ n)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) y) := by
  have hC0 : (0 : ℝ) ≤ C := hC.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    have hq0 : 0 ≤ ‖y‖ / 4 := by positivity
    have hq1 : ‖y‖ / 4 < 1 := by linarith
    refine summable_geom_bound (K := C) hq0 hq1 (fun n => ?_)
    rw [norm_mul, norm_pow]
    have hq : (1 / 4 : ℝ) ^ n * ‖y‖ ^ n = (‖y‖ / 4) ^ n := by
      rw [← mul_pow]; congr 1; ring
    calc ‖c n‖ * ‖y‖ ^ n ≤ (C * (1 / 4 : ℝ) ^ n) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg y) n)
      _ = C * (‖y‖ / 4) ^ n := by rw [← hq]; ring
      _ = C * 1 * (‖y‖ / 4) ^ n := by ring
      _ ≤ C * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Nat.cast_nonneg n)) hC0)
            (pow_nonneg hq0 n)
  · intro y hy
    have hq0 : 0 ≤ ‖y‖ / 4 := by positivity
    have hq1 : ‖y‖ / 4 < 1 := by linarith
    refine summable_geom_bound (K := C) hq0 hq1 (fun n => ?_)
    rw [norm_mul, norm_mul, norm_natCast, norm_pow]
    have hq : (1 / 4 : ℝ) ^ n * ‖y‖ ^ n = (‖y‖ / 4) ^ n := by
      rw [← mul_pow]; congr 1; ring
    calc (n : ℝ) * ‖c n‖ * ‖y‖ ^ n ≤ (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb n) (Nat.cast_nonneg n))
            (pow_nonneg (norm_nonneg y) n)
      _ = C * (n : ℝ) * (‖y‖ / 4) ^ n := by rw [← hq]; ring
      _ ≤ C * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) hC0)
            (pow_nonneg hq0 n)
  · intro y hy
    have hq0 : 0 ≤ ‖y‖ / 4 := by positivity
    have hq1 : ‖y‖ / 4 < 1 := by linarith
    refine summable_geom_bound (K := C / 4) hq0 hq1 (fun n => ?_)
    rw [norm_mul, norm_mul, norm_natCast, norm_pow]
    push_cast
    have hp : (1 / 4 : ℝ) ^ (n + 1) = (1 / 4) * (1 / 4) ^ n := by rw [pow_succ]; ring
    have hq' : (1 / 4 : ℝ) ^ n * ‖y‖ ^ n = (‖y‖ / 4) ^ n := by
      rw [← mul_pow]; congr 1; ring
    have hq : (1 / 4 : ℝ) ^ (n + 1) * ‖y‖ ^ n = (1 / 4) * (‖y‖ / 4) ^ n := by
      rw [hp, mul_assoc, hq']
    calc ((n : ℝ) + 1) * ‖c (n + 1)‖ * ‖y‖ ^ n
        ≤ ((n : ℝ) + 1) * (C * (1 / 4 : ℝ) ^ (n + 1)) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb (n + 1)) (by positivity))
            (pow_nonneg (norm_nonneg y) n)
      _ = C * ((n : ℝ) + 1) * ((1 / 4 : ℝ) ^ (n + 1) * ‖y‖ ^ n) := by ring
      _ = C * ((n : ℝ) + 1) * ((1 / 4) * (‖y‖ / 4) ^ n) := by rw [hq]
      _ = (C / 4) * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n := by ring
  · intro y hy
    set r : ℝ := (‖y‖ + 4) / 2 with hrdef
    have hyltr : ‖y‖ < r := by rw [hrdef]; linarith
    have hrpos : 0 < r := by rw [hrdef]; linarith [norm_nonneg y]
    have hrge1 : 1 ≤ r := by rw [hrdef]; linarith [norm_nonneg y]
    set q : ℝ := r / 4 with hqdef
    have hq0 : 0 ≤ q := by rw [hqdef]; positivity
    have hq1 : q < 1 := by rw [hqdef]; linarith
    have hu : Summable (fun n : ℕ => C * ((n : ℝ) + 1) * q ^ n) :=
      summable_geom_bound hq0 hq1
        (fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])
    have hg : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun w : ℂ => c n * w ^ n) ((n : ℂ) * c n * z ^ (n - 1)) z := by
      intro n z _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_pow n z).const_mul (c n)
    have htb : y ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hyltr
    have hg0 : Summable (fun n : ℕ => c n * (0 : ℂ) ^ n) := by
      refine summable_geom_bound (K := C) (q := 0) le_rfl (by norm_num) (fun n => ?_)
      rw [norm_mul, norm_pow, norm_zero]
      rcases eq_or_ne n 0 with hn | hn
      · subst hn; simpa using hb 0
      · rw [zero_pow hn]; simp
    have hg' : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖(n : ℂ) * c n * z ^ (n - 1)‖ ≤ C * ((n : ℝ) + 1) * q ^ n := by
      intro n z hz
      have hzr : ‖z‖ < r := by
        rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp only [Nat.cast_zero, zero_mul, norm_zero]
        positivity
      · rw [norm_mul, norm_mul, norm_natCast, norm_pow]
        have hpow : ‖z‖ ^ (n - 1) ≤ r ^ (n - 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzr.le (n - 1)
        have hkey : (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * r ^ (n - 1)
            ≤ C * ((n : ℝ) + 1) * ((1 / 4 : ℝ) ^ n * r ^ n) := by
          have hA : 0 ≤ C * (1 / 4 : ℝ) ^ n * r ^ (n - 1) := by positivity
          have hnle : (n : ℝ) ≤ ((n : ℝ) + 1) * r := by
            nlinarith [hrge1, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
          have hrn : r ^ n = r ^ (n - 1) * r := by
            rcases n with _ | k
            · exact absurd hn (lt_irrefl 0)
            · rw [add_tsub_cancel_right, pow_succ]
          calc (n : ℝ) * (C * (1 / 4) ^ n) * r ^ (n - 1)
              = (n : ℝ) * (C * (1 / 4) ^ n * r ^ (n - 1)) := by ring
            _ ≤ (((n : ℝ) + 1) * r) * (C * (1 / 4) ^ n * r ^ (n - 1)) :=
                mul_le_mul_of_nonneg_right hnle hA
            _ = C * ((n : ℝ) + 1) * ((1 / 4 : ℝ) ^ n * r ^ n) := by rw [hrn]; ring
        calc (n : ℝ) * ‖c n‖ * ‖z‖ ^ (n - 1)
            ≤ (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * r ^ (n - 1) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hb n) (Nat.cast_nonneg n)) hpow
                (pow_nonneg (norm_nonneg z) (n - 1)) (by positivity)
          _ ≤ C * ((n : ℝ) + 1) * ((1 / 4 : ℝ) ^ n * r ^ n) := hkey
          _ = C * ((n : ℝ) + 1) * q ^ n := by
              have hq'' : (1 / 4 : ℝ) ^ n * r ^ n = q ^ n := by
                rw [hqdef, ← mul_pow]; congr 1; ring
              rw [hq'']
    have hderiv := hasDerivAt_tsum_of_isPreconnected (g := fun n z => c n * z ^ n)
        (g' := fun n z => (n : ℂ) * c n * z ^ (n - 1)) hu Metric.isOpen_ball
        Metric.isPreconnected_ball hg hg' (y₀ := 0)
        (by rw [Metric.mem_ball, dist_self]; exact hrpos) hg0 htb
    have hf'sum : Summable (fun n : ℕ => (n : ℂ) * c n * y ^ (n - 1)) :=
      Summable.of_norm_bounded hu (fun n => hg' n y htb)
    rw [tsum_mul_pow_pred c y hf'sum] at hderiv
    exact hderiv

end Work.CPull
