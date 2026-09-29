import Mathlib

/-!
# Term-by-term differentiation of a power series with geometric coefficient growth

If `‖c n‖ ≤ C * (1/4)^n` then the power series `f z = ∑' n, c n * z^n` is absolutely
convergent, together with its termwise-derivative series, on the disc `‖z‖ < 4`, and `f` is
complex differentiable there with derivative `∑' n, ((n+1 : ℕ) : ℂ) * c (n+1) * z^n`.

The convergence statements are the comparison test against `∑ (n+1) q^n` for `q = ‖z‖/4 < 1`.
The differentiability statement is Mathlib's term-by-term differentiation of uniformly
dominated series of functions (`hasDerivAt_tsum_of_isPreconnected`) applied on the ball of
radius `r = (‖z‖ + 4)/2`, together with the reindexing `∑ n c n * n * z^(n-1) = ∑ (n+1) c (n+1) * z^n`.
-/

namespace Work.B5pull

open scoped BigOperators

/-- `(1/4)^n * x^n = (x/4)^n`. -/
private lemma geom_pow_mul (n : ℕ) (x : ℝ) : (1 / 4 : ℝ) ^ n * x ^ n = (x / 4) ^ n := by
  rw [← mul_pow]; congr 1; ring

/-- `∑ n, K * (n+1) * q^n` converges for `0 ≤ q < 1`. -/
private lemma summable_succ_mul_geom (K q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => K * ((n : ℝ) + 1) * q ^ n) := by
  have hqnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have h1 : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := q) hqnorm
  have h2 : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_norm_lt_one hqnorm
  exact ((h1.add h2).mul_left K).congr (fun n => by ring)

/-- A complex series dominated by `K * (n+1) * q^n`, `0 ≤ q < 1`, is summable. -/
private lemma summable_of_norm_le_geom {a : ℕ → ℂ} {K q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ n : ℕ, ‖a n‖ ≤ K * ((n : ℝ) + 1) * q ^ n) : Summable a :=
  (summable_succ_mul_geom K q hq hq1).of_norm_bounded h

/-- Reindexing: `∑ n, n c n z^(n-1) = ∑ n, (n+1) c (n+1) z^n`. -/
private lemma tsum_pred_mul_pow (c : ℕ → ℂ) (y : ℂ)
    (h : Summable fun n : ℕ => (n : ℂ) * c n * y ^ (n - 1)) :
    (∑' n : ℕ, (n : ℂ) * c n * y ^ (n - 1))
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n := by
  rw [Summable.tsum_eq_zero_add h]
  have h0 : ((0 : ℕ) : ℂ) * c 0 * y ^ (0 - 1) = 0 := by simp
  rw [h0, zero_add]
  exact tsum_congr fun n => by rw [Nat.add_sub_cancel]

theorem powser_deriv (c : ℕ → ℂ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ n : ℕ, ‖c n‖ ≤ C * (1 / 4 : ℝ) ^ n) :
    (∀ y : ℂ, ‖y‖ < 4 → Summable fun n : ℕ => c n * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 4 → Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) ∧
    (∀ y : ℂ, ‖y‖ < 4 → HasDerivAt (fun z : ℂ => ∑' n : ℕ, c n * z ^ n)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) y) := by
  have hC0 : (0 : ℝ) ≤ C := hC.le
  refine ⟨?_, ?_, ?_⟩
  · -- summability of the series itself
    intro y hy
    have hq0 : 0 ≤ ‖y‖ / 4 := by positivity
    have hq1 : ‖y‖ / 4 < 1 := by linarith
    refine summable_of_norm_le_geom (K := C) hq0 hq1 (fun n => ?_)
    rw [norm_mul, norm_pow]
    calc ‖c n‖ * ‖y‖ ^ n ≤ (C * (1 / 4 : ℝ) ^ n) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg y) n)
      _ = C * (‖y‖ / 4) ^ n := by
          rw [show C * (1 / 4 : ℝ) ^ n * ‖y‖ ^ n = C * ((1 / 4 : ℝ) ^ n * ‖y‖ ^ n) from by ring,
            geom_pow_mul n ‖y‖]
      _ ≤ C * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n := by
          have h1' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
          have h2' : (0 : ℝ) ≤ (‖y‖ / 4) ^ n := pow_nonneg hq0 n
          calc C * (‖y‖ / 4) ^ n = C * 1 * (‖y‖ / 4) ^ n := by ring
            _ ≤ C * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1' hC0) h2'
  · -- summability of the termwise derivative series
    intro y hy
    have hq0 : 0 ≤ ‖y‖ / 4 := by positivity
    have hq1 : ‖y‖ / 4 < 1 := by linarith
    refine summable_of_norm_le_geom (K := C) hq0 hq1 (fun n => ?_)
    have hyn : (0 : ℝ) ≤ ‖y‖ ^ n := pow_nonneg (norm_nonneg y) n
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hp : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 4 : ℝ) ^ n :=
      pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num) (Nat.le_succ n)
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    push_cast
    calc ((n : ℝ) + 1) * ‖c (n + 1)‖ * ‖y‖ ^ n
        ≤ ((n : ℝ) + 1) * (C * (1 / 4 : ℝ) ^ (n + 1)) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb (n + 1)) hn1) hyn
      _ ≤ ((n : ℝ) + 1) * (C * (1 / 4 : ℝ) ^ n) * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC0) hn1) hyn
      _ = C * ((n : ℝ) + 1) * (‖y‖ / 4) ^ n := by
          rw [show ((n : ℝ) + 1) * (C * (1 / 4 : ℝ) ^ n) * ‖y‖ ^ n
                = C * ((n : ℝ) + 1) * ((1 / 4 : ℝ) ^ n * ‖y‖ ^ n) from by ring,
              geom_pow_mul n ‖y‖]
  · -- term-by-term differentiation
    intro y hy
    set r : ℝ := (‖y‖ + 4) / 2 with hrdef
    have hyltr : ‖y‖ < r := by rw [hrdef]; linarith
    have hrpos : 0 < r := by rw [hrdef]; linarith [norm_nonneg y]
    have hr1 : 1 ≤ r := by rw [hrdef]; linarith [norm_nonneg y]
    set q : ℝ := r / 4 with hqdef
    have hq0 : 0 ≤ q := by rw [hqdef]; positivity
    have hq1 : q < 1 := by rw [hqdef]; linarith
    set u : ℕ → ℝ := fun n => C * ((n : ℝ) + 1) * q ^ n with hudef
    have hu : Summable u := summable_succ_mul_geom C q hq0 hq1
    have hg : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun w : ℂ => c n * w ^ n) ((n : ℂ) * c n * z ^ (n - 1)) z := by
      intro n z _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using (hasDerivAt_pow n z).const_mul (c n)
    have hg' : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖(n : ℂ) * c n * z ^ (n - 1)‖ ≤ u n := by
      intro n z hz
      have hzr : ‖z‖ < r := by
        rwa [Metric.mem_ball, dist_zero_right] at hz
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have h0 : ‖(((0 : ℕ)) : ℂ) * c 0 * z ^ (0 - 1)‖ = 0 := by simp
        have h1 : u 0 = C := by simp [hudef]
        rw [h0, h1]
        exact hC.le
      · have hzn : ‖z‖ ^ (n - 1) ≤ r ^ (n - 1) :=
          pow_le_pow_left₀ (norm_nonneg z) hzr.le (n - 1)
        have hrn : r ^ (n - 1) ≤ r ^ n := by
          have h : r ^ n = r ^ (n - 1) * r := by
            conv_lhs => rw [← Nat.sub_add_cancel hn]
            rw [pow_succ]
          rw [h]
          exact le_mul_of_one_le_right (pow_nonneg (le_of_lt hrpos) (n - 1)) hr1
        have hfac : (0 : ℝ) ≤ (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) :=
          mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hC0 (pow_nonneg (by norm_num) n))
        calc ‖(n : ℂ) * c n * z ^ (n - 1)‖
            = (n : ℝ) * ‖c n‖ * ‖z‖ ^ (n - 1) := by
              rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
          _ ≤ (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * r ^ (n - 1) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hb n) (Nat.cast_nonneg n)) hzn
                (pow_nonneg (norm_nonneg z) (n - 1)) hfac
          _ ≤ (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * r ^ n :=
              mul_le_mul_of_nonneg_left hrn hfac
          _ = C * (n : ℝ) * q ^ n := by
              rw [show (n : ℝ) * (C * (1 / 4 : ℝ) ^ n) * r ^ n
                    = C * (n : ℝ) * ((1 / 4 : ℝ) ^ n * r ^ n) from by ring,
                  geom_pow_mul n r, hqdef]
          _ ≤ u n := by
              rw [hudef]
              have h : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hC0)
                (pow_nonneg hq0 n)
    have hy0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_self]; exact hrpos
    have hg0 : Summable (fun n : ℕ => c n * (0 : ℂ) ^ n) := by
      refine summable_of_ne_finset_zero (s := {0}) ?_
      intro n hn
      simp only [Finset.mem_singleton] at hn
      rw [zero_pow hn, mul_zero]
    have htb : y ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hyltr
    have hderiv : HasDerivAt (fun z : ℂ => ∑' n : ℕ, c n * z ^ n)
        (∑' n : ℕ, (n : ℂ) * c n * y ^ (n - 1)) y :=
      hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) r) (y₀ := 0)
        (g := fun n z => c n * z ^ n) (g' := fun n z => (n : ℂ) * c n * z ^ (n - 1))
        (u := u) hu Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected hg hg' hy0 hg0 htb
    have hfs : Summable (fun n : ℕ => (n : ℂ) * c n * y ^ (n - 1)) :=
      Summable.of_norm_bounded hu (fun n => hg' n y htb)
    rwa [tsum_pred_mul_pow c y hfs] at hderiv

end Work.B5pull
