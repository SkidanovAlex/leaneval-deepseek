import Mathlib
import Submission.Work.Holonomy3.polydisc_log_mean

namespace Work.Holonomy3

open MeasureTheory Polynomial
open scoped Real BigOperators

/-- **Reverse Jensen inequality for the leading coefficient of a polynomial.**

For any coefficient sequence `a` and `ε > 0`, the logarithm of `‖a N‖ + ε` is bounded by the
average over the unit circle of `log (‖∑_{k ≤ N} a k z^k‖ + ε)`.

The proof applies the (smoothed) Jensen mean-value inequality `smoothed_jensen` to the reversed
polynomial with conjugated coefficients `g z = ∑_{j ≤ N} conj (a j) * z^{N-j}`.  On the unit circle
`g` coincides, up to the unimodular factor `z^N`, with the conjugate of the original polynomial,
so `‖g z‖ = ‖∑_{k ≤ N} a k z^k‖`, while `g 0 = conj (a N)`. -/
theorem rev_jensen_trig (a : ℕ → ℂ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.log (‖a N‖ + ε) ≤
      ∫ θ : ℝ, Real.log (‖Finset.sum (Finset.range (N + 1)) (fun k => a k * Work.Holonomy3.circlePt θ ^ k)‖ + ε)
        ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) := by
  classical
  -- The reversed polynomial with conjugated coefficients.
  set g : ℂ → ℂ := fun z => ∑ j ∈ Finset.range (N+1), star (a j) * z^(N-j) with hg
  -- `g` is a polynomial, hence analytic.
  have hg_an : AnalyticOnNhd ℂ g (Metric.closedBall 0 1) := by
    let gp : Polynomial ℂ :=
      ∑ j ∈ Finset.range (N+1), Polynomial.C (star (a j)) * Polynomial.X^(N-j)
    have hfun : g = fun z : ℂ => Polynomial.eval z gp := by
      funext z
      rw [hg]
      simp only [gp, Polynomial.eval_finsetSum]
      simp
    rw [hfun]
    exact fun z _ => AnalyticOnNhd.eval_polynomial gp z (Set.mem_univ z)
  -- The value at the origin is the conjugate of the top coefficient.
  have hg0 : g 0 = star (a N) := by
    rw [hg]
    simp only []
    rw [Finset.sum_eq_single N]
    · simp
    · intro j hj hjne
      have hjN : j < N := by
        have h : j < N + 1 := Finset.mem_range.mp hj
        omega
      rw [zero_pow (by omega : N - j ≠ 0), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self N)) h
  -- On the unit circle `g` has the same modulus as the original polynomial.
  have hgnorm : ∀ z : ℂ, ‖z‖ = 1 → ‖g z‖ = ‖∑ k ∈ Finset.range (N+1), a k * z^k‖ := by
    intro z hz
    have hmain : g z = z^N * star (∑ k ∈ Finset.range (N+1), a k * z^k) := by
      rw [hg]
      rw [star_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hzz : z * star z = 1 := by
        rw [show z * star z = (Complex.normSq z : ℂ) from Complex.mul_conj z,
          Complex.normSq_eq_norm_sq, hz]
        norm_num
      have hpow : z^(N-j) = z^N * star z ^ j := by
        calc z^(N-j) = z^(N-j) * (z * star z)^j := by rw [hzz, one_pow, mul_one]
          _ = z^(N-j) * (z^j * star z ^j) := by rw [mul_pow]
          _ = (z^(N-j) * z^j) * star z ^j := by rw [mul_assoc]
          _ = z^N * star z ^j := by rw [← pow_add, Nat.sub_add_cancel hjN]
      rw [hpow, star_mul, star_pow]
      ring
    rw [hmain, norm_mul, norm_star]
    have hzn : ‖z^N‖ = 1 := by rw [norm_pow, hz, one_pow]
    rw [hzn, one_mul]
  -- The smoothed Jensen inequality for `g`.
  have h1 := Work.Holonomy3.smoothed_jensen g hg_an hε
  rw [hg0, norm_star] at h1
  refine h1.trans (le_of_eq ?_)
  -- Identify the two circle integrals pointwise.
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ
  change Real.log (‖g (Work.Holonomy3.circlePt θ)‖ + ε)
      = Real.log (‖∑ k ∈ Finset.range (N+1), a k * Work.Holonomy3.circlePt θ ^ k‖ + ε)
  rw [hgnorm (Work.Holonomy3.circlePt θ) (Work.Holonomy3.norm_circlePt θ)]

end Work.Holonomy3
