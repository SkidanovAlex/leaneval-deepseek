import Mathlib

namespace Work.RHContract.A.RegionI

open Finset

/-!
## A sharp lower bound for the Euler--Mascheroni constant

We prove `γ > 57721/100000 ≈ 0.57721`.

The proof uses the increasing sequence `eulerMascheroniSeq n = harmonic n - log (n+1)`,
which converges to `γ` from below, together with the elementary bound

`1/m - log (1 + 1/m) ≥ 1/(2 * m * (m+1))`   (`m ≥ 1`),

whose proof is the trapezoid (convexity) estimate for the logarithm:
`log x ≤ (x - 1/x)/2`, applied with `x = (m+1)/m`.  Summing the bounds for
`m = N+1, …, M` telescopes, giving

`γ > eulerMascheroniSeq M ≥ eulerMascheroniSeq N + (1/2) * (1/(N+1) - 1/(M+1))`.

Taking `N = 255` (so that `N + 1 = 256 = 2^8` and `log 256 = 8 log 2` is cheap to
bound) and `M = 10^6`, all that remains is an explicit rational inequality, which
`decide +kernel` discharges.
-/

/-- For `m ≥ 1`, `log (1 + 1/m) ≤ 1/m - 1/(2 m (m+1))`, i.e.
`1/m - log (1 + 1/m) ≥ 1/(2 m (m+1))`. -/
theorem gamma57721_log_one_add_inv_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + (1:ℝ)/m) ≤ (1:ℝ)/m - 1/(2*(m:ℝ)*((m:ℝ)+1)) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set x : ℝ := 1/(2*(m:ℝ)+1) with hxdef
  have hxm : (0:ℝ) < 2*(m:ℝ)+1 := by linarith
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxlt1 : |x| < 1 := by rw [abs_of_pos hxpos, hxdef, div_lt_one hxm]; linarith
  -- the trapezoid estimate for the truncated series of `log ((1+x)/(1-x))`
  have h := Real.sum_range_sub_log_div_le hxlt1 0
  simp only [Finset.sum_range_zero, sub_zero, Nat.mul_zero, Nat.zero_add, pow_one] at h
  have hid1 : (1 + x)/(1 - x) = 1 + (1:ℝ)/m := by rw [hxdef]; field_simp; try ring
  have hle := (abs_le.1 h).2
  rw [hid1, abs_of_pos hxpos] at hle
  have hfac : 1 - x^2 = 4*(m:ℝ)*((m:ℝ)+1)/(2*(m:ℝ)+1)^2 := by
    rw [hxdef]; field_simp; try ring
  have hgoal : 2 * (x/(1-x^2)) = (1:ℝ)/m - 1/(2*(m:ℝ)*((m:ℝ)+1)) := by
    rw [hfac, hxdef]; field_simp; try ring
  linarith [hle]

/-- The increment of `eulerMascheroniSeq` is `1/m - log (1 + 1/m)`. -/
theorem gamma57721_seq_succ_sub (n : ℕ) :
    Real.eulerMascheroniSeq (n+1) - Real.eulerMascheroniSeq n
      = (1:ℝ)/((n:ℝ)+1) - Real.log (1 + 1/((n:ℝ)+1)) := by
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  rw [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq]
  push_cast
  have hlog : Real.log ((n:ℝ) + 1 + 1) = Real.log ((n:ℝ)+1) + Real.log (1 + 1/((n:ℝ)+1)) := by
    rw [← Real.log_mul (ne_of_gt hn) (by positivity)]
    congr 1
    field_simp; try ring
  rw [hlog]
  have hhar : ((harmonic (n+1) : ℚ) : ℝ) = ((harmonic n : ℚ):ℝ) + 1/((n:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; try ring
  rw [hhar]
  ring

/-- The tail estimate: for `1 ≤ N ≤ M`,
`eulerMascheroniSeq M ≥ eulerMascheroniSeq N + (1/2) (1/(N+1) - 1/(M+1))`. -/
theorem gamma57721_tail (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    Real.eulerMascheroniSeq N + (1/2) * (1/((N:ℝ)+1) - 1/((M:ℝ)+1)) ≤
      Real.eulerMascheroniSeq M := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    push_cast
    have hgoal_eq : (1/2) * (1/((N:ℝ)+1) - 1/(((m:ℝ)+1)+1)) =
        (1/2)*(1/((N:ℝ)+1) - 1/((m:ℝ)+1)) + 1/(2*((m:ℝ)+1)*(((m:ℝ)+1)+1)) := by
      field_simp; try ring
    have hstep : Real.eulerMascheroniSeq m + 1/(2*((m:ℝ)+1)*(((m:ℝ)+1)+1)) ≤
        Real.eulerMascheroniSeq (m+1) := by
      have h1 := gamma57721_seq_succ_sub m
      have h2 := gamma57721_log_one_add_inv_le (m+1) (by omega)
      push_cast at h2
      linarith [h1, h2]
    linarith [ih, hstep, hgoal_eq]

/-- `γ > 57721/100000`.

Mathlib facts: `Real.eulerMascheroniSeq n = harmonic n - log (n+1)` is increasing with
`eulerMascheroniSeq n < γ` (`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`,
`tendsto_eulerMascheroniSeq`); note `eulerMascheroniSeq' n = harmonic n - log n` bounds `γ`
from *above*, so it is useless here.

Route.  With `N = 1000` the partial sums of `a_m := 1/m - log (1 + 1/m)` (`m ≥ N+1`) are
`eulerMascheroniSeq m - (harmonic N - log (N+1))`; since `eulerMascheroniSeq → γ` and
`a_m ≥ 0` with `a_m ≤ 1/(2m²)` summably, this gives
`γ = (harmonic N - log (N+1)) + ∑' k, a_{N+1+k}`.
By the alternating series for `log`, `a_m ≥ 1/(2m²) - 1/(3m³)`, so the tail is at least
`(1/2)∑'_{m>N} 1/m² - (1/3)∑'_{m>N} 1/m³`.  Now `1/m² ≥ 1/m - 1/(m+1)` gives
`∑'_{m>N} 1/m² ≥ 1/(N+1)` (telescoping), and `1/m³ ≤ (1/2)(1/(m-1)² - 1/m²)` for `m ≥ 2`
gives `∑'_{m>N} 1/m³ ≤ 1/(2N²)` (telescoping partial sums plus `tsum_le_of_sum_le`).
Hence `γ ≥ harmonic 1000 - log 1001 + 1/2002 - 1/(6·1000²)`.

Finally `1001 = 1024·(1 - t)` with `t = 23/1024`, so
`log 1001 = 10 log 2 + log (1-t) ≤ 10·(6931471808/10^10) - (t + t²/2 + t³/3 + t⁴/4)`
(using `Real.log_two_lt_d9`; truncating the series of `log (1-t)` gives an upper bound
because all terms are negative).  The resulting explicit rational inequality is closed by
`decide +kernel` with `set_option maxRecDepth 100000` (compiling takes a few seconds since
`harmonic 1000` has a ~430-digit denominator).

Formalisation note: the argument above is what is implemented below, except that we use
`N = 255` and `M = 10^6`.  With `N + 1 = 256 = 2^8` the inequality `log 256 = 8 log 2`
reduces the logarithm to `Real.log_two_lt_d9`, and the only arithmetic left is the
rational fact `57721/100000 < harmonic 255 - 8·0.6931471808 + (1/2)(1/256 - 1/1000001)`,
which `decide +kernel` checks directly (`harmonic 255` has a ~109-digit denominator).
The tail bound used is `1/m - log (1+1/m) ≥ 1/(2 m (m+1))` (the trapezoid estimate
`log x ≤ (x - 1/x)/2`, i.e. the alternating series bound `log(1+u) ≤ u - u²/2 + u³/3`),
which sums by telescoping rather than by an appeal to `tsum`. -/
theorem gamma_gt_57721 : (57721 : ℝ) / 100000 < Real.eulerMascheroniConstant := by
  -- the tail estimate with `N = 255`, `M = 10^6`
  have htail := gamma57721_tail 255 1000000 (by norm_num) (by norm_num)
  have hnumN : ((255 : ℕ) : ℝ) + 1 = 256 := by norm_num
  have hnumM : ((1000000 : ℕ) : ℝ) + 1 = 1000001 := by norm_num
  rw [hnumN, hnumM] at htail
  have hγ : Real.eulerMascheroniSeq 1000000 < Real.eulerMascheroniConstant :=
    Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 1000000
  -- `eulerMascheroniSeq 255 = harmonic 255 - log 256 = harmonic 255 - 8 log 2`
  have hseq : Real.eulerMascheroniSeq 255 = (harmonic 255 : ℝ) - Real.log 256 := by
    rw [Real.eulerMascheroniSeq, hnumN]
  have hlog256 : Real.log 256 = 8 * Real.log 2 := by
    have h2 : (256 : ℝ) = 2^8 := by norm_num
    rw [h2, Real.log_pow]
    norm_num
  have hlog2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  -- the explicit rational inequality
  have hrat : ((57721 : ℚ)/100000) <
      harmonic 255 - 8*(0.6931471808 : ℚ) + (1/2)*(1/256 - 1/1000001) := by
    decide +kernel
  have hreal : ((57721 : ℝ)/100000) <
      (harmonic 255 : ℝ) - 8*(0.6931471808 : ℝ) + (1/2)*(1/256 - 1/1000001) := by
    have h2 := (Rat.cast_lt (K := ℝ)).2 hrat
    push_cast at h2
    exact h2
  linarith [htail, hγ, hseq, hlog256, hreal, hlog2]

end Work.RHContract.A.RegionI
