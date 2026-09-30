import Mathlib
import Submission.Commons.NumberTheory.Mertens.theta_sub_id_phi_integral_finite
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `∑_{p ≤ x} 1/p − log log x − L = O((log x)^{-A})`

For every real `A > 0` the reciprocal sum over primes differs from `log log x` by a
constant up to an error of size `(log x)^{-A}`.  This is the Prime Number Theorem with a
power-of-log error term (`theta_sub_id_powLog`), transported to the prime reciprocal sum
by Abel summation (`theta_sub_id_phi_integral_finite`) and an explicit bound for the
resulting tail integral.

The construction: for `x ≥ max x₀ 11` one has on the one hand the exact Abel identity
```
∫_x^X (θ t − t) (log t + 1)/(t² (log t)²) dt
  = −(θ X − X)/(X log X) + (θ x − x)/(x log x) + (primeRecips X − primeRecips x)
    − (log log X − log log x)
```
and on the other hand the θ-bound `|θ t − t| ≤ t/(log t)^N` for a large integer `N ≥ A`.
Letting `X → ∞` (the second Mertens limit `primeRecips X − log log X → M` exists) shows that
the remainder `primeRecips x − log log x − M` equals `(θ x − x)/(x log x)` minus the
convergent tail `∫_x^∞ (θ t − t) φ(t) dt`, whose absolute value is at most
`2/(N (log x)^N) → O((log x)^{-A})`.  Below the threshold the closed range `[11, X₁]` is
handled by boundedness (`primeRecips_sub_loglog_bound`).
-/

open Finset Real Filter MeasureTheory
open scoped Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `Fval x = ∑_{p ≤ x} 1/p − log log x`, the remainder in the second Mertens theorem. -/
private def Fval (x : ℝ) : ℝ := primeRecips x - Real.log (Real.log x)

lemma hasDerivAt_neg_one_div_mul_log_pow (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => -1 / ((n : ℝ) * (Real.log s) ^ n))
      (1 / (t * (Real.log t) ^ (n + 1))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hL : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : n ≠ 0))
    exact ne_of_gt this
  have hlog : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log ht0
  have hpow : HasDerivAt (fun s : ℝ => (Real.log s) ^ n)
      ((n : ℝ) * (Real.log t) ^ (n - 1) * t⁻¹) t := hlog.pow n
  have hden : HasDerivAt (fun s : ℝ => (n : ℝ) * (Real.log s) ^ n)
      ((n : ℝ) * ((n : ℝ) * (Real.log t) ^ (n - 1) * t⁻¹)) t := hpow.const_mul (n : ℝ)
  have hden0 : (n : ℝ) * (Real.log t) ^ n ≠ 0 := mul_ne_zero hn0 (pow_ne_zero n hL)
  have h := (hasDerivAt_const (x := t) (-1 : ℝ)).div hden hden0
  have hderiv :
      (0 * ((n : ℝ) * (Real.log t) ^ n) - (-1) * ((n : ℝ) * ((n : ℝ) * (Real.log t) ^ (n - 1) * t⁻¹)))
        / ((n : ℝ) * (Real.log t) ^ n) ^ 2 = 1 / (t * (Real.log t) ^ (n + 1)) := by
    set L : ℝ := Real.log t with hLdef
    have hLp : L ^ n = L ^ (n - 1) * L := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_add, pow_one]
    have hL2 : L ^ (n * 2) = L ^ n * L ^ n := by
      rw [show n * 2 = n + n by ring, pow_add]
    have hLp1 : L ^ (n + 1) = L * L ^ n := by rw [pow_succ']
    have hLp' : L ^ n = L * L ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ']
    rw [show (0 * ((n : ℝ) * L ^ n) - (-1) * ((n : ℝ) * ((n : ℝ) * L ^ (n - 1) * t⁻¹)))
        = (n : ℝ)^2 * L ^ (n - 1) * t⁻¹ by ring]
    rw [mul_pow, ← pow_mul, hL2, hLp, hLp1]
    field_simp
    rw [hLp']
    ring
  exact h.congr_deriv hderiv

private lemma integral_inv_mul_log_pow (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (t * (Real.log t) ^ (n + 1)) =
      1 / ((n : ℝ) * (Real.log a) ^ n) - 1 / ((n : ℝ) * (Real.log b) ^ n) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => -1 / ((n : ℝ) * (Real.log s) ^ n))
        (1 / (x * (Real.log x) ^ (n + 1))) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_neg_one_div_mul_log_pow n hn (by linarith [hx.1])
  have hint : IntervalIntegrable (fun t : ℝ => 1 / (t * (Real.log t) ^ (n + 1))) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : (0 : ℝ) < Real.log t := Real.log_pos ht1
    fun_prop (disch := positivity)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  ring

private lemma tail_integral_bound {N : ℕ} (hN : 1 ≤ N) {x₀ x X : ℝ}
    (hθ : ∀ t : ℝ, x₀ ≤ t → |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ N)
    (hx₀ : x₀ ≤ x) (hx1 : 1 < x) (hxe : Real.exp 1 ≤ x) (hxX : x ≤ X) :
    |∫ t in x..X,
        (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))| ≤
      2 / ((N : ℝ) * (Real.log x) ^ N) := by
  have hX1 : 1 < X := lt_of_lt_of_le hx1 hxX
  have hpt : ∀ t ∈ Set.Ioc x X,
      ‖(Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))‖ ≤
        2 / (t * (Real.log t) ^ (N + 1)) := by
    intro t ht
    have hxt : x < t := ht.1
    have ht1 : 1 < t := lt_trans hx1 hxt
    have ht0 : (0 : ℝ) < t := by linarith
    have hltpos : 0 < Real.log t := Real.log_pos ht1
    have hL1 : 1 ≤ Real.log t := by
      have hxt2 : Real.exp 1 ≤ t := le_trans hxe (le_of_lt hxt)
      have := Real.log_le_log (Real.exp_pos 1) hxt2
      rwa [Real.log_exp] at this
    have hθt := hθ t (le_trans hx₀ (le_of_lt hxt))
    have hfrac : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
    have hφle : (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) ≤ 2 / (t ^ 2 * Real.log t) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < t ^ 2 * (Real.log t) ^ 2)]
      rw [show (2 / (t ^ 2 * Real.log t)) * (t ^ 2 * (Real.log t) ^ 2) = 2 * Real.log t by
        field_simp]
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hfrac]
    have hnon : (0:ℝ) ≤ t / (Real.log t) ^ N := by positivity
    have hkey : (t / (Real.log t) ^ N) * (2 / (t ^ 2 * Real.log t)) = 2 / (t * (Real.log t) ^ (N + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    calc |Chebyshev.theta t - t| * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        ≤ (t / (Real.log t) ^ N) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
          mul_le_mul_of_nonneg_right hθt hfrac
      _ ≤ (t / (Real.log t) ^ N) * (2 / (t ^ 2 * Real.log t)) :=
          mul_le_mul_of_nonneg_left hφle hnon
      _ = 2 / (t * (Real.log t) ^ (N + 1)) := hkey
  have hgint : IntervalIntegrable (fun t : ℝ => 2 / (t * (Real.log t) ^ (N + 1))) volume x X := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxX
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hx1 ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : (0 : ℝ) < Real.log t := Real.log_pos ht1
    fun_prop (disch := positivity)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hxX (Eventually.of_forall hpt) hgint
  rw [Real.norm_eq_abs] at hnorm
  have hInt : ∫ t in x..X, 2 / (t * (Real.log t) ^ (N + 1)) =
      2 * (1 / ((N : ℝ) * (Real.log x) ^ N) - 1 / ((N : ℝ) * (Real.log X) ^ N)) := by
    rw [show (fun t : ℝ => 2 / (t * (Real.log t) ^ (N + 1)))
          = (fun t => 2 * (1 / (t * (Real.log t) ^ (N + 1)))) by funext t; ring]
    rw [intervalIntegral.integral_const_mul, integral_inv_mul_log_pow N hN hx1 hxX]
  have hpos : 0 ≤ 1 / ((N : ℝ) * (Real.log X) ^ N) :=
    div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg N)
      (pow_nonneg (le_of_lt (Real.log_pos hX1)) N))
  calc |∫ t in x..X,
        (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
      ≤ ∫ t in x..X, 2 / (t * (Real.log t) ^ (N + 1)) := hnorm
    _ = 2 * (1 / ((N : ℝ) * (Real.log x) ^ N) - 1 / ((N : ℝ) * (Real.log X) ^ N)) := hInt
    _ ≤ 2 / ((N : ℝ) * (Real.log x) ^ N) := by
        have h2 : 2 * (1 / ((N : ℝ) * (Real.log x) ^ N) - 1 / ((N : ℝ) * (Real.log X) ^ N))
            = 2 / ((N : ℝ) * (Real.log x) ^ N) - 2 * (1 / ((N : ℝ) * (Real.log X) ^ N)) := by ring
        rw [h2]; linarith [hpos]

private lemma ratio_bound {N : ℕ} {x₀ : ℝ}
    (hθ : ∀ t : ℝ, x₀ ≤ t → |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ N)
    {u : ℝ} (hu₀ : x₀ ≤ u) (hu1 : 1 < u) :
    |(Chebyshev.theta u - u) / (u * Real.log u)| ≤ 1 / (Real.log u) ^ (N + 1) := by
  have hu0 : 0 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hθu := hθ u hu₀
  rw [abs_div, abs_of_pos (mul_pos hu0 hlogu)]
  calc |Chebyshev.theta u - u| / (u * Real.log u)
      ≤ (u / (Real.log u) ^ N) / (u * Real.log u) := by
        apply div_le_div_of_nonneg_right hθu
        positivity
    _ = 1 / (Real.log u) ^ (N + 1) := by
        rw [pow_succ]; field_simp

private lemma rate_small {N : ℕ} (hN : 1 ≤ N) {x₀ x : ℝ}
    (hθ : ∀ t : ℝ, x₀ ≤ t → |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ N)
    {L : ℝ} (hL : Filter.Tendsto Fval Filter.atTop (nhds L))
    (hx₀ : x₀ ≤ x) (hx2 : 2 ≤ x) (hxe : Real.exp 1 ≤ x) :
    |Fval x - L| ≤ 2 / ((N : ℝ) * (Real.log x) ^ N) + 1 / (Real.log x) ^ (N + 1) := by
  have hx1 : 1 < x := by linarith
  have htend : Filter.Tendsto (fun X : ℝ => |Fval x - Fval X|) Filter.atTop (nhds |Fval x - L|) :=
    (tendsto_const_nhds.sub hL).abs
  have hD1 : Filter.Tendsto (fun X : ℝ => (Real.log X) ^ N) Filter.atTop Filter.atTop := by
    have h := (tendsto_rpow_atTop (show (0:ℝ) < (N:ℝ) by positivity)).comp Real.tendsto_log_atTop
    simpa only [Function.comp_def, Real.rpow_natCast] using h
  have hD : Filter.Tendsto (fun X : ℝ => 1 / (Real.log X) ^ N) Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hD1
    simpa only [one_div, Function.comp_def] using h
  have hbnd : ∀ᶠ X : ℝ in Filter.atTop,
      |Fval x - Fval X| ≤
        (2 / ((N : ℝ) * (Real.log x) ^ N) + 1 / (Real.log x) ^ (N + 1))
          + 1 / (Real.log X) ^ N := by
    filter_upwards [Filter.eventually_ge_atTop x, Filter.eventually_ge_atTop x₀,
      Filter.eventually_ge_atTop (Real.exp 1)] with X hxX hx₀X hXe
    have hX1 : 1 < X := lt_of_lt_of_le hx1 hxX
    have hid := Commons.NumberTheory.Mertens.theta_sub_id_phi_integral_finite (x := x) (X := X) hx2 hxX
    have hidn : (∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        = -((Chebyshev.theta X - X) / (X * Real.log X))
          + (Chebyshev.theta x - x) / (x * Real.log x)
          + (primeRecips X - primeRecips x)
          - (Real.log (Real.log X) - Real.log (Real.log x)) := by
      have h := hid
      rw [neg_div] at h
      exact h
    have hkey : Fval X - Fval x =
        (∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        + (Chebyshev.theta X - X) / (X * Real.log X)
        - (Chebyshev.theta x - x) / (x * Real.log x) := by
      unfold Fval
      linarith [hidn]
    have htri : |Fval x - Fval X| ≤
        |∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
        + |(Chebyshev.theta X - X) / (X * Real.log X)|
        + |(Chebyshev.theta x - x) / (x * Real.log x)| := by
      have hrew : Fval x - Fval X =
          -((∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
          + (Chebyshev.theta X - X) / (X * Real.log X)
          - (Chebyshev.theta x - x) / (x * Real.log x)) := by rw [← hkey]; ring
      rw [hrew, abs_neg, sub_eq_add_neg]
      calc |((∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
              + (Chebyshev.theta X - X) / (X * Real.log X))
              + -((Chebyshev.theta x - x) / (x * Real.log x))|
          ≤ |(∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
              + (Chebyshev.theta X - X) / (X * Real.log X)|
            + |-((Chebyshev.theta x - x) / (x * Real.log x))| := abs_add_le _ _
        _ = |(∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
              + (Chebyshev.theta X - X) / (X * Real.log X)|
            + |(Chebyshev.theta x - x) / (x * Real.log x)| := by rw [abs_neg]
        _ ≤ (|∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
              + |(Chebyshev.theta X - X) / (X * Real.log X)|)
            + |(Chebyshev.theta x - x) / (x * Real.log x)| := by
            linarith [abs_add_le (∫ t in x..X, (Chebyshev.theta t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ((Chebyshev.theta X - X) / (X * Real.log X))]
    have hI := tail_integral_bound hN hθ hx₀ hx1 hxe hxX
    have hXr : |(Chebyshev.theta X - X) / (X * Real.log X)| ≤ 1 / (Real.log X) ^ N := by
      have h1 := ratio_bound hθ hx₀X hX1
      have h2 : 1 / (Real.log X) ^ (N + 1) ≤ 1 / (Real.log X) ^ N := by
        have hL1 : 1 ≤ Real.log X := by
          have h := Real.log_le_log (Real.exp_pos 1) hXe
          rwa [Real.log_exp] at h
        exact one_div_le_one_div_of_le (pow_pos (Real.log_pos hX1) N)
          (pow_le_pow_right₀ hL1 (Nat.le_succ N))
      linarith
    have hxr : |(Chebyshev.theta x - x) / (x * Real.log x)| ≤ 1 / (Real.log x) ^ (N + 1) :=
      ratio_bound hθ hx₀ hx1
    linarith
  have := le_of_tendsto_of_tendsto htend (tendsto_const_nhds.add hD) hbnd
  simpa using this


/-- Arithmetic step: for `1 ≤ N`, `A ≤ N`, `1 ≤ log x`, the reciprocals
`2/(N (log x)^N)` and `1/(log x)^{N+1}` together are at most `3/(log x)^A`. -/
private lemma bound_to_three {N : ℕ} (hN : 1 ≤ N) {A : ℝ} (hAN : A ≤ (N : ℝ)) {x : ℝ}
    (hx : 1 ≤ Real.log x) :
    2 / ((N : ℝ) * (Real.log x) ^ N) + 1 / (Real.log x) ^ (N + 1) ≤ 3 / (Real.log x) ^ A := by
  have hxpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hx
  have hpowA : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hxpos A
  have hpowN : 0 < (Real.log x) ^ N := pow_pos hxpos N
  have hAN' : (Real.log x) ^ A ≤ (Real.log x) ^ N := by
    rw [← Real.rpow_natCast (Real.log x) N]
    exact Real.rpow_le_rpow_of_exponent_le hx hAN
  have hNN1 : (Real.log x) ^ N ≤ (Real.log x) ^ (N + 1) :=
    pow_le_pow_right₀ hx (Nat.le_succ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have h1 : 2 / ((N : ℝ) * (Real.log x) ^ N) ≤ 2 / (Real.log x) ^ A := by
    have hle : (Real.log x) ^ N ≤ (N : ℝ) * (Real.log x) ^ N := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN) hpowN.le
      simpa using this
    calc 2 / ((N : ℝ) * (Real.log x) ^ N) ≤ 2 / (Real.log x) ^ N :=
          div_le_div_of_nonneg_left (by norm_num) hpowN hle
      _ ≤ 2 / (Real.log x) ^ A :=
          div_le_div_of_nonneg_left (by norm_num) hpowA hAN'
  have h2 : 1 / (Real.log x) ^ (N + 1) ≤ 1 / (Real.log x) ^ A :=
    one_div_le_one_div_of_le hpowA (le_trans hAN' hNN1)
  calc 2 / ((N : ℝ) * (Real.log x) ^ N) + 1 / (Real.log x) ^ (N + 1)
      ≤ 2 / (Real.log x) ^ A + 1 / (Real.log x) ^ A := by linarith
    _ = 3 / (Real.log x) ^ A := by ring

/-- **Main theorem.**  For every `A > 0`, `∑_{p ≤ x} 1/p − log log x` differs from a constant
`L` by at most `C (log x)^{-A}` for every `x ≥ 11`. -/
theorem primeRecips_sub_loglog_powLog :
    ∀ A : ℝ, 0 < A → ∃ L C : ℝ, 0 < C ∧ ∀ x : ℝ, 11 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x) - L| ≤
        C / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨M, hM⟩ := second_mertens_converges
  obtain ⟨B₀, hB₀pos, hB₀⟩ := primeRecips_sub_loglog_bound
  set N : ℕ := ⌈A⌉₊ + 1 with hNdef
  have hAN : A ≤ (N : ℝ) := by
    have h := Nat.le_ceil A
    rw [hNdef]; push_cast; linarith
  have hN1 : 1 ≤ N := by
    have hpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hA hAN
    have h : 0 < N := by exact_mod_cast hpos
    omega
  obtain ⟨x₀, hθ₀⟩ := Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog (N : ℝ) (by positivity)
  have hθ : ∀ t : ℝ, x₀ ≤ t → |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ N := by
    intro t ht
    have h := hθ₀ t ht
    rwa [Real.rpow_natCast] at h
  set X₁ : ℝ := max x₀ 11 with hX₁def
  have hX₁11 : 11 ≤ X₁ := le_max_right _ _
  have hx₀X₁ : x₀ ≤ X₁ := le_max_left _ _
  have hX₁e : Real.exp 1 ≤ X₁ := by
    have h : Real.exp 1 < 11 := lt_trans Real.exp_one_lt_three (by norm_num)
    linarith
  set L : ℝ := M with hLdef
  set C : ℝ := max 3 ((B₀ + |M|) * (Real.log X₁) ^ A) + 1 with hCdef
  have hKnonneg : 0 ≤ B₀ + |M| := by
    have := abs_nonneg M; linarith
  refine ⟨L, C, ?_, ?_⟩
  · rw [hCdef]
    have h1 := le_max_left (3 : ℝ) ((B₀ + |M|) * (Real.log X₁) ^ A)
    linarith
  · intro x hx11
    have hxpos : 0 < x := by linarith
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    change |Fval x - L| ≤ C / (Real.log x) ^ A
    by_cases hxX : X₁ ≤ x
    · have h2x : 2 ≤ x := by linarith
      have hxe : Real.exp 1 ≤ x := le_trans hX₁e hxX
      have hrate := rate_small (x₀ := x₀) hN1 hθ (x := x) (L := L)
        (by rw [hLdef]; exact hM) (le_trans hx₀X₁ hxX) h2x hxe
      have hL1x : 1 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxe
        rwa [Real.log_exp] at h
      have hthree := bound_to_three hN1 hAN hL1x
      have h3C : (3 : ℝ) ≤ C := by
        rw [hCdef]; have := le_max_left (3:ℝ) ((B₀ + |M|) * (Real.log X₁) ^ A); linarith
      have hdenA : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogxpos A
      calc |Fval x - L|
          ≤ 2 / ((N : ℝ) * (Real.log x) ^ N) + 1 / (Real.log x) ^ (N + 1) := hrate
        _ ≤ 3 / (Real.log x) ^ A := hthree
        _ ≤ C / (Real.log x) ^ A := div_le_div_of_nonneg_right h3C hdenA.le
    · have hxX1 : x ≤ X₁ := le_of_lt (not_le.mp hxX)
      have hFx : |Fval x| ≤ B₀ := by
        have h := hB₀ x hx11
        simpa only [Fval, primeRecips] using h
      have htri : |Fval x - L| ≤ B₀ + |M| := by
        calc |Fval x - L| ≤ |Fval x| + |L| := by
              have := abs_add_le (Fval x) (-L)
              simpa [sub_eq_add_neg, abs_neg] using this
          _ ≤ B₀ + |M| := by rw [hLdef]; linarith
      have hlogle : Real.log x ≤ Real.log X₁ := Real.log_le_log hxpos hxX1
      have hpowle : (Real.log x) ^ A ≤ (Real.log X₁) ^ A :=
        Real.rpow_le_rpow hlogxpos.le hlogle hA.le
      have hdenA : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogxpos A
      have hCK : (B₀ + |M|) ≤ C / (Real.log x) ^ A := by
        rw [le_div_iff₀ hdenA]
        calc (B₀ + |M|) * (Real.log x) ^ A ≤ (B₀ + |M|) * (Real.log X₁) ^ A :=
              mul_le_mul_of_nonneg_left hpowle hKnonneg
          _ ≤ C := by
              rw [hCdef]
              have := le_max_right (3:ℝ) ((B₀ + |M|) * (Real.log X₁) ^ A)
              linarith
      linarith


end

end Commons.NumberTheory.Mertens
