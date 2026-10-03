import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds

open scoped BigOperators
open Finset MeasureTheory intervalIntegral Set

noncomputable section

namespace Commons.NumberTheory.Mertens

/-- The first-Mertens sum at an integer, in the convention of the statement. -/
private def mSum (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)

/-- The prime-power correction sum at an integer. -/
private def cSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))

/-! ## Legendre's formula for `log (n!)` -/

private lemma primeFactors_factorial (n : ℕ) : (n.factorial).primeFactors = n.primesLE := by
  ext p
  constructor
  · intro hp
    rw [Nat.mem_primesLE]
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n.factorial := by
      have hmem : p ∈ (n.factorial).primeFactorsList := by
        exact (Nat.mem_primeFactors_iff_mem_primeFactorsList).1 hp
      exact Nat.dvd_of_mem_primeFactorsList hmem
    exact ⟨(Nat.Prime.dvd_factorial hp').mp hdvd, hp'⟩
  · intro hp
    rw [Nat.mem_primesLE] at hp
    have hnon : n.factorial ≠ 0 := by positivity
    have hdvd : p ∣ n.factorial := (Nat.Prime.dvd_factorial hp.2).mpr hp.1
    exact Nat.Prime.mem_primeFactors hp.2 hdvd hnon

private lemma log_factorial_eq_sum_factorization_log (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ n.primesLE, ((n.factorial).factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization (n.factorial)]
  simp only [Finsupp.sum, Nat.support_factorization]
  rw [primeFactors_factorial]

private lemma log_factorial_eq_sum_legendre (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
  rw [log_factorial_eq_sum_factorization_log]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hfac := Nat.factorization_factorial (Nat.prime_of_mem_primesLE hp) (n := n) (b := n + 1)
  have hlog : Nat.log p n < n + 1 := by
    exact Nat.lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n)
  rw [hfac hlog]
  rw [Nat.cast_sum]

/-! ## The geometric bound and `v_p(n!) ≤ n/(p-1)` -/

/-- For `0 ≤ r < 1` and any `m`, `∑_{k<m} r^k ≤ 1/(1-r)`. -/
private lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, r ^ k) ≤ 1 / (1 - r) := by
  have hr1ne : r ≠ 1 := ne_of_lt hr1
  have h1r : 0 < 1 - r := by linarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hpos : (0 : ℝ) ≤ 1 / (1 - r) := by positivity
    simpa using hpos
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    rcases eq_or_lt_of_le hr0 with h0 | h0
    · subst h0
      have hone : (∑ k ∈ Finset.range (m' + 1), (0 : ℝ) ^ k) = 1 := by
        rw [Finset.sum_range_succ']
        simp
      rw [hone]
      norm_num
    · rw [geom_sum_eq hr1ne (m' + 1)]
      have hrw : (r ^ (m' + 1) - 1) / (r - 1) = (1 - r ^ (m' + 1)) / (1 - r) := by
        field_simp
        ring
      rw [hrw, div_le_div_iff_of_pos_right h1r]
      have := pow_nonneg (le_of_lt h0) (m' + 1)
      linarith

/-- `∑_{i=1}^{n} (1/p)^i ≤ 1/(p-1)` for `p ≥ 2`. -/
private lemma geom_inv_sum_le (n p : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / (p : ℝ)) ^ i) ≤ 1 / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]; linarith
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show n + 1 - 1 = n by omega]
  have hsplit : (∑ k ∈ Finset.range n, (1 / (p : ℝ)) ^ (1 + k)) =
      (1 / (p : ℝ)) * ∑ k ∈ Finset.range n, (1 / (p : ℝ)) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [pow_add, pow_one]
  rw [hsplit]
  have hgeom := geom_sum_le_inv_one_sub (r := 1 / (p : ℝ)) hr0 hr1 n
  have hmono : (1 / (p : ℝ)) * (∑ k ∈ Finset.range n, (1 / (p : ℝ)) ^ k)
      ≤ (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) :=
    mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hval : (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) = 1 / ((p : ℝ) - 1) := by
    field_simp
  calc (1 / (p : ℝ)) * (∑ k ∈ Finset.range n, (1 / (p : ℝ)) ^ k)
      ≤ (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) := hmono
    _ = 1 / ((p : ℝ) - 1) := hval

/-- `v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋ ≤ n/(p-1)` for a prime `p ≥ 2`. -/
private lemma legendre_sum_le (n p : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hstep1 : (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ i := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := p ^ i)
    have hcast : ((p ^ i : ℕ) : ℝ) = (p : ℝ) ^ i := by push_cast; ring
    rw [hcast] at h
    have hrw : (n : ℝ) / (p : ℝ) ^ i = (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ i := by
      rw [div_pow, one_pow]
      field_simp
    exact hrw ▸ h
  have hstep2 : (∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ i) =
      (n : ℝ) * (∑ i ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / (p : ℝ)) ^ i) := by
    rw [Finset.mul_sum]
  have hstep3 : (∑ i ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / (p : ℝ)) ^ i) ≤ 1 / ((p : ℝ) - 1) :=
    geom_inv_sum_le n p hp
  have hstep4 : (n : ℝ) * (∑ i ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / (p : ℝ)) ^ i)
      ≤ (n : ℝ) * (1 / ((p : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left hstep3 (Nat.cast_nonneg n)
  calc (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ))
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) * ((1 : ℝ) / (p : ℝ)) ^ i := hstep1
    _ = (n : ℝ) * (∑ i ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / (p : ℝ)) ^ i) := hstep2
    _ ≤ (n : ℝ) * (1 / ((p : ℝ) - 1)) := hstep4
    _ = (n : ℝ) / ((p : ℝ) - 1) := by ring

/-! ## Assembly: the lower bound at integers -/

private lemma mem_primesLE_two_le {p n : ℕ} (hp : p ∈ n.primesLE) : 2 ≤ p :=
  Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)

private lemma log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le hp))

/-- `∑_{p ≤ n} log p/(p-1) = mSum n + cSum n`. -/
private lemma sum_log_div_pred_eq (n : ℕ) :
    (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) - 1)) = mSum n + cSum n := by
  simp only [mSum, cSum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp2 : 2 ≤ p := mem_primesLE_two_le hp
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  field_simp
  ring

/-- Legendre's formula + `v_p(n!) ≤ n/(p-1)`: `log (n!) ≤ n·(mSum n + cSum n)`. -/
private lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * (mSum n + cSum n) := by
  have hstep : Real.log (n.factorial : ℝ) ≤
      ∑ p ∈ n.primesLE, ((n : ℝ) / ((p : ℝ) - 1)) * Real.log (p : ℝ) := by
    rw [log_factorial_eq_sum_legendre]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := mem_primesLE_two_le hp
    have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg (Nat.prime_of_mem_primesLE hp)
    exact mul_le_mul_of_nonneg_right (legendre_sum_le n p hp2) hlog
  have hsplit : (∑ p ∈ n.primesLE, ((n : ℝ) / ((p : ℝ) - 1)) * Real.log (p : ℝ)) =
      (n : ℝ) * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    ring
  rw [hsplit, sum_log_div_pred_eq] at hstep
  exact hstep

/-! ### Bounding the prime-power correction: `∑_{p ≤ n} log p/(p(p-1)) ≤ 1` -/

/-- `log p ≤ (p-1)/√p` for `p ≥ 2`, via `2 log √p ≤ √p - 1/√p`
(equivalently `log y ≤ sinh (log y) = (y - y⁻¹)/2` for `y = √p ≥ 1`). -/
private lemma log_prime_le_pred_div_sqrt {p : ℕ} (hp : 2 ≤ p) :
    Real.log (p : ℝ) ≤ ((p : ℝ) - 1) / Real.sqrt p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hy1 : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (by omega : 1 ≤ p)
  have hy0 : (0 : ℝ) < Real.sqrt (p : ℝ) := by linarith
  have hlog : Real.log (Real.sqrt p) ≤ (Real.sqrt p - (Real.sqrt p)⁻¹) / 2 := by
    have h := (Real.self_le_sinh_iff (x := Real.log (Real.sqrt p))).mpr
      (Real.log_nonneg hy1)
    rwa [Real.sinh_log hy0] at h
  have hlogp : Real.log (p : ℝ) = 2 * Real.log (Real.sqrt p) := by
    have h := Real.log_pow (Real.sqrt p) 2
    rw [hsq] at h
    rw [h]
    norm_num
  have hval : Real.sqrt p - (Real.sqrt p)⁻¹ = ((p : ℝ) - 1) / Real.sqrt p := by
    field_simp
    nlinarith [hsq]
  rw [hlogp]
  linarith [hlog, hval]

/-- `(log p)/(p(p-1)) ≤ 1/(p·√p)` for `p ≥ 2`. -/
private lemma log_div_p_mul_pred_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) * Real.sqrt p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hs : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hb := log_prime_le_pred_div_sqrt hp
  have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hp0 (by linarith)
  rw [div_le_div_iff₀ hden (mul_pos hp0 hs)]
  have h2 : Real.log (p : ℝ) * ((p : ℝ) * Real.sqrt p)
      ≤ (((p : ℝ) - 1) / Real.sqrt p) * ((p : ℝ) * Real.sqrt p) :=
    mul_le_mul_of_nonneg_right hb (le_of_lt (mul_pos hp0 hs))
  have h3 : (((p : ℝ) - 1) / Real.sqrt p) * ((p : ℝ) * Real.sqrt p) = (p : ℝ) * ((p : ℝ) - 1) := by
    field_simp
  linarith [h2, h3.le, h3.ge]

/-- Rational lower bounds for `√p` at the primes `p ≤ 31`. -/
private def sqrtLB (p : ℕ) : ℝ :=
  if p = 2 then 1.414
  else if p = 3 then 1.732
  else if p = 5 then 2.236
  else if p = 7 then 2.645
  else if p = 11 then 3.316
  else if p = 13 then 3.605
  else if p = 17 then 4.123
  else if p = 19 then 4.358
  else if p = 23 then 4.795
  else if p = 29 then 5.385
  else 5.567

private lemma sqrtLB_pos (p : ℕ) : 0 < sqrtLB p := by
  have hone : (1 : ℝ) ≤ sqrtLB p := by
    unfold sqrtLB
    split_ifs <;> norm_num
  linarith

private lemma sqrtLB_nonneg (p : ℕ) : 0 ≤ sqrtLB p := (sqrtLB_pos p).le

private lemma sqrtLB_sq_le {p : ℕ} (hp : p ∈ (31 : ℕ).primesLE) : (sqrtLB p) ^ 2 ≤ (p : ℝ) := by
  have hle : p ≤ 31 := (Nat.mem_primesLE.mp hp).1
  have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
  interval_cases p <;> first | exact absurd hpr (by decide) | norm_num [sqrtLB]

private lemma sqrtLB_le_sqrt {p : ℕ} (hp : p ∈ (31 : ℕ).primesLE) :
    sqrtLB p ≤ Real.sqrt p := by
  have h := sqrtLB_sq_le hp
  have h0 := sqrtLB_nonneg p
  rw [Real.le_sqrt h0 (by positivity)]
  exact h

/-- `∑_{p ≤ 31} 1/(p√p) ≤ 0.786`. -/
private lemma small_sqrt_sum_le :
    (∑ p ∈ (31 : ℕ).primesLE, 1 / ((p : ℝ) * Real.sqrt p)) ≤ 0.786 := by
  have h31 : (31 : ℕ).primesLE = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by decide
  have hstep : (∑ p ∈ (31 : ℕ).primesLE, 1 / ((p : ℝ) * Real.sqrt p)) ≤
      ∑ p ∈ (31 : ℕ).primesLE, 1 / ((p : ℝ) * sqrtLB p) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hlb := sqrtLB_le_sqrt hp
    exact one_div_le_one_div_of_le (mul_pos hp0 (sqrtLB_pos p))
      (mul_le_mul_of_nonneg_left hlb hp0.le)
  refine le_trans hstep ?_
  rw [h31]
  norm_num [sqrtLB]

/-- Nonnegativity of the correction summands at primes. -/
private lemma cSum_term_nonneg {p n : ℕ} (hp : p ∈ n.primesLE) :
    0 ≤ Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : 2 ≤ p := mem_primesLE_two_le hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  exact div_nonneg (log_prime_nonneg (Nat.prime_of_mem_primesLE hp)) (mul_pos hp0 hp1).le

/-- The primes `≤ 31` contribute at most `0.786` to the correction sum. -/
private lemma small_cSum_le (n : ℕ) :
    (∑ p ∈ n.primesLE.filter (fun p => p ≤ 31),
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 0.786 := by
  have hsub : n.primesLE.filter (fun p => p ≤ 31) ⊆ (31 : ℕ).primesLE := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.2, hp.1.2⟩
  have h1 : (∑ p ∈ n.primesLE.filter (fun p => p ≤ 31),
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∑ p ∈ (31 : ℕ).primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => cSum_term_nonneg (p := p) (n := 31) hp)
  have h2 : (∑ p ∈ (31 : ℕ).primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∑ p ∈ (31 : ℕ).primesLE, 1 / ((p : ℝ) * Real.sqrt p) :=
    Finset.sum_le_sum (fun p hp =>
      log_div_p_mul_pred_le (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2))
  linarith [h1, h2, small_sqrt_sum_le]

/-- Upper bound `log 31 ≤ 3.46574`. -/
private lemma log_31_le : Real.log (31 : ℝ) ≤ 3.46574 := by
  have h2 := Real.log_two_lt_d9
  have hle : Real.log (31 : ℝ) ≤ Real.log (32 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [h32] at hle
  linarith

private lemma hasDerivAt_log_div_sq (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t / (t * t)) ((1 - 2 * Real.log x) / x ^ 3) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx)
  have hsq : HasDerivAt (fun t : ℝ => t * t) (x + x) x := by
    have h := (hasDerivAt_id x).mul (hasDerivAt_id x)
    exact h.congr_deriv (by ring : (1 : ℝ) * x + x * 1 = x + x)
  have hquot := hlog.div hsq (by positivity : x * x ≠ 0)
  have hval : (x⁻¹ * (x * x) - Real.log x * (x + x)) / (x * x) ^ 2 = (1 - 2 * Real.log x) / x ^ 3 := by
    field_simp
    ring
  exact hquot.congr_deriv hval

private lemma antitoneOn_log_div_sq {a N : ℕ} (ha : 2 ≤ a) :
    AntitoneOn (fun x : ℝ => Real.log x / (x * x)) (Set.Icc (a : ℝ) (N : ℝ)) := by
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?hcont ?hdiff ?hderiv
  · refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.mono ?_
      intro x hx
      have hx2 : (2 : ℝ) ≤ x := le_trans ha2 hx.1
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact continuousOn_id.mul continuousOn_id
    · intro x hx
      have hx2 : (2 : ℝ) ≤ x := le_trans ha2 hx.1
      positivity
  · rw [interior_Icc]
    refine DifferentiableOn.div ?_ ?_ ?_
    · refine DifferentiableOn.log differentiableOn_id ?_
      intro x hx
      have hx2 : (2 : ℝ) ≤ x := le_trans ha2 (le_of_lt hx.1)
      linarith
    · exact differentiableOn_id.mul differentiableOn_id
    · intro x hx
      have hx2 : (2 : ℝ) ≤ x := le_trans ha2 (le_of_lt hx.1)
      positivity
  · intro x hx
    rw [interior_Icc] at hx
    have hx2 : (2 : ℝ) ≤ x := le_trans ha2 (le_of_lt hx.1)
    have hx0 : 0 < x := by linarith
    rw [(hasDerivAt_log_div_sq x hx0).deriv]
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogx : (1 / 2 : ℝ) ≤ Real.log x :=
      le_trans hlog2.le (Real.log_le_log (by norm_num) hx2)
    have hnum : 1 - 2 * Real.log x ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

private lemma hasDerivAt_antideriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -(Real.log t + 1) / t) (Real.log x / (x * x)) x := by
  have hnum : HasDerivAt (fun t : ℝ => -(Real.log t + 1)) (-(x⁻¹)) x :=
    ((Real.hasDerivAt_log (ne_of_gt hx)).add_const 1).neg
  have hden : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hq := hnum.div hden (ne_of_gt hx)
  have hval : (-(x⁻¹) * x - (-(Real.log x + 1)) * 1) / x ^ 2 = Real.log x / (x * x) := by
    field_simp
    ring
  exact hq.congr_deriv hval

private lemma integral_log_div_sq {a N : ℕ} (ha : 2 ≤ a) (hle : a ≤ N) :
    (∫ x in (a : ℝ)..(N : ℝ), Real.log x / (x * x)) =
      (Real.log (a : ℝ) + 1) / (a : ℝ) - (Real.log (N : ℝ) + 1) / (N : ℝ) := by
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := le_trans ha2 (by exact_mod_cast hle)
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (a : ℝ) (N : ℝ),
      HasDerivAt (fun t : ℝ => -(Real.log t + 1) / t) (Real.log x / (x * x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hle)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
    exact hasDerivAt_antideriv x hx0
  have hint : IntervalIntegrable (fun x : ℝ => Real.log x / (x * x)) volume (a : ℝ) (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by exact_mod_cast hle)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.mono ?_
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact continuousOn_id.mul continuousOn_id
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha0 hx.1
      positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hane : (a : ℝ) ≠ 0 := ne_of_gt ha0
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  field_simp
  ring

private lemma log_div_sq_Ico_succ_le (a N : ℕ) (ha : 2 ≤ a) :
    (∑ m ∈ Finset.Ico (a + 1) (N + 1), Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ))) ≤
      (Real.log (a : ℝ) + 1) / (a : ℝ) := by
  by_cases hN : N ≤ a
  · have hempty : Finset.Ico (a + 1) (N + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
    positivity
  · have hle : a ≤ N := by omega
    have hanti := antitoneOn_log_div_sq (N := N) ha
    have hstep : (∑ i ∈ Finset.Ico a N,
          (fun x : ℝ => Real.log x / (x * x)) ((i : ℝ) + 1)) ≤
        ∫ x in (a : ℝ)..(N : ℝ), Real.log x / (x * x) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => Real.log x / (x * x)) hle hanti)
    have hre : (∑ i ∈ Finset.Ico a N,
          (fun x : ℝ => Real.log x / (x * x)) ((i : ℕ) + 1)) =
        ∑ m ∈ Finset.Ico (a + 1) (N + 1), Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ)) := by
      have h := Finset.sum_Ico_add' (fun m : ℕ => Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ))) a N 1
      simpa only [Nat.cast_add, Nat.cast_one] using h
    have hint := integral_log_div_sq (a := a) (N := N) ha hle
    have hnonneg : 0 ≤ (Real.log (N : ℝ) + 1) / (N : ℝ) := by
      apply div_nonneg _ (by positivity)
      have : (0 : ℝ) < Real.log (N : ℝ) := by
        have h1 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        have h2 : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
        exact Real.log_pos (by linarith)
      linarith
    calc (∑ m ∈ Finset.Ico (a + 1) (N + 1), Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ)))
        = ∑ i ∈ Finset.Ico a N, (fun x : ℝ => Real.log x / (x * x)) ((i : ℕ) + 1) := hre.symm
      _ ≤ ∫ x in (a : ℝ)..(N : ℝ), Real.log x / (x * x) := hstep
      _ = (Real.log (a : ℝ) + 1) / (a : ℝ) - (Real.log (N : ℝ) + 1) / (N : ℝ) := hint
      _ ≤ (Real.log (a : ℝ) + 1) / (a : ℝ) := by linarith


/-- The primes above `31` contribute at most `0.15` to the correction sum. -/
private lemma tail_cSum_le (n : ℕ) :
    (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 0.15 := by
  -- termwise comparison with `(32/31)·log p / p²`
  have hterm : ∀ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        (32 / 31 : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp32 : 32 ≤ p := hp.2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
      linarith
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      log_prime_nonneg (Nat.prime_of_mem_primesLE hp.1)
    have hratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 32 / 31 := by
      rw [div_le_div_iff₀ hp1 (by norm_num : (0 : ℝ) < 31)]
      have hp32' : (32 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp32
      linarith
    have hkey : Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))
        * ((p : ℝ) / ((p : ℝ) - 1)) =
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp
    calc Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        = (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) * ((p : ℝ) / ((p : ℝ) - 1)) := hkey.symm
      _ ≤ (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) * (32 / 31) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (32 / 31 : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) := by ring
  -- the integer sum
  have hsub : n.primesLE.filter (fun p => 32 ≤ p) ⊆ Finset.Ico 32 (n + 1) := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2, by omega⟩
  have hint : (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) ≤
      ∑ m ∈ Finset.Ico 32 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => ?_)
    have hm2 : 2 ≤ m := le_trans (by norm_num : 2 ≤ 32) (Finset.mem_Ico.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))) (mul_pos hm0 hm0).le
  have hIco : Finset.Ico 32 (n + 1) = Finset.Ico (31 + 1) (n + 1) := by norm_num
  have hint' : (∑ m ∈ Finset.Ico 32 (n + 1), Real.log (m : ℝ) / ((m : ℝ) * (m : ℝ))) ≤
      (Real.log 31 + 1) / 31 := by
    rw [hIco]
    exact log_div_sq_Ico_succ_le 31 n (by norm_num)
  have hmid : (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) ≤ (Real.log 31 + 1) / 31 :=
    le_trans hint hint'
  have hnum : (32 / 31 : ℝ) * ((Real.log 31 + 1) / 31) ≤ 0.15 := by
    have h1 : (Real.log 31 + 1) / 31 ≤ (3.46574 + 1) / 31 :=
      div_le_div_of_nonneg_right (by linarith [log_31_le]) (by norm_num)
    calc (32 / 31 : ℝ) * ((Real.log 31 + 1) / 31)
        ≤ (32 / 31) * ((3.46574 + 1) / 31) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 0.15 := by norm_num
  have hfinal : (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      (32 / 31 : ℝ) * ((Real.log 31 + 1) / 31) := by
    have hsum : (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
        (32 / 31 : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ)))) =
        (32 / 31 : ℝ) * (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) := by
      rw [Finset.mul_sum]
    calc (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤ ∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
            (32 / 31 : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = (32 / 31 : ℝ) * (∑ p ∈ n.primesLE.filter (fun p => 32 ≤ p),
            Real.log (p : ℝ) / ((p : ℝ) * (p : ℝ))) := hsum
      _ ≤ (32 / 31 : ℝ) * ((Real.log 31 + 1) / 31) :=
          mul_le_mul_of_nonneg_left hmid (by norm_num)
  linarith [hfinal, hnum]

private lemma cSum_le_one (n : ℕ) : cSum n ≤ 1 := by
  have hsmall := small_cSum_le n
  have htail := tail_cSum_le n
  have hfilt : n.primesLE.filter (fun p => ¬ p ≤ 31) = n.primesLE.filter (fun p => 32 ≤ p) := by
    apply Finset.filter_congr
    intro p hp
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := n.primesLE) (p := fun p => p ≤ 31)
    (f := fun p => Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
  simp only [cSum]
  rw [← hsplit, hfilt]
  linarith [hsmall, htail]

/-- The integer form: for `n ≥ 2`, `log n - 2 + 1/n ≤ ∑_{p ≤ n} log p/p`. -/
private lemma int_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n : ℝ) - 2 + 1 / (n : ℝ) ≤ mSum n := by
  have hn1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn1
  have hfac := (Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds hn).1
  -- hfac : 1 ≤ log (n!) - (n log n - n)
  have hle := log_factorial_le n
  have hc := cSum_le_one n
  have hbound : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 ≤ (n : ℝ) * mSum n + (n : ℝ) := by
    have h1 : (n : ℝ) * (mSum n + cSum n) ≤ (n : ℝ) * mSum n + (n : ℝ) := by
      nlinarith [hc, hn1]
    linarith [hle, h1, hfac]
  have hgoal : (n : ℝ) * (Real.log (n : ℝ) - 2 + 1 / (n : ℝ)) ≤ (n : ℝ) * mSum n := by
    have : (n : ℝ) * (Real.log (n : ℝ) - 2 + 1 / (n : ℝ)) =
        (n : ℝ) * Real.log (n : ℝ) - 2 * (n : ℝ) + 1 := by
      field_simp
    rw [this]
    linarith
  exact le_of_mul_le_mul_left hgoal hn1

/-! ## The real form -/

private lemma floor_nonneg {x : ℝ} (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx

/-- `log x ≤ log ⌊x⌋₊ + 1/⌊x⌋₊` for `x ≥ 2`. -/
private lemma log_le_log_floor_add (x : ℝ) (hx : 2 ≤ x) :
    Real.log x ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) + 1 / ((⌊x⌋₊ : ℕ) : ℝ) := by
  have hx0 : 0 < x := by linarith
  set N : ℕ := ⌊x⌋₊ with hN
  have hN2 : 2 ≤ N := by
    have h := Nat.floor_mono hx
    norm_num at h
    exact h
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hxlt : x < (N : ℝ) + 1 := by
    rw [hN]
    exact Nat.lt_floor_add_one x
  have h1 : Real.log x ≤ Real.log ((N : ℝ) + 1) := by
    refine Real.log_le_log hx0 (le_of_lt hxlt)
  have h2 : Real.log ((N : ℝ) + 1) = Real.log (N : ℝ) + Real.log (1 + 1 / (N : ℝ)) := by
    have hrw : (N : ℝ) + 1 = (N : ℝ) * (1 + 1 / (N : ℝ)) := by
      field_simp
    rw [hrw, Real.log_mul (ne_of_gt hN0) (by positivity)]
  have h3 : Real.log (1 + 1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (N : ℝ)) (by positivity)
    linarith
  linarith [h1, h2, h3]



/-! ## The target theorem -/

/-- **First Mertens inequality, lower form with explicit constant `2`.** For every real
`x ≥ 2`, `log x - 2 ≤ ∑_{p prime, p ≤ x} (log p)/p`. -/
theorem log_prime_div_prime_ge_log_sub_two (x : ℝ) (hx : 2 ≤ x) :
    Real.log x - 2 ≤ (∑ p ∈ (⌊x⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hN2 : 2 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    norm_num at h
    exact h
  have hb := int_bound ⌊x⌋₊ hN2
  have hlx := log_le_log_floor_add x hx
  have hmain : Real.log x - 2 ≤ mSum ⌊x⌋₊ := by linarith
  simpa [mSum] using hmain

end Commons.NumberTheory.Mertens