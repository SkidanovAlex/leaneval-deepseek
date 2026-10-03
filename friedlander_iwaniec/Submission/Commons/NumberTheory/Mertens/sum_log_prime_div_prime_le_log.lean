import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.Analysis.ExpLog.log_le_two_sqrt
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds

noncomputable section

set_option maxRecDepth 10000

open Finset Real
open scoped BigOperators

namespace Commons.NumberTheory.Mertens

/-! ## Sharp first-Mertens inequality

We prove, for every real `x ≥ 2`,
`Σ_{p ≤ x} (log p)/p ≤ log x`.  The proof is elementary:

* at the integers `n`, `log(n!) = Σ_p log p · v_p(n!)` (Legendre) gives the identity
  `n·S(n) = log(n!) − T(n) + F(n)` with `T` (tail of Legendre) and `F` (fractional
  parts) both explicit sums over the primes `≤ n`;
* lower bounding `T(n) − F(n) = Σ_p log p (v_p(n!) − n/p)` by `n·Σ_{p≤√n} log p/p² − θ(n) − θ(√n)`
  and upper bounding `log(n!) − n log n` (trapezoid/Stirling) yields
  `S(n) ≤ log n` for every `n ≥ 100` (a short verification with the elementary bound
  `θ(y) ≤ (log 3)·y` and certified decimal bounds for `log 2, log 3, log 5`);
* the remaining integers `2 ≤ n ≤ 99` are checked exactly, prime by prime, by raising
  the inequality `∏_{p ≤ n} p^{1/p} ≤ n` to integer powers.
-/

/-- `Σ_{p ≤ n} log p / p` at the integer `n` (`n.primesLE`). -/
private def msNatSum (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)

/-- `Σ_{p ≤ n} ⌊n/p⌋·log p`, first Legendre term. -/
private def msFloor (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} (n/p − ⌊n/p⌋)·log p`, fractional-part correction. -/
private def msFrac (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} Σ_{i ≥ 2, p^i ≤ n} ⌊n/p^i⌋·log p`, tail of Legendre's formula. -/
private def msTail (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} log p / p²`. -/
private def msSqSum (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) ^ 2)

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
      ∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
  rw [log_factorial_eq_sum_factorization_log]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hfac := Nat.factorization_factorial (Nat.prime_of_mem_primesLE hp) (n := n) (b := n + 1)
  have hlog : Nat.log p n < n + 1 := by
    exact Nat.lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n)
  rw [hfac hlog]
  rw [Nat.cast_sum]

private lemma sum_Ico_succ_split {R : Type*} [AddCommMonoid R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Ico 1 (n + 1), f i) = f 1 + ∑ i ∈ Finset.Ico 2 (n + 1), f i := by
  have hEq : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
    ext i
    rw [mem_Ico, mem_insert, mem_Ico]
    constructor
    · intro h
      by_cases hi : i = 1
      · exact Or.inl hi
      · apply Or.inr
        exact ⟨by omega, h.2⟩
    · intro h
      rcases h with h | h
      · constructor <;> omega
      · constructor <;> omega
  rw [hEq, Finset.sum_insert]
  simp

/-- Legendre's formula split into the `i = 1` term and the tail. -/
private lemma log_factorial_eq_floor_add_tail (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = msFloor n + msTail n := by
  unfold msFloor msTail
  rw [log_factorial_eq_sum_legendre]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [sum_Ico_succ_split (R := ℝ) (f := fun i => ((n / p ^ i : ℕ) : ℝ)) hn]
  rw [add_mul]
  norm_num [pow_one]

/-- `n · Σ_{p ≤ n} log p/p = (Σ ⌊n/p⌋·log p) + (Σ (n/p − ⌊n/p⌋)·log p)`. -/
private lemma n_mul_msNatSum_eq_floor_add_frac (n : ℕ) :
    (n : ℝ) * msNatSum n = msFloor n + msFrac n := by
  unfold msNatSum msFloor msFrac
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : (p : ℝ) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    linarith
  field_simp [hp0]
  ring

/-- Core identity: `n·S(n) = log(n!) − T(n) + F(n)`. -/
private lemma n_mul_msNatSum_eq_logFac_sub (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * msNatSum n = Real.log (n.factorial : ℝ) - msTail n + msFrac n := by
  rw [n_mul_msNatSum_eq_floor_add_frac, log_factorial_eq_floor_add_tail n hn]
  ring

/-- `Σ_{p ≤ n} log p / p²` is nonneg and sums only nonneg terms. -/
private lemma msSqSum_nonneg (n : ℕ) : 0 ≤ msSqSum n := by
  unfold msSqSum
  exact sum_nonneg (fun p hp => div_nonneg (log_nonneg (by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    linarith)) (sq_nonneg (p : ℝ)))

/-- truncation: `Σ_{p ≤ n} logp/p² ≥ Σ_{p ≤ m} logp/p²` when `m ≤ n`. -/
private lemma msSqSum_mono {m n : ℕ} (hmn : m ≤ n) : msSqSum m ≤ msSqSum n := by
  unfold msSqSum
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => div_nonneg (log_nonneg (by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    linarith)) (sq_nonneg (p : ℝ)))
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨le_trans hp.1 hmn, hp.2⟩

/-! ### Trapezoid bound for `log(n!)` -/

/-- `(n + 1/2)·log(1 + 1/n) ≥ 1` for `n ≥ 1` (elementary). -/
private lemma log_one_add_inv_mul_ge (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ((n : ℝ) + (1 : ℝ) / 2) * Real.log (1 + 1 / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hx : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hle := Real.le_log_one_add_of_nonneg (x := (n : ℝ)⁻¹) hx
  have hrew : 2 * (n : ℝ)⁻¹ / ((n : ℝ)⁻¹ + 2) = 2 / (2 * (n : ℝ) + 1) := by
    field_simp [ne_of_gt hnpos]
    ring
  have hlog : 2 / (2 * (n : ℝ) + 1) ≤ Real.log (1 + 1 / (n : ℝ)) := by
    rw [← hrew]
    simpa [one_div] using hle
  have hbase : ((n : ℝ) + (1 : ℝ) / 2) * (2 / (2 * (n : ℝ) + 1)) = 1 := by
    field_simp [ne_of_gt hnpos]
  calc
    (1 : ℝ) ≤ ((n : ℝ) + (1 : ℝ) / 2) * (2 / (2 * (n : ℝ) + 1)) := le_of_eq hbase.symm
    _ ≤ ((n : ℝ) + (1 : ℝ) / 2) * Real.log (1 + 1 / (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Auxiliary quantity `n·log n − n + 1 + (1/2)·log n − log(n!)`. -/
private def tf (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) + 1 + (1 / 2 : ℝ) * Real.log (m : ℝ) -
    Real.log ((m.factorial : ℕ) : ℝ)

/-- `tf 1 = 0`. -/
private lemma tf_one : tf 1 = 0 := by
  simp [tf, Nat.factorial_one]

/-- Step difference of `tf`. -/
private lemma tf_step (m : ℕ) (hm : 1 ≤ m) :
    tf (m + 1) - tf m = ((m : ℝ) + (1 : ℝ) / 2) * Real.log (1 + 1 / (m : ℝ)) - 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hfac1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  have hfaclog : Real.log (((m + 1).factorial : ℕ) : ℝ) =
      Real.log ((m : ℝ) + 1) + Real.log ((m.factorial : ℕ) : ℝ) := by
    rw [hfac1]
    exact Real.log_mul (by linarith) (by exact_mod_cast (Nat.factorial_ne_zero m))
  have hq : (1 + 1 / (m : ℝ)) = (((m : ℝ) + 1) / (m : ℝ)) := by
    field_simp [ne_of_gt hmpos]
  have hlogd : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) = Real.log (1 + 1 / (m : ℝ)) := by
    rw [hq]
    exact (Real.log_div (by linarith) (ne_of_gt hmpos)).symm
  calc
    tf (m + 1) - tf m
        = (((m : ℝ) + (1 : ℝ) / 2) * Real.log (((m + 1 : ℕ) : ℝ)))
            - (((m : ℝ) + (1 : ℝ) / 2) * Real.log (m : ℝ)) - 1 := by
          unfold tf at *
          rw [hfaclog]
          simp only [Nat.cast_add, Nat.cast_one]
          ring_nf
    _ = ((m : ℝ) + (1 : ℝ) / 2) * (Real.log (((m + 1 : ℕ) : ℝ)) - Real.log (m : ℝ)) - 1 := by
          ring
    _ = ((m : ℝ) + (1 : ℝ) / 2) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) - 1 := by
          simp only [Nat.cast_add, Nat.cast_one]
    _ = ((m : ℝ) + (1 : ℝ) / 2) * Real.log (1 + 1 / (m : ℝ)) - 1 := by
          rw [hlogd]

/-- `tf ≥ 0` for all `m ≥ 1`. -/
private lemma tf_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ tf m := by
  induction m with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [tf_one]
      · have hk1 : 1 ≤ k := hk
        have hprev : 0 ≤ tf k := ih hk1
        have hstep := tf_step k hk1
        have hge := log_one_add_inv_mul_ge k hk1
        have : 0 ≤ ((k : ℝ) + (1 : ℝ) / 2) * Real.log (1 + 1 / (k : ℝ)) - 1 := by linarith
        linarith [hstep]

/-- Trapezoid upper bound: `log(n!) ≤ n·log n − n + 1 + (1/2)·log n` for `n ≥ 2`. -/
private lemma log_factorial_le_trapezoid (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + 1 + (1 / 2 : ℝ) * Real.log (n : ℝ) := by
  have h := tf_nonneg n (by omega)
  unfold tf at h
  linarith

/-! ### Bounds for the Legendre correction terms -/

private lemma msNatSum_nonneg (n : ℕ) : 0 ≤ msNatSum n := by
  unfold msNatSum
  refine sum_nonneg (fun p hp => div_nonneg ?_ (Nat.cast_nonneg p))
  have hp2 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp))
  exact log_nonneg hp2

/-- `log p ≥ 0` for a prime `p`. -/
private lemma log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le hp))

/-- `n/p − ⌊n/p⌋ ≤ 1 − 1/p` for primes `p ≥ 2`. -/
private lemma frac_le_one_sub_inv {n p : ℕ} (hp : 2 ≤ p) :
    (n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ) ≤ 1 - 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpnat : 0 < p := by omega
  have hnmod : (n : ℝ) = (p : ℝ) * (((n / p : ℕ) : ℝ)) + (((n % p : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.div_add_mod n p).symm
  have hδ : (n : ℝ) / (p : ℝ) - (((n / p : ℕ) : ℝ)) = (((n % p : ℕ) : ℝ)) / (p : ℝ) := by
    rw [hnmod]; field_simp [hp0.ne']; ring
  rw [hδ]
  have hlt : (((n % p : ℕ) : ℝ)) ≤ (p : ℝ) - 1 := by
    have h1 : n % p ≤ p - 1 := by have := Nat.mod_lt n hpnat; omega
    have h2 : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    have h3 : ((n % p : ℕ) : ℝ) ≤ (((p - 1 : ℕ)) : ℝ) := by exact_mod_cast h1
    linarith
  calc
    (((n % p : ℕ) : ℝ)) / (p : ℝ) ≤ ((p : ℝ) - 1) / (p : ℝ) :=
      div_le_div_of_nonneg_right hlt (le_of_lt hp0)
    _ = 1 - 1 / (p : ℝ) := by field_simp [hp0.ne']

/-- Upper bound for the fractional-part correction. -/
private lemma msFrac_le (n : ℕ) :
    msFrac n ≤ Chebyshev.theta (n : ℝ) - msNatSum n := by
  have hθ : Chebyshev.theta (n : ℝ) = ∑ p ∈ n.primesLE, Real.log (p : ℝ) :=
    Chebyshev.theta_eq_sum_primesLE_log n
  have hterm : ∀ p ∈ n.primesLE,
      (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ) ≤
        Real.log (p : ℝ) - Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg hpprime
    have hbound := frac_le_one_sub_inv (n := n) hp2
    have hrw : (1 - 1 / (p : ℝ)) * Real.log (p : ℝ) =
        Real.log (p : ℝ) - Real.log (p : ℝ) / (p : ℝ) := by
      field_simp
    rw [← hrw]
    exact mul_le_mul_of_nonneg_right hbound hlog
  calc
    msFrac n = ∑ p ∈ n.primesLE,
        (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ) := rfl
    _ ≤ ∑ p ∈ n.primesLE, (Real.log (p : ℝ) - Real.log (p : ℝ) / (p : ℝ)) :=
        sum_le_sum hterm
    _ = (∑ p ∈ n.primesLE, Real.log (p : ℝ)) - ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
        rw [Finset.sum_sub_distrib]
    _ = Chebyshev.theta (n : ℝ) - msNatSum n := by rw [← hθ]; rfl

/-- `⌊n/p²⌋ ≥ n/p² − 1` (as reals). -/
private lemma natDiv_pow_two_ge {n p : ℕ} (hp : 0 < p) :
    (n : ℝ) / ((p : ℝ) ^ 2) - 1 ≤ ((n / p ^ 2 : ℕ) : ℝ) := by
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hq : ((p : ℝ) ^ 2) ≠ 0 := ne_of_gt hp2
  have hd : p ^ 2 * (n / p ^ 2) + n % p ^ 2 = n := Nat.div_add_mod n (p ^ 2)
  have hcast : (n : ℝ) = ((p : ℝ) ^ 2) * (((n / p ^ 2 : ℕ) : ℝ)) + ((n % p ^ 2 : ℕ) : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hd
    push_cast at h
    linarith
  have hmod : (0 : ℝ) ≤ ((n % p ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmodlt : ((n % p ^ 2 : ℕ) : ℝ) ≤ (p : ℝ) ^ 2 := by
    have h := Nat.mod_lt n (show 0 < p ^ 2 by positivity)
    have h' : ((n % p ^ 2 : ℕ) : ℝ) < (((p ^ 2 : ℕ)) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hrew : (n : ℝ) / ((p : ℝ) ^ 2) - 1 = ((n : ℝ) - (p : ℝ) ^ 2) / ((p : ℝ) ^ 2) := by
    field_simp [hq]
  rw [hrew, div_le_iff₀ hp2]
  nlinarith [hcast, hmod, hmodlt]

/-- Nonnegativity of the truncated Legendre inner sum. -/
private lemma inner_tail_nonneg (n p : ℕ) :
    0 ≤ ∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ) :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Lower bound for the Legendre tail: `msTail n ≥ n·S2(√n) − θ(√n)`. -/
private lemma msTail_ge (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * msSqSum (Nat.sqrt n) - Chebyshev.theta ((Nat.sqrt n : ℕ) : ℝ) ≤ msTail n := by
  set m := Nat.sqrt n with hm
  have hmn : m ≤ n := Nat.sqrt_le_self n
  have hθ : Chebyshev.theta ((m : ℕ) : ℝ) = ∑ p ∈ m.primesLE, Real.log (p : ℝ) :=
    Chebyshev.theta_eq_sum_primesLE_log m
  -- step 1: restrict the outer sum to `m.primesLE`
  have hstep1 : (∑ p ∈ m.primesLE,
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) ≤ msTail n := by
    unfold msTail
    refine Finset.sum_le_sum_of_subset_of_nonneg (s := m.primesLE) (t := n.primesLE)
      (f := fun p : ℕ => ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) : ℝ)) ?_ ?_
    · intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨le_trans hp.1 hmn, hp.2⟩
    · intro p hp _
      exact mul_nonneg (inner_tail_nonneg n p) (log_prime_nonneg (Nat.mem_primesLE.mp hp).2)
  -- step 2: termwise lower bound
  have hstep2 : (∑ p ∈ m.primesLE, ((n : ℝ) / ((p : ℝ) ^ 2) - 1) * Real.log (p : ℝ)) ≤
      ∑ p ∈ m.primesLE,
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
    refine sum_le_sum (fun p hp => ?_)
    have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg (Nat.mem_primesLE.mp hp).2
    have hmem : 2 ∈ Finset.Ico 2 (n + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hinner : ((n / p ^ 2 : ℕ) : ℝ) ≤
        ∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ) := by
      simpa using Finset.single_le_sum (f := fun i => ((n / p ^ i : ℕ) : ℝ))
        (fun i hi => Nat.cast_nonneg _) hmem
    have hge := natDiv_pow_two_ge (n := n) (p := p) (Nat.Prime.pos (Nat.mem_primesLE.mp hp).2)
    exact mul_le_mul_of_nonneg_right (le_trans hge hinner) hlog
  -- step 3: evaluate the lower sum
  have hstep3 : (∑ p ∈ m.primesLE, ((n : ℝ) / ((p : ℝ) ^ 2) - 1) * Real.log (p : ℝ))
      = n * msSqSum m - Chebyshev.theta ((m : ℕ) : ℝ) := by
    have hsum : (∑ p ∈ m.primesLE, ((n : ℝ) / ((p : ℝ) ^ 2) - 1) * Real.log (p : ℝ))
        = ∑ p ∈ m.primesLE,
            ((Real.log (p : ℝ) / (p : ℝ) ^ (2:ℕ)) * (n : ℝ) - Real.log (p : ℝ)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp0 : (p : ℝ) ≠ 0 := by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2)
        linarith
      field_simp [hp0]
    rw [hsum, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hθ]
    simp only [msSqSum]
    ring
  linarith [hstep1, hstep2, hstep3.le]

/-- Key lower bound: `msTail n − msFrac n ≥ n·S2(√n) − θ(√n) − θ(n)`. -/
private lemma tail_sub_frac_ge (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * msSqSum (Nat.sqrt n) - Chebyshev.theta ((Nat.sqrt n : ℕ) : ℝ)
      - Chebyshev.theta (n : ℝ) ≤ msTail n - msFrac n := by
  have h1 := msTail_ge n hn
  have h2 := msFrac_le n
  have h3 := msNatSum_nonneg n
  linarith

/-! ### Numeric constants and the analytic case `n ≥ 100` -/

/-- Lower bound constant for `Σ_{p ≤ 5} log p/p²`. -/
private def L2 : ℝ := 35961 / 100000

/-- Upper bound constant for `log 3`. -/
private def U3 : ℝ := 1099 / 1000

private lemma msSqSum_five_ge : L2 ≤ msSqSum 5 := by
  have h5 : (5 : ℕ).primesLE = {2, 3, 5} := by decide
  have hsum : (∑ p ∈ ({2, 3, 5} : Finset ℕ), Real.log (p : ℝ) / ((p : ℝ) ^ 2))
      = Real.log 2 / 4 + Real.log 3 / 9 + Real.log 5 / 25 := by
    norm_num
    ring
  have h2 : (693 : ℝ) / 1000 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have h3 : (1098 : ℝ) / 1000 ≤ Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have h5' : (1609 : ℝ) / 1000 ≤ Real.log 5 := by
    linarith [Real.log_five_gt_d9]
  have e2 : (693 : ℝ) / 4000 ≤ Real.log 2 / 4 := by linarith
  have e3 : (122 : ℝ) / 1000 ≤ Real.log 3 / 9 := by linarith
  have e5 : (1609 : ℝ) / 25000 ≤ Real.log 5 / 25 := by linarith
  have hL : L2 = (693 : ℝ) / 4000 + 122 / 1000 + 1609 / 25000 := by norm_num [L2]
  unfold msSqSum
  rw [h5, hsum, hL]
  linarith

private lemma msSqSum_ge_L2 {m : ℕ} (hm : 5 ≤ m) : L2 ≤ msSqSum m :=
  le_trans msSqSum_five_ge (msSqSum_mono hm)

private lemma log_three_le_U3 : Real.log 3 ≤ U3 := by
  have := Real.log_three_lt_d9
  norm_num [U3] at this ⊢
  linarith

private lemma theta_le_U3 (m : ℕ) : Chebyshev.theta (m : ℝ) ≤ U3 * (m : ℝ) := by
  have h := Commons.NumberTheory.Chebyshev.theta_le_log3_mul m
  have h3 := log_three_le_U3
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith [h, h3, hm0]

private lemma natSqrt_cast_le_sqrt (n : ℕ) : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' n

private lemma sqrt_le_div_ten {n : ℕ} (hn : 100 ≤ n) : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 10 := by
  rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (n : ℝ) / 10)]
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  nlinarith [hn100, hn0]

private lemma half_log_le_sqrt (n : ℕ) : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h := Commons.Analysis.ExpLog.log_le_two_sqrt (Nat.cast_nonneg n)
  linarith

private lemma numeric_key (n : ℕ) (hn : 100 ≤ n) :
    1 + (U3 + 1) * Real.sqrt (n : ℝ) ≤ (n : ℝ) * (1 + L2 - U3) := by
  have hs := sqrt_le_div_ten hn
  have hn100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoef : (1 : ℝ) / 20 ≤ (1 + L2 - U3) - (U3 + 1) / 10 := by norm_num [L2, U3]
  have hU3n : (0 : ℝ) ≤ U3 + 1 := by norm_num [U3]
  nlinarith [hs, hn100, hcoef, mul_nonneg hU3n (sub_nonneg.mpr hs), hU3n]

/-- The analytic case: `Σ_{p ≤ n} log p/p ≤ log n` for all `n ≥ 100`. -/
private lemma analytic_case (n : ℕ) (hn : 100 ≤ n) : msNatSum n ≤ Real.log (n : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hm5 : 5 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; norm_num; omega
  have hS2 : L2 ≤ msSqSum (Nat.sqrt n) := msSqSum_ge_L2 hm5
  have hTF := tail_sub_frac_ge n hn2
  have hθm : Chebyshev.theta ((Nat.sqrt n : ℕ) : ℝ) ≤ U3 * Real.sqrt (n : ℝ) :=
    le_trans (theta_le_U3 (Nat.sqrt n))
      (mul_le_mul_of_nonneg_left (natSqrt_cast_le_sqrt n) (by norm_num [U3]))
  have hθn : Chebyshev.theta (n : ℝ) ≤ U3 * (n : ℝ) := theta_le_U3 n
  have hkey := numeric_key n hn
  have hloghalf := half_log_le_sqrt n
  have hs1 : (n : ℝ) * L2 ≤ (n : ℝ) * msSqSum (Nat.sqrt n) :=
    mul_le_mul_of_nonneg_left hS2 (Nat.cast_nonneg n)
  have hmix : -(n : ℝ) + 1 + (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ msTail n - msFrac n := by
    have hmid : -(n : ℝ) + 1 + (1 / 2 : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) * msSqSum (Nat.sqrt n) - Chebyshev.theta ((Nat.sqrt n : ℕ) : ℝ)
          - Chebyshev.theta (n : ℝ) := by
      nlinarith [hs1, hθm, hθn, hkey, hloghalf]
    linarith [hTF]
  have hident := n_mul_msNatSum_eq_logFac_sub n (by omega)
  have htra := log_factorial_le_trapezoid n hn2
  have hfinal : (n : ℝ) * msNatSum n ≤ (n : ℝ) * Real.log (n : ℝ) := by
    nlinarith [hident, htra, hmix]
  exact le_of_mul_le_mul_left hfinal (by exact_mod_cast (by omega : 0 < n))

/-! ### The small primes `2 ≤ p ≤ 97` -/

/-- Rational envelope of `q^{1/q}` for primes `q ≤ 97`.  The constants are chosen so that
`b q ^ q ≥ q` and `∏_{q ≤ p} b q ≤ p` for every prime `p ≤ 97`. -/
private def b (q : ℕ) : ℝ :=
  if q = 2 ∨ q = 3 ∨ q = 5 then 3/2
  else if q = 7 then 4/3
  else if q = 11 ∨ q = 13 then 5/4
  else if 17 ≤ q ∧ q ≤ 37 then 6/5
  else 10/9

private lemma b_pos (q : ℕ) : 0 < b q := by
  unfold b
  split_ifs <;> norm_num

/-- If `q ≤ c^q` with `c > 0` then `log q/q ≤ log c`. -/
private lemma log_div_le_log_of_pow_ge {q : ℕ} (hq : 1 ≤ q) {c : ℝ} (hc : 0 < c)
    (h : (q : ℝ) ≤ c ^ q) :
    Real.log (q : ℝ) / (q : ℝ) ≤ Real.log c := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  calc
    Real.log (q : ℝ) / (q : ℝ) ≤ Real.log (c ^ q) / (q : ℝ) :=
      div_le_div_of_nonneg_right (Real.log_le_log hqpos h) (le_of_lt hqpos)
    _ = Real.log c := by
      rw [Real.log_pow]
      field_simp [hq0]

/-- `log q / q ≤ log (b q)` for every prime `q ≤ 97`. -/
private lemma term_bound (q : ℕ) (hq : q.Prime) (hle : q ≤ 97) :
    Real.log (q : ℝ) / (q : ℝ) ≤ Real.log (b q) := by
  have hq2 : 2 ≤ q := hq.two_le
  interval_cases q <;>
    first
      | exact absurd hq (by decide)
      | (refine log_div_le_log_of_pow_ge (by norm_num) (b_pos _) ?_
         norm_num [b])

private lemma prod_le_2 : ∏ q ∈ (2 : ℕ).primesLE, b q ≤ (2 : ℝ) := by
  rw [show (2 : ℕ).primesLE = ({2} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_3 : ∏ q ∈ (3 : ℕ).primesLE, b q ≤ (3 : ℝ) := by
  rw [show (3 : ℕ).primesLE = ({2,3} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_5 : ∏ q ∈ (5 : ℕ).primesLE, b q ≤ (5 : ℝ) := by
  rw [show (5 : ℕ).primesLE = ({2,3,5} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_7 : ∏ q ∈ (7 : ℕ).primesLE, b q ≤ (7 : ℝ) := by
  rw [show (7 : ℕ).primesLE = ({2,3,5,7} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_11 : ∏ q ∈ (11 : ℕ).primesLE, b q ≤ (11 : ℝ) := by
  rw [show (11 : ℕ).primesLE = ({2,3,5,7,11} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_13 : ∏ q ∈ (13 : ℕ).primesLE, b q ≤ (13 : ℝ) := by
  rw [show (13 : ℕ).primesLE = ({2,3,5,7,11,13} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_17 : ∏ q ∈ (17 : ℕ).primesLE, b q ≤ (17 : ℝ) := by
  rw [show (17 : ℕ).primesLE = ({2,3,5,7,11,13,17} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_19 : ∏ q ∈ (19 : ℕ).primesLE, b q ≤ (19 : ℝ) := by
  rw [show (19 : ℕ).primesLE = ({2,3,5,7,11,13,17,19} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_23 : ∏ q ∈ (23 : ℕ).primesLE, b q ≤ (23 : ℝ) := by
  rw [show (23 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_29 : ∏ q ∈ (29 : ℕ).primesLE, b q ≤ (29 : ℝ) := by
  rw [show (29 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_31 : ∏ q ∈ (31 : ℕ).primesLE, b q ≤ (31 : ℝ) := by
  rw [show (31 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_37 : ∏ q ∈ (37 : ℕ).primesLE, b q ≤ (37 : ℝ) := by
  rw [show (37 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_41 : ∏ q ∈ (41 : ℕ).primesLE, b q ≤ (41 : ℝ) := by
  rw [show (41 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_43 : ∏ q ∈ (43 : ℕ).primesLE, b q ≤ (43 : ℝ) := by
  rw [show (43 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_47 : ∏ q ∈ (47 : ℕ).primesLE, b q ≤ (47 : ℝ) := by
  rw [show (47 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_53 : ∏ q ∈ (53 : ℕ).primesLE, b q ≤ (53 : ℝ) := by
  rw [show (53 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_59 : ∏ q ∈ (59 : ℕ).primesLE, b q ≤ (59 : ℝ) := by
  rw [show (59 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_61 : ∏ q ∈ (61 : ℕ).primesLE, b q ≤ (61 : ℝ) := by
  rw [show (61 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_67 : ∏ q ∈ (67 : ℕ).primesLE, b q ≤ (67 : ℝ) := by
  rw [show (67 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_71 : ∏ q ∈ (71 : ℕ).primesLE, b q ≤ (71 : ℝ) := by
  rw [show (71 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_73 : ∏ q ∈ (73 : ℕ).primesLE, b q ≤ (73 : ℝ) := by
  rw [show (73 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_79 : ∏ q ∈ (79 : ℕ).primesLE, b q ≤ (79 : ℝ) := by
  rw [show (79 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_83 : ∏ q ∈ (83 : ℕ).primesLE, b q ≤ (83 : ℝ) := by
  rw [show (83 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_89 : ∏ q ∈ (89 : ℕ).primesLE, b q ≤ (89 : ℝ) := by
  rw [show (89 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89} : Finset ℕ) by decide]
  norm_num [b]

private lemma prod_le_97 : ∏ q ∈ (97 : ℕ).primesLE, b q ≤ (97 : ℝ) := by
  rw [show (97 : ℕ).primesLE = ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} : Finset ℕ) by decide]
  norm_num [b]

/-- `∏_{q ≤ p} b q ≤ p` for every prime `p ≤ 97`. -/
private lemma prod_b_le (p : ℕ) (hp : p.Prime) (hle : p ≤ 97) :
    ∏ q ∈ p.primesLE, b q ≤ (p : ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p <;>
    first
      | exact absurd hp (by decide)
      | exact prod_le_2
      | exact prod_le_3
      | exact prod_le_5
      | exact prod_le_7
      | exact prod_le_11
      | exact prod_le_13
      | exact prod_le_17
      | exact prod_le_19
      | exact prod_le_23
      | exact prod_le_29
      | exact prod_le_31
      | exact prod_le_37
      | exact prod_le_41
      | exact prod_le_43
      | exact prod_le_47
      | exact prod_le_53
      | exact prod_le_59
      | exact prod_le_61
      | exact prod_le_67
      | exact prod_le_71
      | exact prod_le_73
      | exact prod_le_79
      | exact prod_le_83
      | exact prod_le_89
      | exact prod_le_97


/-- `Σ_{p ≤ n} log p/p ≤ log n` for primes `p ≤ 97`. -/
private lemma prime_case (p : ℕ) (hp : p.Prime) (hle : p ≤ 97) :
    msNatSum p ≤ Real.log (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    msNatSum p = ∑ q ∈ p.primesLE, Real.log (q : ℝ) / (q : ℝ) := rfl
    _ ≤ ∑ q ∈ p.primesLE, Real.log (b q) := by
        refine sum_le_sum (fun q hq => ?_)
        have hq' := Nat.mem_primesLE.mp hq
        exact term_bound q hq'.2 (le_trans hq'.1 hle)
    _ = Real.log (∏ q ∈ p.primesLE, b q) :=
        (Real.log_prod (fun q _ => ne_of_gt (b_pos q))).symm
    _ ≤ Real.log (p : ℝ) :=
        Real.log_le_log (Finset.prod_pos (fun q _ => b_pos q)) (prod_b_le p hp hle)

/-- `n.primesLE = (n-1).primesLE` for non-prime `n ≥ 1`. -/
private lemma primesLE_pred_eq {n : ℕ} (hn : 1 ≤ n) (hp : ¬ n.Prime) :
    n.primesLE = (n - 1).primesLE := by
  ext q
  rw [Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    rcases lt_or_eq_of_le h.1 with h' | h'
    · omega
    · exact absurd (h'.symm ▸ h.2) hp
  · intro h
    exact ⟨le_trans h.1 (Nat.sub_le n 1), h.2⟩

/-- `Σ_{p ≤ n} log p/p ≤ log n` for all `2 ≤ n ≤ 99`. -/
private lemma small_case (n : ℕ) (hn2 : 2 ≤ n) (hn99 : n ≤ 99) :
    msNatSum n ≤ Real.log (n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · have hn97 : n ≤ 97 := by
        by_contra h
        rw [not_le] at h
        interval_cases n <;> exact absurd hp (by decide)
      exact prime_case n hp hn97
    · have hn4 : 4 ≤ n := by
        by_contra h
        rw [not_le] at h
        interval_cases n <;> exact hp (by decide)
      have hprev : msNatSum (n - 1) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
        ih (n - 1) (by omega) (by omega) (by omega)
      have hlog : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
        refine Real.log_le_log (by exact_mod_cast (by omega : 0 < n - 1)) ?_
        exact_mod_cast (Nat.sub_le n 1)
      calc
        msNatSum n = msNatSum (n - 1) := by
          unfold msNatSum
          rw [primesLE_pred_eq (by omega) hp]
        _ ≤ Real.log ((n - 1 : ℕ) : ℝ) := hprev
        _ ≤ Real.log (n : ℝ) := hlog

/-- The main integer statement: `Σ_{p ≤ n} log p/p ≤ log n` for all `n ≥ 2`. -/
private lemma nat_case (n : ℕ) (hn : 2 ≤ n) : msNatSum n ≤ Real.log (n : ℝ) := by
  by_cases h : n ≤ 99
  · exact small_case n hn h
  · rw [not_le] at h
    exact analytic_case n (by omega)

/-! ## The real theorem -/

/-- Sharp first-Mertens inequality: `Σ_{p ≤ x} (log p)/p ≤ log x` for every real `x ≥ 2`
(primes `p ≤ x`, sum in `x.primesLE`).  True for all `x ≥ 2` (margin `≥ (1/2) log 2` at
`x = 2`, tending to the first-Mertens constant ~1.33); needs an effective first-Mertens
estimate (e.g. effective PNT/Chebyshev/Mertens bounds + finite check). -/
theorem sum_log_prime_div_prime_le_log (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log x := by
  have hn2 : 2 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    norm_num at h
    exact h
  have hxpos : 0 < x := by linarith
  have hle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  calc
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ)) = msNatSum ⌊x⌋₊ := rfl
    _ ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := nat_case ⌊x⌋₊ hn2
    _ ≤ Real.log x := Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) hle
