import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds
import Submission.Commons.Analysis.ExpLog.sum_log_sq_inv_le_four

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset Real Filter
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

/-!
# First Mertens theorem: `|Σ_{p ≤ x} log p / p − log x|` is bounded

We prove the bounded form of the first Mertens theorem: there is a constant `C` with
`|logDiv x − log x| ≤ C` for every `x ≥ 2`.
The proof is the classical elementary argument via `log (n!)`: Legendre's formula and
an estimate of `log (n!)` by an integral.
-/

noncomputable section

/-- `log p / p` summed over primes `p ≤ n` (the value of `logDiv` at the integer `n`). -/
private def fmbNatLogDiv (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)

/-- `Σ_{p ≤ n} ⌊n/p⌋ · log p` (the first Legendre term). -/
private def fmbFloor (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} (n/p − ⌊n/p⌋) · log p`, the fractional-part correction. -/
private def fmbFrac (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} Σ_{i ≥ 2, p^i ≤ n} ⌊n/p^i⌋ · log p`, the tail of Legendre's formula. -/
private def fmbTail (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE,
    (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)

/-! ## Legendre's formula and elementary identities -/

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
  simp [hn]

/-- Legendre's formula split into the `i = 1` term and the tail. -/
private lemma log_factorial_eq_floor_add_tail (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = fmbFloor n + fmbTail n := by
  unfold fmbFloor fmbTail
  rw [log_factorial_eq_sum_legendre]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [sum_Ico_succ_split (R := ℝ) (f := fun i => ((n / p ^ i : ℕ) : ℝ)) hn]
  rw [add_mul]
  norm_num [pow_one]

/-- `logDiv` at an integer equals the sum over primes `≤ n`. -/
private lemma logDiv_eq_sum_nat {n : ℕ} :
    logDiv (n : ℝ) = ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
  unfold logDiv
  simp [Nat.floor_natCast]

/-- `n · Σ log p/p = (Σ ⌊n/p⌋ log p) + (Σ (n/p − ⌊n/p⌋) log p)`. -/
private lemma n_mul_logDivNat_eq_floor_add_frac (n : ℕ) :
    (n : ℝ) * fmbNatLogDiv n = fmbFloor n + fmbFrac n := by
  unfold fmbNatLogDiv fmbFloor fmbFrac
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : (p : ℝ) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp))
    linarith
  field_simp [hp0]
  ring

/-! ## Bounds for the correction terms -/

private lemma nat_div_cast_le (a b : ℕ) (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have h1 : (a / b : ℕ) * b ≤ a := Nat.div_mul_le_self a b
  have h1r : ((a / b : ℕ) : ℝ) * (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact h1r

private lemma geom_Ico_two_le_two_mul_sq {r : ℝ} (hr0 : 0 ≤ r) (hrle : r ≤ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.Ico 2 (n + 1), r ^ i) ≤ 2 * r ^ 2 := by
  have hr1 : r ≠ 1 := by linarith
  have h1mr : 0 < 1 - r := by linarith
  calc
    (∑ i ∈ Finset.Ico 2 (n + 1), r ^ i) = (r ^ 2 - r ^ (n + 1)) / (1 - r) := geom_sum_Ico' hr1 (by omega)
    _ ≤ r ^ 2 / (1 - r) := by
      rw [div_le_div_iff₀ h1mr h1mr]
      have hnn : 0 ≤ r ^ (n + 1) := pow_nonneg hr0 (n + 1)
      nlinarith
    _ ≤ 2 * r ^ 2 := by
      rw [div_le_iff₀ h1mr]
      have hfac : 0 ≤ r ^ 2 * (1 - 2 * r) := by
        exact mul_nonneg (sq_nonneg r) (by linarith)
      nlinarith

private lemma log_sq_inv_sum_le_four (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Icc 2 n, Real.log (k : ℝ) / ((k : ℝ) ^ 2)) ≤ 4 := by
  have h := Commons.Analysis.ExpLog.sum_log_sq_inv_le_four n hn
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_two]

/-! ### The fractional-part term -/

private lemma frac_pp_bound {n p : ℕ} (hp : 2 ≤ p) :
    0 ≤ ((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ) ∧
      ((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ) ≤ 1 := by
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0' : 0 < (p : ℝ) := by linarith
  have hpnat : 0 < p := by omega
  have hnmod : (n : ℝ) = (p : ℝ) * (((n / p : ℕ) : ℝ)) + (((n % p : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.div_add_mod n p).symm
  have hδ : ((n : ℝ) / (p : ℝ)) - (((n / p : ℕ) : ℝ)) = (((n % p : ℕ) : ℝ)) / (p : ℝ) := by
    rw [hnmod]
    field_simp [hp0'.ne']
    ring
  constructor
  · rw [hδ]
    exact div_nonneg (Nat.cast_nonneg (n % p)) (le_of_lt hp0')
  · rw [hδ]
    rw [div_le_iff₀ hp0']
    have hlt : (((n % p : ℕ) : ℝ)) < (p : ℝ) := by exact_mod_cast (Nat.mod_lt n hpnat)
    nlinarith

private lemma log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.one_le hp)
  exact Real.log_nonneg hp1

private lemma fmbFrac_nonneg (n : ℕ) : 0 ≤ fmbFrac n := by
  unfold fmbFrac
  exact Finset.sum_nonneg (fun p hp => by
    have hle2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)
    exact mul_nonneg (frac_pp_bound hle2).1 (log_prime_nonneg (Nat.prime_of_mem_primesLE hp)))

private lemma fmbFrac_le_log4_mul {n : ℕ} (hn : 1 ≤ n) : fmbFrac n ≤ Real.log 4 * (n : ℝ) := by
  unfold fmbFrac
  have hsumle : (∑ p ∈ n.primesLE, (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ))
      ≤ ∑ p ∈ n.primesLE, Real.log (p : ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hle2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)
    have hδ := (frac_pp_bound (n := n) (p := p) hle2).2
    have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg (Nat.prime_of_mem_primesLE hp)
    calc
      (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)
          ≤ 1 * Real.log (p : ℝ) := by
            exact mul_le_mul_of_nonneg_right hδ hlog
      _ = Real.log (p : ℝ) := by ring
  have hθ : Chebyshev.theta (n : ℝ) = ∑ p ∈ n.primesLE, Real.log (p : ℝ) :=
    Chebyshev.theta_eq_sum_primesLE_log n
  calc
    (∑ p ∈ n.primesLE, (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ))
        ≤ ∑ p ∈ n.primesLE, Real.log (p : ℝ) := hsumle
    _ = Chebyshev.theta (n : ℝ) := hθ.symm
    _ ≤ Real.log 4 * (n : ℝ) := by
      exact Chebyshev.theta_le_log4_mul_x (by exact_mod_cast (Nat.zero_le n))

/-! ### The tail term -/

private lemma inv_sq_sum_ge {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ (1 : ℝ) / (p : ℝ) ∧ (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  constructor
  · exact div_nonneg zero_le_one (le_of_lt hp0)
  · rw [div_le_div_iff₀ hp0 (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact_mod_cast hp

private lemma one_div_pow_real {p : ℕ} (i : ℕ) (hp0 : (p : ℝ) ≠ 0) :
    (1 / (p : ℝ) ^ i) = ((1 : ℝ) / (p : ℝ)) ^ i := by
  rw [div_pow, one_pow]

private lemma inner_tail_bound {n p : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.Ico 2 (n + 1), (((n / p ^ i : ℕ) : ℝ))) ≤ (n : ℝ) * 2 / ((p : ℝ) ^ 2) := by
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0r : (p : ℝ) ≠ 0 := by linarith
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hgeom := geom_Ico_two_le_two_mul_sq (r := (1 : ℝ) / (p : ℝ))
    (inv_sq_sum_ge hp).1 (inv_sq_sum_ge hp).2 n hn
  calc
    (∑ i ∈ Finset.Ico 2 (n + 1), (((n / p ^ i : ℕ) : ℝ)))
        ≤ ∑ i ∈ Finset.Ico 2 (n + 1), (n : ℝ) * (((1 : ℝ) / (p : ℝ)) ^ i) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hb0 : 0 < p ^ i := pow_pos (by omega) i
          have hle := nat_div_cast_le n (p ^ i) hb0
          have hpowc : (((p ^ i : ℕ) : ℝ)) = (p : ℝ) ^ i := by norm_num
          rw [hpowc] at hle
          have hdiv : (n : ℝ) / (p : ℝ) ^ i = (n : ℝ) * (((1 : ℝ) / (p : ℝ)) ^ i) := by
            rw [← one_div_pow_real i hp0r]
            field_simp [pow_ne_zero i hp0r]
          calc
            (((n / p ^ i : ℕ) : ℝ)) ≤ (n : ℝ) / (p : ℝ) ^ i := hle
            _ = (n : ℝ) * (((1 : ℝ) / (p : ℝ)) ^ i) := hdiv
    _ = (n : ℝ) * (∑ i ∈ Finset.Ico 2 (n + 1), (((1 : ℝ) / (p : ℝ)) ^ i)) := by
          rw [Finset.mul_sum]
    _ ≤ (n : ℝ) * (2 * ((1 : ℝ) / (p : ℝ)) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hgeom hn0
    _ = (n : ℝ) * 2 / ((p : ℝ) ^ 2) := by
          have hrew : (n : ℝ) * (2 * ((1 : ℝ) / (p : ℝ)) ^ 2) = (n : ℝ) * 2 / ((p : ℝ) ^ 2) := by
            rw [div_pow, one_pow]
            field_simp [hp0r]
          exact hrew

private lemma fmbTail_nonneg (n : ℕ) : 0 ≤ fmbTail n := by
  unfold fmbTail
  exact Finset.sum_nonneg (fun p hp => by
    refine mul_nonneg ?_ (log_prime_nonneg (Nat.prime_of_mem_primesLE hp))
    exact Finset.sum_nonneg (fun i hi => by exact_mod_cast (Nat.zero_le (n / p ^ i))))

private lemma prime_subset_Icc_two {n : ℕ} (hn : 2 ≤ n) : n.primesLE ⊆ Finset.Icc 2 n := by
  intro p hp
  rw [Nat.mem_primesLE] at hp
  rw [mem_Icc]
  exact ⟨Nat.Prime.two_le hp.2, hp.1⟩

private lemma fmbTail_le_eight_mul {n : ℕ} (hn : 2 ≤ n) : fmbTail n ≤ 8 * (n : ℝ) := by
  unfold fmbTail
  have h1 : (∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 2 (n + 1), (((n / p ^ i : ℕ) : ℝ))) * Real.log (p : ℝ))
      ≤ ∑ p ∈ n.primesLE, ((n : ℝ) * 2 / ((p : ℝ) ^ 2)) * Real.log (p : ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)
    have hin := inner_tail_bound (p := p) hp2 hn
    have hlog : 0 ≤ Real.log (p : ℝ) := log_prime_nonneg (Nat.prime_of_mem_primesLE hp)
    exact mul_le_mul_of_nonneg_right hin hlog
  have h2e : (∑ p ∈ n.primesLE, ((n : ℝ) * 2 / ((p : ℝ) ^ 2)) * Real.log (p : ℝ))
      = (n : ℝ) * 2 * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := by
    calc
      (∑ p ∈ n.primesLE, ((n : ℝ) * 2 / ((p : ℝ) ^ 2)) * Real.log (p : ℝ))
          = ∑ p ∈ n.primesLE, (n : ℝ) * 2 * (Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := by
              refine Finset.sum_congr rfl (fun p hp => ?_)
              have hp0 : (p : ℝ) ≠ 0 := by
                have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.prime_of_mem_primesLE hp)
                have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
                linarith
              field_simp [hp0]
      _ = (n : ℝ) * 2 * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := by
              rw [Finset.mul_sum]
  have h3 : (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) ^ 2))
      ≤ ∑ k ∈ Finset.Icc 2 n, Real.log (k : ℝ) / ((k : ℝ) ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (prime_subset_Icc_two hn) (fun k hk _ => ?_)
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by linarith [show (2 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk2]
    exact div_nonneg (Real.log_nonneg hk1) (sq_pos_of_ne_zero (by linarith : (k : ℝ) ≠ 0)).le
  calc
    (∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 2 (n + 1), (((n / p ^ i : ℕ) : ℝ))) * Real.log (p : ℝ))
        ≤ ∑ p ∈ n.primesLE, ((n : ℝ) * 2 / ((p : ℝ) ^ 2)) * Real.log (p : ℝ) := h1
    _ = (n : ℝ) * 2 * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / ((p : ℝ) ^ 2)) := h2e
    _ ≤ (n : ℝ) * 2 * (∑ k ∈ Finset.Icc 2 n, Real.log (k : ℝ) / ((k : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (n : ℝ) * 2 * 4 := by
          exact mul_le_mul_of_nonneg_left (log_sq_inv_sum_le_four n hn) (by positivity)
    _ = 8 * (n : ℝ) := by ring


/-! ### Assembly: the bound at integers -/

private lemma n_mul_logDivNat_eq_logFac_sub (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * fmbNatLogDiv n = Real.log (n.factorial : ℝ) - fmbTail n + fmbFrac n := by
  rw [n_mul_logDivNat_eq_floor_add_frac, log_factorial_eq_floor_add_tail n hn]
  ring

private lemma logDivNat_sub_log_upper {n : ℕ} (hn : 2 ≤ n) :
    fmbNatLogDiv n - Real.log (n : ℝ) ≤ 1 / 2 + Real.log 4 := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let E : ℝ := Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))
  have hE := Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds (n := n) hn
  have hE2 : E ≤ 1 + Real.log (n : ℝ) := by simpa [E] using hE.2
  have hid : (n : ℝ) * fmbNatLogDiv n = Real.log (n.factorial : ℝ) - fmbTail n + fmbFrac n :=
    n_mul_logDivNat_eq_logFac_sub n hn1
  have htail0 : 0 ≤ fmbTail n := fmbTail_nonneg n
  have hfracl : fmbFrac n ≤ Real.log 4 * (n : ℝ) := fmbFrac_le_log4_mul hn1
  calc
    fmbNatLogDiv n - Real.log (n : ℝ)
        = (((n : ℝ) * fmbNatLogDiv n) - (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ) := by
            field_simp [hn0]
    _ = (Real.log (n.factorial : ℝ) - fmbTail n + fmbFrac n
          - (n : ℝ) * Real.log (n : ℝ)) / (n : ℝ) := by
            rw [hid]
    _ = (-1) + (E - fmbTail n + fmbFrac n) / (n : ℝ) := by
            dsimp [E]
            field_simp [hn0]
            ring
    _ ≤ (-1) + (1 + Real.log (n : ℝ) + Real.log 4 * (n : ℝ)) / (n : ℝ) := by
            have hnumle : E - fmbTail n + fmbFrac n ≤
                1 + Real.log (n : ℝ) + Real.log 4 * (n : ℝ) := by
              linarith [hE2, hfracl, htail0]
            have hd := div_le_div_of_nonneg_right hnumle (le_of_lt hnpos)
            nlinarith
    _ = -1 + (1 + Real.log (n : ℝ)) / (n : ℝ) + Real.log 4 := by
            rw [add_div]
            field_simp [hn0]
            ring
    _ ≤ -1 + (1 / 2 + 1) + Real.log 4 := by
            have h1n : (1 : ℝ) / (n : ℝ) ≤ 1 / 2 := by
              rw [div_le_div_iff₀ hnpos (by norm_num : (0 : ℝ) < 2)]
              norm_num
              exact_mod_cast hn
            have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
            have hlog : Real.log (n : ℝ) / (n : ℝ) ≤ 1 := by
              have hd := div_le_div_of_nonneg_right hlogle (le_of_lt hnpos)
              have hred : ((n : ℝ) - 1) / (n : ℝ) ≤ 1 := by
                rw [div_le_iff₀ hnpos]
                nlinarith
              exact le_trans hd hred
            have hsplit : (1 + Real.log (n : ℝ)) / (n : ℝ) ≤ 1 / 2 + 1 := by
              rw [add_div]
              nlinarith
            nlinarith
    _ = 1 / 2 + Real.log 4 := by ring

private lemma logDivNat_sub_log_lower {n : ℕ} (hn : 2 ≤ n) :
    (-9 : ℝ) ≤ fmbNatLogDiv n - Real.log (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let E : ℝ := Real.log (n.factorial : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))
  have hE := Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds (n := n) hn
  have hE1 : 1 ≤ E := by simpa [E] using hE.1
  have hid : (n : ℝ) * fmbNatLogDiv n = Real.log (n.factorial : ℝ) - fmbTail n + fmbFrac n :=
    n_mul_logDivNat_eq_logFac_sub n hn1
  have hfrac0 : 0 ≤ fmbFrac n := fmbFrac_nonneg n
  have htaill : fmbTail n ≤ 8 * (n : ℝ) := fmbTail_le_eight_mul hn
  calc
    (-9 : ℝ) = (-1) + (-(8 : ℝ)) := by norm_num
    _ ≤ (-1) + (-(fmbTail n)) / (n : ℝ) := by
            have htail : fmbTail n / (n : ℝ) ≤ 8 := by
              have hd := div_le_div_of_nonneg_right htaill (le_of_lt hnpos)
              have hred : (8 * (n : ℝ)) / (n : ℝ) = 8 := by
                field_simp [hn0]
              rw [hred] at hd
              exact hd
            rw [neg_div]
            nlinarith
    _ ≤ (-1) + (E - fmbTail n + fmbFrac n) / (n : ℝ) := by
            have hge : (-(fmbTail n)) / (n : ℝ) ≤ (E - fmbTail n + fmbFrac n) / (n : ℝ) := by
              have hle2 : -(fmbTail n) ≤ E - fmbTail n + fmbFrac n := by linarith [hE1, hfrac0]
              exact div_le_div_of_nonneg_right hle2 (le_of_lt hnpos)
            nlinarith
    _ = fmbNatLogDiv n - Real.log (n : ℝ) := by
            dsimp [E] at *
            field_simp [hn0]
            ring_nf
            rw [hid]
            ring



private lemma logDiv_natCast (n : ℕ) : logDiv (n : ℝ) = fmbNatLogDiv n := by
  rw [logDiv_eq_sum_nat]
  rfl

private lemma fmbNatLogDiv_abs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → |fmbNatLogDiv n - Real.log (n : ℝ)| ≤ C := by
  refine ⟨9 + Real.log 4, ?_, ?_⟩
  · have h4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    positivity
  · intro n hn
    have hu := logDivNat_sub_log_upper (n := n) hn
    have hl := logDivNat_sub_log_lower (n := n) hn
    have h4 : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4))
    rw [abs_le]
    constructor <;> linarith

private lemma logDiv_nat_abs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → |logDiv (n : ℝ) - Real.log (n : ℝ)| ≤ C := by
  rcases fmbNatLogDiv_abs_bound with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, fun n hn => ?_⟩
  simpa [logDiv_natCast] using hC n hn

private lemma logDiv_eq_logDiv_floor (x : ℝ) : logDiv x = logDiv ((⌊x⌋₊ : ℕ) : ℝ) := by
  unfold logDiv
  simp [Nat.floor_natCast]

private lemma abs_log_sub_floor_le_log_two {x : ℝ} (hx : 2 ≤ x) :
    |Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ)| ≤ Real.log 2 := by
  let N : ℕ := ⌊x⌋₊
  have hN2 : 2 ≤ N := by
    dsimp [N]
    simpa using (Nat.floor_mono hx : ⌊(2 : ℝ)⌋₊ ≤ ⌊x⌋₊)
  have hNposR : 0 < ((N : ℕ) : ℝ) := by
    have hNpos : 0 < N := by omega
    exact_mod_cast hNpos
  have hxposR : 0 < x := by linarith
  have hNle : ((N : ℕ) : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le (by linarith)
  have hxlt : x < ((N : ℕ) : ℝ) + 1 := by
    dsimp [N]
    exact Nat.lt_floor_add_one x
  have hxdiv : x / ((N : ℕ) : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNposR]
    nlinarith [hxlt, show (2 : ℝ) ≤ (N : ℕ) by exact_mod_cast hN2]
  have hlognonneg : 0 ≤ Real.log x - Real.log ((N : ℕ) : ℝ) := by
    exact sub_nonneg.mpr (Real.log_le_log hNposR hNle)
  calc
    |Real.log x - Real.log ((N : ℕ) : ℝ)|
        = Real.log x - Real.log ((N : ℕ) : ℝ) := abs_of_nonneg hlognonneg
    _ = Real.log (x / ((N : ℕ) : ℝ)) := by
          rw [Real.log_div (ne_of_gt hxposR) (ne_of_gt hNposR)]
    _ ≤ Real.log 2 := by
          exact Real.log_le_log (div_pos hxposR hNposR) hxdiv
  -- x/hmm: calc is over N; rewrite statement: statement has ((⌊x⌋₊ : ℕ) : ℝ) and N := ⌊x⌋₊ defeq; ok

theorem first_mertens_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Commons.NumberTheory.Mertens.logDiv x - Real.log x| ≤ C := by
  rcases logDiv_nat_abs_bound with ⟨C0, hC0pos, hC0⟩
  refine ⟨C0 + Real.log 2, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  · intro x hx
    let N : ℕ := ⌊x⌋₊
    have hN2 : 2 ≤ N := by
      dsimp [N]
      simpa using (Nat.floor_mono hx : ⌊(2 : ℝ)⌋₊ ≤ ⌊x⌋₊)
    calc
      |logDiv x - Real.log x|
          ≤ |logDiv x - Real.log ((N : ℕ) : ℝ)| + |Real.log ((N : ℕ) : ℝ) - Real.log x| := by
              have hsplit : logDiv x - Real.log x =
                  (logDiv x - Real.log ((N : ℕ) : ℝ)) + (Real.log ((N : ℕ) : ℝ) - Real.log x) := by
                ring
              rw [hsplit]
              exact abs_add_le _ _
      _ ≤ C0 + Real.log 2 := by
              have h1 : |logDiv x - Real.log ((N : ℕ) : ℝ)| ≤ C0 := by
                dsimp [N]
                rw [logDiv_eq_logDiv_floor]
                exact hC0 ⌊x⌋₊ (by simpa using (Nat.floor_mono hx : ⌊(2 : ℝ)⌋₊ ≤ ⌊x⌋₊))
              have h2 : |Real.log ((N : ℕ) : ℝ) - Real.log x| ≤ Real.log 2 := by
                simpa [N, abs_sub_comm] using (abs_log_sub_floor_le_log_two hx)
              linarith

end
end Commons.NumberTheory.Mertens