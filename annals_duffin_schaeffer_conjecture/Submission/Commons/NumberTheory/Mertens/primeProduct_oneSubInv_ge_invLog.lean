import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.NumberTheory.Mertens.corr_sum_le
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds
import Submission.Commons.NumberTheory.PrimeReciprocals.logDiv_100_ge_36
import Submission.Commons.NumberTheory.PrimeReciprocals.primeRecips_100_le

open Finset Real
open scoped BigOperators
open MeasureTheory

namespace Commons.NumberTheory.Mertens

noncomputable section

/-! ## The quantitative deficiency of the first Mertens sum -/

/-- The prime factors of `n!` are exactly the primes `≤ n`. -/
private lemma primeFactors_factorial_eq (n : ℕ) : (n.factorial).factorization.support = n.primesLE := by
  change (n.factorial).primeFactors = n.primesLE
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    exact ⟨(Nat.Prime.dvd_factorial hp).mp hdvd, hp⟩
  · rintro ⟨hpn, hp⟩
    exact ⟨hp, (Nat.Prime.dvd_factorial hp).mpr hpn, Nat.factorial_ne_zero n⟩

/-- Legendre's formula for `log (n!)`. -/
private lemma log_factorial_eq_sum_legendre' (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 1 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, primeFactors_factorial_eq]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
  have hb : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
  rw [Nat.factorization_factorial hpp hb, Nat.cast_sum]

private lemma sum_Ico_succ_split' {R : Type*} [AddCommMonoid R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Ico 1 (n + 1), f i) = f 1 + ∑ i ∈ Finset.Ico 2 (n + 1), f i := by
  have hEq : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
    ext i
    rw [mem_Ico, mem_insert, mem_Ico]
    constructor
    · intro h
      by_cases hi : i = 1
      · exact Or.inl hi
      · exact Or.inr ⟨by omega, h.2⟩
    · rintro (h | h)
      · omega
      · omega
  rw [hEq, Finset.sum_insert (by simp)]

private def tailSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)

private def fracSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)

private def floorSum (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)

private lemma log_factorial_eq_floor_add_tail' (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = floorSum n + tailSum n := by
  unfold floorSum tailSum
  rw [log_factorial_eq_sum_legendre', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [sum_Ico_succ_split' (R := ℝ) (f := fun i => ((n / p ^ i : ℕ) : ℝ)) hn]
  rw [add_mul]
  norm_num

private lemma n_mul_sum_eq_floor_add_frac' (n : ℕ) :
    (n : ℝ) * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)) = floorSum n + fracSum n := by
  unfold floorSum fracSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : (p : ℝ) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2)
    linarith
  field_simp
  ring

/-- Exact identity: `n · Σ log p/p = log (n!) − T + F`. -/
private lemma n_mul_sum_eq_log_factorial' (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ))
      = Real.log (n.factorial : ℝ) - tailSum n + fracSum n := by
  rw [n_mul_sum_eq_floor_add_frac', log_factorial_eq_floor_add_tail' n hn]
  ring

private lemma log_prime_nonneg'' {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le hp))

/-- `⌊n/p^i⌋ ≥ n/p^i - 1` for `p ≥ 1`. -/
private lemma div_pow_ge' (n p i : ℕ) (hp : 1 ≤ p) :
    (n : ℝ)/(p:ℝ)^i - 1 ≤ ((n / p^i : ℕ) : ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hpi : (0:ℝ) < (p:ℝ)^i := pow_pos hp0 i
  have hmod : ((n % p^i : ℕ) : ℝ) < (p:ℝ)^i := by
    have h := Nat.mod_lt n (show 0 < p^i by positivity)
    have hcast : ((n % p^i : ℕ) : ℝ) < ((p^i : ℕ) : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_pow] using hcast
  have hd := Nat.div_add_mod n (p^i)
  have hdc : (n : ℝ) = ((n / p^i : ℕ) : ℝ) * (p:ℝ)^i + ((n % p^i : ℕ) : ℝ) := by
    have := congrArg (fun k : ℕ => (k:ℝ)) hd
    push_cast at this
    linarith [this]
  have h1 : (n:ℝ)/(p:ℝ)^i - ((n / p^i : ℕ) : ℝ) = ((n % p^i : ℕ) : ℝ)/(p:ℝ)^i := by
    rw [hdc]; field_simp; ring
  have h2 : ((n % p^i : ℕ) : ℝ)/(p:ℝ)^i ≤ 1 := by
    rw [div_le_one hpi]; linarith
  linarith

/-- Log bounds for `2, 3, 5`. -/
private lemma log2_bounds : (0.6931471803 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.6931471808 :=
  ⟨le_of_lt Real.log_two_gt_d9, le_of_lt Real.log_two_lt_d9⟩

private lemma log3_bounds : (1.0986122885 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0986122888 :=
  ⟨le_of_lt Real.log_three_gt_d9, le_of_lt Real.log_three_lt_d9⟩

private lemma log5_bounds : (1.6094379123 : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ 1.6094379126 :=
  ⟨le_of_lt Real.log_five_gt_d9, le_of_lt Real.log_five_lt_d9⟩

private lemma log7_lower : (1.9365843 : ℝ) ≤ Real.log 7 := by
  have h2 := Real.log_two_gt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; ring
  have hlog : Real.log 8 - Real.log 7 = Real.log (1 + 1/7) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hub : Real.log (1 + 1/7) ≤ 1/7 := by
    have := Real.log_le_sub_one_of_pos (x := 1 + 1/7) (by norm_num)
    linarith
  rw [h8] at hlog
  linarith

private lemma log7_upper : Real.log 7 ≤ 1.9461083 := by
  have h2 := Real.log_two_lt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; ring
  have hlog : Real.log 8 - Real.log 7 = Real.log (1 + 1/7) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hlb : 2 * (1/7) / ((1/7) + 2) ≤ Real.log (1 + 1/7) :=
    Real.le_log_one_add_of_nonneg (by norm_num)
  have hdd : 2 * (1:ℝ)/7 / ((1:ℝ)/7 + 2) = (2:ℝ)/15 := by norm_num
  rw [h8] at hlog
  linarith

/-- The fixed correction sums (over the pairs `(i,p)` with `i ∈ {2,…,6}`, `p ∈ {2,3,5,7}`
and `p^i ≤ 100`). -/
private def lamSum : ℝ :=
  ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
    (if p^i ≤ 100 then Real.log (p:ℝ)/(p:ℝ)^i else 0)

private def errSum : ℝ :=
  ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
    (if p^i ≤ 100 then Real.log (p:ℝ) else 0)

private lemma lamSum_eval : lamSum = Real.log 2/4 + Real.log 3/9 + Real.log 5/25 + Real.log 7/49
    + Real.log 2/8 + Real.log 3/27 + Real.log 2/16 + Real.log 3/81 + Real.log 2/32 + Real.log 2/64 := by
  unfold lamSum
  norm_num [Finset.sum_Ico_succ_top, Finset.sum_insert, Finset.sum_singleton]
  ring

private lemma errSum_eval : errSum = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7
    + Real.log 2 + Real.log 3 + Real.log 2 + Real.log 3 + Real.log 2 + Real.log 2 := by
  unfold errSum
  norm_num [Finset.sum_Ico_succ_top, Finset.sum_insert, Finset.sum_singleton]
  ring

private lemma lamSum_ge : (0.61 : ℝ) ≤ lamSum := by
  rw [lamSum_eval]
  obtain ⟨h2l, -⟩ := log2_bounds
  obtain ⟨h3l, -⟩ := log3_bounds
  obtain ⟨h5l, -⟩ := log5_bounds
  have h7l := log7_lower
  linarith

private lemma errSum_le : errSum ≤ 10.4 := by
  rw [errSum_eval]
  obtain ⟨-, h2u⟩ := log2_bounds
  obtain ⟨-, h3u⟩ := log3_bounds
  obtain ⟨-, h5u⟩ := log5_bounds
  have h7u := log7_upper
  linarith

private lemma tailSum_ge' (n : ℕ) (hn : 100 ≤ n) : (n:ℝ) * lamSum - errSum ≤ tailSum n := by
  have hdouble : tailSum n
      = ∑ i ∈ Finset.Ico 2 (n+1), ∑ p ∈ n.primesLE, ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ) := by
    unfold tailSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_mul]
  rw [hdouble]
  have hIco : Finset.Ico 2 7 ⊆ Finset.Ico 2 (n+1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    exact ⟨hi.1, by omega⟩
  have hstep1 : (∑ i ∈ Finset.Ico 2 7, ∑ p ∈ n.primesLE, ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ))
      ≤ ∑ i ∈ Finset.Ico 2 (n+1), ∑ p ∈ n.primesLE, ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hIco (fun i hi _ => ?_)
    exact Finset.sum_nonneg (fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (log_prime_nonneg'' (Nat.mem_primesLE.mp hp).2))
  have hsmall : ({2,3,5,7} : Finset ℕ) ⊆ n.primesLE := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Nat.mem_primesLE]
    rcases hp with h|h|h|h <;> subst h <;> norm_num <;> omega
  have hstep2 : (∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ))
      ≤ ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ n.primesLE, ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum_of_subset_of_nonneg hsmall (fun p hp _ => ?_))
    exact mul_nonneg (Nat.cast_nonneg _) (log_prime_nonneg'' (Nat.mem_primesLE.mp hp).2)
  have hstep3 : (∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (if p^i ≤ 100 then ((n:ℝ)/(p:ℝ)^i - 1) else 0) * Real.log (p:ℝ))
      ≤ ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        ((n / p^i : ℕ) : ℝ) * Real.log (p:ℝ) := by
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun p hp => ?_))
    have hp2 : (1:ℕ) ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h|h|h|h <;> subst h <;> norm_num
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hp1
    by_cases h : p^i ≤ 100
    · rw [if_pos h]
      have hfloor := div_pow_ge' n p i hp2
      exact mul_le_mul_of_nonneg_right hfloor hlog
    · rw [if_neg h, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) hlog
  have hval : (∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (if p^i ≤ 100 then ((n:ℝ)/(p:ℝ)^i - 1) else 0) * Real.log (p:ℝ))
      = (n:ℝ) * lamSum - errSum := by
    have hlam : lamSum = ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (if p^i ≤ 100 then Real.log (p:ℝ)/(p:ℝ)^i else 0) := rfl
    have herr : errSum = ∑ i ∈ Finset.Ico 2 7, ∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (if p^i ≤ 100 then Real.log (p:ℝ) else 0) := rfl
    rw [hlam, herr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : (2:ℕ) ≤ p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h|h|h|h <;> subst h <;> norm_num
    have hp0 : (p:ℝ) ≠ 0 := by
      have : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
      linarith
    by_cases h : p^i ≤ 100
    · simp only [if_pos h]
      field_simp
    · simp only [if_neg h]
      ring
  linarith [hstep1, hstep2, hstep3, hval.le, hval.ge]

private lemma frac_term_le' (n p : ℕ) (hp : 2 ≤ p) :
    (n:ℝ)/(p:ℝ) - ((n / p : ℕ) : ℝ) ≤ 1 - 1/(p:ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpnat : 0 < p := by omega
  have hd := Nat.div_add_mod n p
  have hdc : (n:ℝ) = ((n / p : ℕ) : ℝ) * (p:ℝ) + ((n % p : ℕ) : ℝ) := by
    have := congrArg (fun k : ℕ => (k:ℝ)) hd
    push_cast at this
    linarith [this]
  have hmodle : ((n % p : ℕ) : ℝ) ≤ (p:ℝ) - 1 := by
    have h := Nat.mod_lt n hpnat
    have h' : (n % p) ≤ p - 1 := by omega
    have h'' : ((n % p : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h'
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h''
    linarith
  have h1 : (n:ℝ)/(p:ℝ) - ((n / p : ℕ) : ℝ) = ((n % p : ℕ) : ℝ)/(p:ℝ) := by
    rw [hdc]; field_simp; ring
  rw [h1, div_le_iff₀ hp0]
  have hkey2 : (1 - 1/(p:ℝ)) * (p:ℝ) = (p:ℝ) - 1 := by
    field_simp
  rw [hkey2]
  exact hmodle

private lemma fracSum_le' (n : ℕ) :
    fracSum n ≤ Chebyshev.theta (n:ℝ) - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE (n:ℝ), Nat.floor_natCast]
  unfold fracSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp2 : 2 ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlog : 0 ≤ Real.log (p:ℝ) := log_prime_nonneg'' (Nat.mem_primesLE.mp hp).2
  have hfr := frac_term_le' n p hp2
  have heq : (1 - 1/(p:ℝ)) * Real.log (p:ℝ) = Real.log (p:ℝ) - Real.log (p:ℝ)/(p:ℝ) := by
    field_simp
  calc ((n:ℝ)/(p:ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p:ℝ)
      ≤ (1 - 1/(p:ℝ)) * Real.log (p:ℝ) := mul_le_mul_of_nonneg_right hfr hlog
    _ = Real.log (p:ℝ) - Real.log (p:ℝ)/(p:ℝ) := heq

/-- **Quantitative deficiency of the first Mertens sum.** For every `n ≥ 100`,
`Σ_{p ≤ n} (log p)/p ≤ log n - 0.36`. -/
private lemma logDiv_le_log_sub' (n : ℕ) (hn : 100 ≤ n) :
    (∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (n : ℝ) - 0.36 := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hident := n_mul_sum_eq_log_factorial' n hn1
  have hfac := (Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds hn2).2
  have hfrac := fracSum_le' n
  have htheta := Commons.NumberTheory.Chebyshev.theta_le_log3_mul n
  have htail := tailSum_ge' n hn
  have hlam := lamSum_ge
  have herr := errSum_le
  have hlog3 : Real.log 3 ≤ 1.0986123 := by linarith [Real.log_three_lt_d9]
  have hmul : 0.61 * (n:ℝ) ≤ (n:ℝ) * lamSum := by
    have := mul_le_mul_of_nonneg_left hlam (le_of_lt hnpos)
    linarith
  have hmul2 : Real.log 3 * (n:ℝ) ≤ 1.0986123 * (n:ℝ) :=
    mul_le_mul_of_nonneg_right hlog3 (le_of_lt hnpos)
  have hkey : (n:ℝ) * (∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ))
      ≤ (n:ℝ) * Real.log (n:ℝ) - (n:ℝ) + 1 + Real.log (n:ℝ)
        - ((n:ℝ) * lamSum - errSum) + (1.0986123 * (n:ℝ)
        - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ)) := by
    have h1 : Real.log (n.factorial:ℝ) - tailSum n + fracSum n
        ≤ (n:ℝ) * Real.log (n:ℝ) - (n:ℝ) + 1 + Real.log (n:ℝ) - ((n:ℝ) * lamSum - errSum)
          + (Real.log 3 * (n:ℝ) - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ)) := by
      linarith [hfac, hfrac, htheta, htail]
    have h2 := h1
    rw [← hident] at h2
    linarith [h2, hmul2]
  have hbound : ((n:ℝ) + 1) * (Real.log (n:ℝ) - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ))
      ≥ 0.5113877 * (n:ℝ) - 11.4 := by
    nlinarith [hkey, hmul, herr]
  have hfinal : Real.log (n:ℝ) - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ) ≥ 0.36 := by
    have hn100 : (100:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h1 : 0.36 * ((n:ℝ) + 1) ≤ 0.5113877 * (n:ℝ) - 11.4 := by nlinarith
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by linarith
    have h2 : ((n:ℝ)+1) * 0.36 ≤ ((n:ℝ)+1) * (Real.log (n:ℝ) - ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ)) := by
      have h1' : ((n:ℝ)+1) * 0.36 = 0.36 * ((n:ℝ)+1) := by ring
      rw [h1']
      exact le_trans h1 hbound
    exact (mul_le_mul_iff_of_pos_left hpos).mp h2
  linarith [hfinal]

/-- Real version of the deficiency. -/
private lemma logDiv_real_le' (t : ℝ) (ht : 100 ≤ t) : logDiv t ≤ Real.log t - 0.36 := by
  have hfloor : 100 ≤ ⌊t⌋₊ := by
    have h := Nat.floor_mono ht
    norm_num at h
    exact h
  have hle := logDiv_le_log_sub' ⌊t⌋₊ hfloor
  have hlogdiv : logDiv t = ∑ p ∈ (⌊t⌋₊).primesLE, Real.log (p : ℝ) / (p : ℝ) := rfl
  have hlogle : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  rw [hlogdiv]; linarith

/-! ## Numerics at `100` -/

private lemma log_100_eq' : Real.log 100 = 2 * Real.log 2 + 2 * Real.log 5 := by
  rw [show (100:ℝ) = 2^2 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  ring

private lemma log_100_le' : Real.log 100 ≤ 4.6051702 := by
  rw [log_100_eq']
  have h2' := Real.log_two_lt_d9
  have h5' := Real.log_five_lt_d9
  linarith

private lemma log_100_ge' : (4.6051701 : ℝ) ≤ Real.log 100 := by
  rw [log_100_eq']
  have h2' := Real.log_two_gt_d9
  have h5' := Real.log_five_gt_d9
  linarith

private lemma loglog_100_ge' : (1.5271 : ℝ) ≤ Real.log (Real.log 100) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2u : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have h100lo : (4.6051701 : ℝ) ≤ Real.log 100 := log_100_ge'
  have hlog100pos : (0:ℝ) < Real.log 100 := by linarith
  have h46 : (1.52605 : ℝ) ≤ Real.log (4.6:ℝ) := by
    have hsplit : Real.log (4.6:ℝ) = Real.log (4.5:ℝ) + Real.log (1 + 1/45) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h45 : Real.log (4.5:ℝ) = 2 * Real.log 3 - Real.log 2 := by
      rw [show (4.5:ℝ) = 3^2 / 2 by norm_num, Real.log_div (by positivity) (by norm_num), Real.log_pow]
      ring
    have h115 : 2 * (1/45) / ((1/45) + 2) ≤ Real.log (1 + 1/45) :=
      Real.le_log_one_add_of_nonneg (by norm_num)
    have hdd : 2 * (1:ℝ)/45 / ((1:ℝ)/45 + 2) = (2:ℝ)/91 := by norm_num
    rw [hsplit, h45]
    linarith [h115, hlog2u, hlog3, hdd]
  have hfrac : (0.001122 : ℝ) ≤ (Real.log 100 - 4.6)/Real.log 100 := by
    rw [le_div_iff₀ hlog100pos]
    nlinarith [h100lo, log_100_le']
  have hconc : Real.log (4.6:ℝ) + (Real.log 100 - 4.6)/Real.log 100 ≤ Real.log (Real.log 100) := by
    have h := Real.log_le_sub_one_of_pos (x := (4.6:ℝ)/Real.log 100) (by positivity)
    have hrw : Real.log ((4.6:ℝ)/Real.log 100) = Real.log 4.6 - Real.log (Real.log 100) :=
      Real.log_div (by norm_num) (ne_of_gt hlog100pos)
    rw [hrw] at h
    have hkey : Real.log (4.6:ℝ) + (Real.log 100 - 4.6)/Real.log 100
        = Real.log 4.6 - 4.6/Real.log 100 + 1 := by
      field_simp
      ring
    linarith [h, hkey.le]
  linarith

private lemma log_20_div_9_ge' : (0.790602 : ℝ) ≤ Real.log (20/9) := by
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_gt_d9
  have h : Real.log (20/9) = 2 * Real.log 2 + Real.log 5 - 2 * Real.log 3 := by
    rw [show (20:ℝ)/9 = 2^2 * 5 / 3^2 by norm_num,
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [h]; linarith

private lemma log_9_div_20_le' : Real.log (9/20) ≤ -0.7862 := by
  have h : Real.log (9/20) = -(Real.log (20/9)) := by
    rw [← Real.log_inv]; norm_num
  rw [h]
  linarith [log_20_div_9_ge']

private lemma primeRecips_100_eq' :
    primeRecips 100 = ∑ p ∈ (100 : ℕ).primesLE, (1:ℝ)/(p:ℝ) := by
  unfold primeRecips
  norm_num

private lemma logDiv_100_eq' :
    logDiv 100 = ∑ p ∈ (100 : ℕ).primesLE, Real.log (p : ℝ) / (p : ℝ) := by
  unfold logDiv
  norm_num

private lemma logDiv_100_ge' : (3.36 : ℝ) ≤ logDiv 100 := by
  rw [logDiv_100_eq']
  exact Commons.NumberTheory.PrimeReciprocals.logDiv_100_ge_36

private lemma primeRecips_100_le' : primeRecips 100 ≤ 1.803 := by
  rw [primeRecips_100_eq']
  exact Commons.NumberTheory.PrimeReciprocals.primeRecips_100_le

/-- The second-Mertens bound we need: `f y ≤ 0.4682` for `y ≥ 100`. -/
private lemma f_le' (y : ℝ) (hy : 100 ≤ y) :
    primeRecips y - Real.log (Real.log y) ≤ 0.4682 := by
  have hx2 : (2:ℝ) ≤ 100 := by norm_num
  have hxy : (100:ℝ) ≤ y := hy
  have hident := primeRecips_loglog_diff (x := (100:ℝ)) (X := y) (B₁ := 0) hx2 hxy
  simp only [sub_zero] at hident
  have hlogx : 0 < Real.log (100:ℝ) := Real.log_pos (by norm_num)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have h1 : (logDiv y - Real.log y)/Real.log y ≤ -0.36/Real.log y := by
    have h := logDiv_real_le' y hy
    rw [div_le_div_iff_of_pos_right hlogy]
    linarith
  have h2 : -((logDiv (100:ℝ) - Real.log (100:ℝ))/Real.log (100:ℝ)) ≤ 0.2704 := by
    have hnum : Real.log (100:ℝ) - logDiv (100:ℝ) ≤ 1.2451702 := by
      linarith [log_100_le', logDiv_100_ge']
    have hdiv : -((logDiv 100 - Real.log 100)/Real.log 100)
        = (Real.log 100 - logDiv 100)/Real.log 100 := by ring
    rw [hdiv]
    have h1' : (Real.log (100:ℝ) - logDiv (100:ℝ))/Real.log (100:ℝ) ≤
        1.2451702/Real.log (100:ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hlogx)
    have h2' : 1.2451702/Real.log (100:ℝ) ≤ 1.2451702/4.6051701 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) log_100_ge'
    have h3' : (1.2451702:ℝ)/4.6051701 ≤ 0.2704 := by
      have h : (1.2451702:ℝ) ≤ 0.2704 * 4.6051701 := by norm_num
      exact (div_le_iff₀ (by norm_num : (0:ℝ) < 4.6051701)).mpr h
    linarith
  have h3 : (∫ t in (100:ℝ)..y, (logDiv t - Real.log t)/(t*(Real.log t)^2))
      ≤ -0.36*(1/Real.log (100:ℝ) - 1/Real.log y) := by
    have hcont1 : IntervalIntegrable (fun t : ℝ => logDiv t/(t*(Real.log t)^2)) volume 100 y :=
      intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num) hxy
    have hcont2 : IntervalIntegrable (fun t : ℝ => (1:ℝ)/(t*(Real.log t))) volume 100 y := by
      apply ContinuousOn.intervalIntegrable
      intro z hz
      rw [Set.uIcc_of_le hxy] at hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hlogz : Real.log z ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
      have hden : ContinuousAt (fun t : ℝ => t * Real.log t) z :=
        continuousAt_id.mul (Real.continuousAt_log hz0)
      exact (continuousAt_const.div hden (mul_ne_zero hz0 hlogz)).continuousWithinAt
    have hcont3 : IntervalIntegrable (fun t : ℝ => (1:ℝ)/(t*(Real.log t)^2)) volume 100 y := by
      apply ContinuousOn.intervalIntegrable
      intro z hz
      rw [Set.uIcc_of_le hxy] at hz
      have hz0 : z ≠ 0 := by linarith [hz.1]
      have hlogz : Real.log z ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
      have hden : ContinuousAt (fun t : ℝ => t * (Real.log t)^2) z :=
        continuousAt_id.mul ((Real.continuousAt_log hz0).pow 2)
      exact (continuousAt_const.div hden (mul_ne_zero hz0 (pow_ne_zero 2 hlogz))).continuousWithinAt
    have hInt3' : IntervalIntegrable (fun t : ℝ => (-0.36)/(t*(Real.log t)^2)) volume 100 y := by
      have he : (fun t : ℝ => (-0.36)/(t*(Real.log t)^2))
          = fun t : ℝ => (-0.36) * ((1:ℝ)/(t*(Real.log t)^2)) := by funext t; ring
      rw [he]
      exact hcont3.const_mul (-0.36)
    have hfInt : IntervalIntegrable (fun t : ℝ => (logDiv t - Real.log t)/(t*(Real.log t)^2))
        volume 100 y := by
      refine IntervalIntegrable.congr ?_ (hcont1.sub hcont2)
      intro t ht
      rw [Set.uIoc_of_le hxy] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
      field_simp
    have hpoint : ∀ t ∈ Set.Icc (100:ℝ) y,
        (logDiv t - Real.log t)/(t*(Real.log t)^2) ≤ (-0.36)/(t*(Real.log t)^2) := by
      intro t ht
      have ht0 : (0:ℝ) < t := by linarith [ht.1]
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have hden : 0 < t*(Real.log t)^2 := by positivity
      have h := logDiv_real_le' t ht.1
      rw [div_le_div_iff_of_pos_right hden]
      linarith
    have hmono := intervalIntegral.integral_mono_on hxy hfInt hInt3' hpoint
    have hval : (∫ t in (100:ℝ)..y, (-0.36)/(t*(Real.log t)^2))
        = -0.36*(1/Real.log (100:ℝ) - 1/Real.log y) := by
      have hrew : (fun t : ℝ => (-0.36)/(t*(Real.log t)^2))
          = fun t : ℝ => (-0.36) * ((t)⁻¹/(Real.log t)^2) := by funext t; ring
      rw [hrew, intervalIntegral.integral_const_mul,
          integral_inv_div_log_sq (by norm_num : (1:ℝ) < 100) (by linarith : (1:ℝ) < y)]
      ring
    rw [← hval]
    exact hmono
  have hcomb : primeRecips y - Real.log (Real.log y) - (primeRecips 100 - Real.log (Real.log 100))
      ≤ -0.36/Real.log y + 0.2704 + (-0.36*(1/Real.log (100:ℝ) - 1/Real.log y)) := by
    linarith [hident, h1, h2, h3]
  have hrew' : -0.36/Real.log y + 0.2704 + (-0.36*(1/Real.log (100:ℝ) - 1/Real.log y))
      = 0.2704 - 0.36/Real.log (100:ℝ) := by
    field_simp
    ring
  have hfin1 : -0.36/Real.log y + 0.2704 + (-0.36*(1/Real.log (100:ℝ) - 1/Real.log y)) ≤ 0.1923 := by
    rw [hrew']
    have h1 : (0.0781:ℝ) * Real.log (100:ℝ) ≤ 0.36 := by nlinarith [log_100_le']
    have h2 : (0.0781:ℝ) ≤ 0.36/Real.log (100:ℝ) := by
      rw [le_div_iff₀ hlogx]; linarith
    linarith
  have hf100 : primeRecips 100 - Real.log (Real.log 100) ≤ 0.2759 := by
    have h1' := primeRecips_100_le'
    have h2' := loglog_100_ge'
    linarith
  linarith

/-! ## The Euler product lower bound -/

/-- The target lemma. -/
theorem primeProduct_oneSubInv_ge_invLog (y : ℕ) (hy : 100 ≤ y) :
    (9/20 : ℝ) / Real.log (y : ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := by
  have hy100 : (100:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hy1 : (1:ℝ) < (y:ℝ) := by linarith
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hy1
  have hfac : ∀ p ∈ Nat.primesLE y, (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
    intro p hp
    have hp2 : (2:ℕ) ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have h2 : (1:ℝ)/2 ≤ 1 - (p:ℝ)⁻¹ := by
      have := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num) hp2'
      rw [one_div] at this ⊢
      linarith
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h2
  have hfacne : ∀ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) ≠ 0 := fun p hp => ne_of_gt (hfac p hp)
  have hlogQ : Real.log (∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹))
      = - ∑ p ∈ Nat.primesLE y, Real.log ((p:ℝ)/((p:ℝ)-1)) := by
    rw [Real.log_prod hfacne]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp2 : (2:ℕ) ≤ p := Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2
    have hp2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hp0 : (0:ℝ) < (p:ℝ) := by linarith
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have h1 : 1 - (p:ℝ)⁻¹ = (((p:ℝ)/((p:ℝ)-1))⁻¹) := by
      field_simp
    rw [h1, Real.log_inv]
  have hsplit : (∑ p ∈ Nat.primesLE y, Real.log ((p:ℝ)/((p:ℝ)-1)))
      = (∑ p ∈ Nat.primesLE y, (1:ℝ)/(p:ℝ))
        + ∑ p ∈ Nat.primesLE y, (Real.log ((p:ℝ)/((p:ℝ)-1)) - (1:ℝ)/(p:ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    ring
  have hrec : (∑ p ∈ Nat.primesLE y, (1:ℝ)/(p:ℝ)) ≤ Real.log (Real.log (y:ℝ)) + 0.4682 := by
    have h1 : (∑ p ∈ Nat.primesLE y, (1:ℝ)/(p:ℝ)) = primeRecips (y:ℝ) := by
      unfold primeRecips
      rw [Nat.floor_natCast]
    rw [h1]
    have h2 := f_le' (y:ℝ) hy100
    linarith
  have hcorr := corr_sum_le y
  have hmain : Real.log (∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹))
      ≥ -(Real.log (Real.log (y:ℝ)) + 0.7862) := by
    rw [hlogQ, hsplit]
    have h0 : (∑ p ∈ Nat.primesLE y, (Real.log ((p:ℝ)/((p:ℝ)-1)) - (1:ℝ)/(p:ℝ))) ≤ 0.318 := by
      convert hcorr using 2
    have : Real.log (Real.log (y:ℝ)) + 0.4682
        + (∑ p ∈ Nat.primesLE y, (Real.log ((p:ℝ)/((p:ℝ)-1)) - (1:ℝ)/(p:ℝ)))
        ≤ Real.log (Real.log (y:ℝ)) + 0.7862 := by
      linarith
    linarith
  have hQpos : 0 < ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := Finset.prod_pos hfac
  have hexp : Real.exp (-(Real.log (Real.log (y:ℝ)) + 0.7862))
      ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := by
    have := Real.exp_le_exp.mpr hmain
    rwa [Real.exp_log hQpos] at this
  have hexpv : Real.exp (-(Real.log (Real.log (y:ℝ)) + 0.7862))
      = Real.exp (-0.7862) / Real.log (y:ℝ) := by
    rw [show -(Real.log (Real.log (y:ℝ)) + 0.7862)
        = -0.7862 + -(Real.log (Real.log (y:ℝ))) by ring]
    rw [Real.exp_add, Real.exp_neg 0.7862, Real.exp_neg (Real.log (Real.log (y:ℝ))),
        Real.exp_log hlogy]
    ring
  rw [hexpv] at hexp
  have h9 : (9/20 : ℝ) ≤ Real.exp (-0.7862) := by
    have h := log_9_div_20_le'
    have h2 : Real.exp (Real.log (9/20:ℝ)) ≤ Real.exp (-0.7862) := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 9/20)] at h2
  calc (9/20 : ℝ) / Real.log (y:ℝ) ≤ Real.exp (-0.7862) / Real.log (y:ℝ) :=
        div_le_div_of_nonneg_right h9 (le_of_lt hlogy)
    _ ≤ ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) := hexp

end

end Commons.NumberTheory.Mertens
