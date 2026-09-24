import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
import Submission.Commons.NumberTheory.Mertens.factorial_log_eq_sum_legendre
import Submission.Commons.NumberTheory.Mertens.legendre_tail_lower

open Finset Real
open scoped BigOperators

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `Σ_{p ≤ n} log p / p`. -/
private def mS (n : ℕ) : ℝ := ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)

/-- `Σ_{p ≤ n} ⌊n/p⌋ log p` (first Legendre term). -/
private def mFloor (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} (n/p − ⌊n/p⌋) log p` (fractional-part correction). -/
private def mFrac (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} Σ_{2 ≤ i ≤ n} ⌊n/p^i⌋ log p` (tail of Legendre's formula). -/
private def mTail (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)

/-- `Σ_{p ≤ n} Σ_{2 ≤ i ≤ log_p n} (log p)/p^i` (the `n`-linear part of the tail). -/
private def mLam (n : ℕ) : ℝ :=
  ∑ p ∈ n.primesLE,
    (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i) * Real.log (p : ℝ)

/-! ## Splitting the range `Ico 1 (n+1)` -/

private lemma sum_Ico_succ_split {R : Type*} [AddCommMonoid R] (f : ℕ → R) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Ico 1 (n + 1), f i) = f 1 + ∑ i ∈ Finset.Ico 2 (n + 1), f i := by
  have hEq : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
    ext i
    rw [mem_Ico, mem_insert, mem_Ico]
    constructor
    · intro h
      by_cases hi : i = 1
      · exact Or.inl hi
      · exact Or.inr ⟨by omega, h.2⟩
    · intro h
      rcases h with h | h
      · subst h; exact ⟨le_rfl, by omega⟩
      · exact ⟨by omega, h.2⟩
  rw [hEq, Finset.sum_insert]
  simp

/-! ## The Legendre identity -/

private lemma n_mul_mS_eq_sum (n : ℕ) :
    (n : ℝ) * mS n = ∑ p ∈ n.primesLE, ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ) := by
  rw [mS, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

private lemma n_mul_mS_eq_floor_add_frac (n : ℕ) :
    (n : ℝ) * mS n = mFloor n + mFrac n := by
  rw [n_mul_mS_eq_sum, mFloor, mFrac, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

private lemma log_factorial_eq_floor_add_tail (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) = mFloor n + mTail n := by
  rw [factorial_log_eq_sum_legendre, mFloor, mTail, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_Ico_succ_split (R := ℝ) (f := fun i => ((n / p ^ i : ℕ) : ℝ)) hn, add_mul, pow_one]

private lemma n_mul_mS_eq_logFac_sub_tail_add_frac (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * mS n = Real.log (n.factorial : ℝ) - mTail n + mFrac n := by
  rw [n_mul_mS_eq_floor_add_frac, log_factorial_eq_floor_add_tail n hn]
  ring

/-! ## Bounding the fractional part term -/

private lemma frac_le_one (n p : ℕ) (hp : 0 < p) :
    (n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ) ≤ 1 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdiv := Nat.div_add_mod n p
  have hmod := Nat.mod_lt n hp
  have hcast : (n : ℝ) = (p : ℝ) * (((n / p : ℕ) : ℝ)) + (((n % p : ℕ) : ℝ)) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hdiv
    push_cast at this
    linarith [this]
  have hmodR : (((n % p : ℕ) : ℝ)) < (p : ℝ) := by exact_mod_cast hmod
  have hfrac : (n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ) = (((n % p : ℕ) : ℝ)) / (p : ℝ) := by
    rw [hcast]
    field_simp
    ring
  rw [hfrac, div_le_one hpR]
  linarith

private lemma mFrac_le_theta (n : ℕ) : mFrac n ≤ Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log n, mFrac]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
  calc ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)
      ≤ 1 * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right (frac_le_one n p hpp.pos) hlog
    _ = Real.log (p : ℝ) := one_mul _

/-! ## Lower bound for the Legendre tail -/

private lemma mTail_ge (n : ℕ) :
    (n : ℝ) * mLam n - (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) ≤ mTail n := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime n
  have htheta := Chebyshev.theta_eq_sum_primesLE_log n
  have hterm : (∑ p ∈ n.primesLE,
        ((n : ℝ) * (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i)
          - ((Nat.log p n : ℝ) - 1)) * Real.log (p : ℝ))
      ≤ mTail n := by
    rw [mTail]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hpn : p ≤ n := Nat.le_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    exact mul_le_mul_of_nonneg_right (legendre_tail_lower n p hpp hpn) hlog
  have hsplit : (∑ p ∈ n.primesLE,
        ((n : ℝ) * (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i)
          - ((Nat.log p n : ℝ) - 1)) * Real.log (p : ℝ))
      = (n : ℝ) * mLam n
        - ∑ p ∈ n.primesLE, ((Nat.log p n : ℝ) - 1) * Real.log (p : ℝ) := by
    rw [mLam, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hcorr : (∑ p ∈ n.primesLE, ((Nat.log p n : ℝ) - 1) * Real.log (p : ℝ))
      = Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
    rw [hpsi, htheta, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit, hcorr] at hterm
  exact hterm

/-! ## The constant `Λ ≥ 3/5` -/

private lemma log_seven_lb : (1.9365843980 : ℝ) ≤ Real.log 7 := by
  have h8 : (0 : ℝ) < 8 / 7 := by norm_num
  have h := Real.log_le_sub_one_of_pos h8
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlog8] at h
  linarith

private lemma geom_le_inner (n p : ℕ) (hp : p.Prime) (m : ℕ) (hm : p ^ m ≤ n) :
    (∑ i ∈ Finset.Ico 2 (m + 1), (1 : ℝ) / (p : ℝ) ^ i)
      ≤ ∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i := by
  have hmle : m ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt hm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    exact ⟨hi.1, by omega⟩
  · intro i _ _
    positivity

private lemma mLam_ge (n : ℕ) (hn : 100 ≤ n) : (3 / 5 : ℝ) ≤ mLam n := by
  have hsub : ({2, 3, 5, 7} : Finset ℕ) ⊆ n.primesLE := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Nat.mem_primesLE.mpr ⟨by omega, by decide⟩
  have hnonneg : ∀ p ∈ n.primesLE,
      0 ≤ (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / (p : ℝ) ^ i) * Real.log (p : ℝ) := by
    intro p hp
    refine mul_nonneg (Finset.sum_nonneg fun i _ => ?_)
      (Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp))))
    positivity
  have hmono : (∑ p ∈ ({2, 3, 5, 7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / ((p : ℕ) : ℝ) ^ i)
          * Real.log ((p : ℕ) : ℝ))
      ≤ mLam n := by
    rw [mLam]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnonneg p hp)
  have hsum : (∑ p ∈ ({2, 3, 5, 7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / ((p : ℕ) : ℝ) ^ i)
          * Real.log ((p : ℕ) : ℝ))
      = (∑ i ∈ Finset.Ico 2 (Nat.log 2 n + 1), (1 : ℝ) / ((2 : ℕ) : ℝ) ^ i)
          * Real.log ((2 : ℕ) : ℝ)
        + (∑ i ∈ Finset.Ico 2 (Nat.log 3 n + 1), (1 : ℝ) / ((3 : ℕ) : ℝ) ^ i)
          * Real.log ((3 : ℕ) : ℝ)
        + (∑ i ∈ Finset.Ico 2 (Nat.log 5 n + 1), (1 : ℝ) / ((5 : ℕ) : ℝ) ^ i)
          * Real.log ((5 : ℕ) : ℝ)
        + (∑ i ∈ Finset.Ico 2 (Nat.log 7 n + 1), (1 : ℝ) / ((7 : ℕ) : ℝ) ^ i)
          * Real.log ((7 : ℕ) : ℝ) := by
    norm_num [Finset.sum_insert]
    ring
  have h2 := geom_le_inner n 2 (by norm_num) 6 (by norm_num; omega : 2 ^ 6 ≤ n)
  have h3 := geom_le_inner n 3 (by norm_num) 4 (by norm_num; omega : 3 ^ 4 ≤ n)
  have h5 := geom_le_inner n 5 (by norm_num) 2 (by norm_num; omega : 5 ^ 2 ≤ n)
  have h7 := geom_le_inner n 7 (by norm_num) 2 (by norm_num; omega : 7 ^ 2 ≤ n)
  have e2 : (∑ i ∈ Finset.Ico 2 (6 + 1), (1 : ℝ) / ((2 : ℕ) : ℝ) ^ i) = 31 / 64 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  have e3 : (∑ i ∈ Finset.Ico 2 (4 + 1), (1 : ℝ) / ((3 : ℕ) : ℝ) ^ i) = 13 / 81 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  have e5 : (∑ i ∈ Finset.Ico 2 (2 + 1), (1 : ℝ) / ((5 : ℕ) : ℝ) ^ i) = 1 / 25 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  have e7 : (∑ i ∈ Finset.Ico 2 (2 + 1), (1 : ℝ) / ((7 : ℕ) : ℝ) ^ i) = 1 / 49 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num [Finset.sum_range_succ]
  have h2' : (31 / 64 : ℝ)
      ≤ ∑ i ∈ Finset.Ico 2 (Nat.log 2 n + 1), (1 : ℝ) / ((2 : ℕ) : ℝ) ^ i := by
    rw [← e2]; exact h2
  have h3' : (13 / 81 : ℝ)
      ≤ ∑ i ∈ Finset.Ico 2 (Nat.log 3 n + 1), (1 : ℝ) / ((3 : ℕ) : ℝ) ^ i := by
    rw [← e3]; exact h3
  have h5' : (1 / 25 : ℝ)
      ≤ ∑ i ∈ Finset.Ico 2 (Nat.log 5 n + 1), (1 : ℝ) / ((5 : ℕ) : ℝ) ^ i := by
    rw [← e5]; exact h5
  have h7' : (1 / 49 : ℝ)
      ≤ ∑ i ∈ Finset.Ico 2 (Nat.log 7 n + 1), (1 : ℝ) / ((7 : ℕ) : ℝ) ^ i := by
    rw [← e7]; exact h7
  have hl2 : (0.6931471803 : ℝ) < Real.log ((2 : ℕ) : ℝ) := Real.log_two_gt_d9
  have hl3 : (1.0986122885 : ℝ) < Real.log ((3 : ℕ) : ℝ) := Real.log_three_gt_d9
  have hl5 : (1.6094379123 : ℝ) < Real.log ((5 : ℕ) : ℝ) := Real.log_five_gt_d9
  have hl7 : (1.9365843980 : ℝ) ≤ Real.log ((7 : ℕ) : ℝ) := log_seven_lb
  have hl2' : (0 : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
  have hl3' : (0 : ℝ) ≤ Real.log ((3 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
  have hl5' : (0 : ℝ) ≤ Real.log ((5 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
  have hl7' : (0 : ℝ) ≤ Real.log ((7 : ℕ) : ℝ) := Real.log_nonneg (by norm_num)
  have hprod2 : (31 / 64) * Real.log ((2 : ℕ) : ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (Nat.log 2 n + 1), (1 : ℝ) / ((2 : ℕ) : ℝ) ^ i)
        * Real.log ((2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h2' hl2'
  have hprod3 : (13 / 81) * Real.log ((3 : ℕ) : ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (Nat.log 3 n + 1), (1 : ℝ) / ((3 : ℕ) : ℝ) ^ i)
        * Real.log ((3 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h3' hl3'
  have hprod5 : (1 / 25) * Real.log ((5 : ℕ) : ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (Nat.log 5 n + 1), (1 : ℝ) / ((5 : ℕ) : ℝ) ^ i)
        * Real.log ((5 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h5' hl5'
  have hprod7 : (1 / 49) * Real.log ((7 : ℕ) : ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (Nat.log 7 n + 1), (1 : ℝ) / ((7 : ℕ) : ℝ) ^ i)
        * Real.log ((7 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h7' hl7'
  have hbase : (3 / 5 : ℝ) ≤ (31 / 64) * Real.log ((2 : ℕ) : ℝ)
      + (13 / 81) * Real.log ((3 : ℕ) : ℝ) + (1 / 25) * Real.log ((5 : ℕ) : ℝ)
      + (1 / 49) * Real.log ((7 : ℕ) : ℝ) := by
    nlinarith [hl2, hl3, hl5, hl7]
  calc (3 / 5 : ℝ)
      ≤ (31 / 64) * Real.log ((2 : ℕ) : ℝ) + (13 / 81) * Real.log ((3 : ℕ) : ℝ)
          + (1 / 25) * Real.log ((5 : ℕ) : ℝ) + (1 / 49) * Real.log ((7 : ℕ) : ℝ) := hbase
    _ ≤ (∑ i ∈ Finset.Ico 2 (Nat.log 2 n + 1), (1 : ℝ) / ((2 : ℕ) : ℝ) ^ i)
            * Real.log ((2 : ℕ) : ℝ)
          + (∑ i ∈ Finset.Ico 2 (Nat.log 3 n + 1), (1 : ℝ) / ((3 : ℕ) : ℝ) ^ i)
            * Real.log ((3 : ℕ) : ℝ)
          + (∑ i ∈ Finset.Ico 2 (Nat.log 5 n + 1), (1 : ℝ) / ((5 : ℕ) : ℝ) ^ i)
            * Real.log ((5 : ℕ) : ℝ)
          + (∑ i ∈ Finset.Ico 2 (Nat.log 7 n + 1), (1 : ℝ) / ((7 : ℕ) : ℝ) ^ i)
            * Real.log ((7 : ℕ) : ℝ) := by
        linarith [hbase, hprod2, hprod3, hprod5, hprod7]
    _ = (∑ p ∈ ({2, 3, 5, 7} : Finset ℕ),
          (∑ i ∈ Finset.Ico 2 (Nat.log p n + 1), (1 : ℝ) / ((p : ℕ) : ℝ) ^ i)
            * Real.log ((p : ℕ) : ℝ)) := hsum.symm
    _ ≤ mLam n := hmono

/-! ## Bounds on `ψ` and the final numeric inequality -/

private lemma psi_le (n : ℕ) : Chebyshev.psi (n : ℝ) ≤ 1.099 * (n : ℝ) := by
  have h := Chebyshev.psi_le_log3_mul_real (n : ℝ) (Nat.cast_nonneg n)
  have h3 : Real.log 3 ≤ 1.099 := by linarith [Real.log_three_lt_d9]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h, h3, hn0]

private lemma numeric_key (n : ℕ) (hn : 100 ≤ n) : 1 + Real.log (n : ℝ) ≤ 0.201 * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log (n : ℝ) = Real.log 100 + Real.log ((n : ℝ) / 100) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (100 : ℝ) ≤ 7 * Real.log 2 := by
    have h : (100 : ℝ) ≤ (2 : ℝ) ^ 7 := by norm_num
    calc Real.log 100 ≤ Real.log ((2 : ℝ) ^ 7) := Real.log_le_log (by norm_num) h
      _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h3 : Real.log ((n : ℝ) / 100) ≤ (n : ℝ) / 100 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have h100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [hlog]
  linarith

end

/-! ## The theorem -/

/-- **Quantitative deficiency of the first Mertens sum.** For every `n ≥ 100`,
`Σ_{p ≤ n} (log p)/p ≤ log n - 0.3`.-/
theorem logDiv_le_log_sub (n : ℕ) (hn : 100 ≤ n) :
    (∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (n : ℝ) - 0.3 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hid := n_mul_mS_eq_logFac_sub_tail_add_frac n hn1
  have hfac := (Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds (n := n)
    (by omega : 2 ≤ n)).2
  have htail := mTail_ge n
  have hfrac := mFrac_le_theta n
  have hlam := mLam_ge n hn
  have hpsi := psi_le n
  have hkey := numeric_key n hn
  have hlam' : (3 / 5 : ℝ) * (n : ℝ) ≤ (n : ℝ) * mLam n := by
    have := mul_le_mul_of_nonneg_left hlam (Nat.cast_nonneg n)
    linarith
  have hmain : (n : ℝ) * mS n ≤ (n : ℝ) * Real.log (n : ℝ) - 0.3 * (n : ℝ) := by
    rw [hid]
    nlinarith [hfac, htail, hfrac, hpsi, hkey, hlam']
  have hmain' : (n : ℝ) * mS n ≤ (n : ℝ) * (Real.log (n : ℝ) - 0.3) := by linarith
  have := le_of_mul_le_mul_left hmain' hn0
  show mS n ≤ Real.log (n : ℝ) - 0.3
  linarith

end Commons.NumberTheory.Mertens
