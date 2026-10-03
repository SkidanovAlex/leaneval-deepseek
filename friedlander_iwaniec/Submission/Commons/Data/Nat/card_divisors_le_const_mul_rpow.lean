import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace Commons.Data.Nat

private lemma nat_cast_succ_le_two_pow (e : ℕ) : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have h2 : (2 : ℝ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    rw [h2]
    push_cast
    nlinarith [ih, pow_pos (by norm_num : (0 : ℝ) < 2) e]

private noncomputable def divBound (eps : ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ^ eps < 2 then 1 + 1 / ((p : ℝ) ^ eps - 1) else 1

private lemma one_lt_rpow_of_two_le (eps : ℝ) (heps : 0 < eps) {p : ℕ} (hp : 2 ≤ p) :
    1 < (p : ℝ) ^ eps := by
  have h1 : (1 : ℝ) < (2 : ℝ) ^ eps := Real.one_lt_rpow (by norm_num) heps
  have h2 : (2 : ℝ) ^ eps ≤ (p : ℝ) ^ eps :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) (le_of_lt heps)
  linarith

private lemma one_le_divBound (eps : ℝ) (heps : 0 < eps) {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ divBound eps p := by
  have hx : 1 < (p : ℝ) ^ eps := one_lt_rpow_of_two_le eps heps hp
  rw [divBound]
  by_cases h : (p : ℝ) ^ eps < 2
  · rw [if_pos h]
    have ht : 0 < (p : ℝ) ^ eps - 1 := by linarith
    have : 0 < 1 / ((p : ℝ) ^ eps - 1) := by positivity
    linarith
  · rw [if_neg h]

private lemma zero_le_divBound (eps : ℝ) (heps : 0 < eps) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ divBound eps p :=
  le_trans zero_le_one (one_le_divBound eps heps hp)

private lemma rpow_bound (eps : ℝ) {x : ℝ} (hx1 : 1 < x) (e : ℕ) :
    (e : ℝ) + 1 ≤ (if x < 2 then 1 + 1 / (x - 1) else 1) * x ^ e := by
  by_cases hsmall : x < 2
  · rw [if_pos hsmall]
    have ht : 0 < x - 1 := by linarith
    have hxt : (1 : ℝ) + (x - 1) = x := by ring
    have hbern : 1 + (e : ℝ) * (x - 1) ≤ x ^ e := by
      have h := one_add_mul_le_pow (R := ℝ) (show (-2 : ℝ) ≤ x - 1 by linarith) e
      rwa [hxt] at h
    have h1 : (e : ℝ) + 1 ≤ (1 + 1 / (x - 1)) * (1 + (e : ℝ) * (x - 1)) := by
      have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
      have hx : (1 : ℝ) + 1 / (x - 1) = (x - 1 + 1) / (x - 1) := by
        rw [add_div, div_self (ne_of_gt ht)]
      rw [hx, div_mul_eq_mul_div, le_div_iff₀ ht]
      nlinarith [sq_nonneg (x - 1), he0, mul_nonneg he0 (sq_nonneg (x - 1))]
    calc (e : ℝ) + 1 ≤ (1 + 1 / (x - 1)) * (1 + (e : ℝ) * (x - 1)) := h1
      _ ≤ (1 + 1 / (x - 1)) * x ^ e := by
        apply mul_le_mul_of_nonneg_left hbern
        have : (0 : ℝ) < 1 / (x - 1) := by positivity
        linarith
  · rw [if_neg hsmall]
    have hle : (2 : ℝ) ≤ x := not_lt.mp hsmall
    have h2 : (2 : ℝ) ^ e ≤ x ^ e := pow_le_pow_left₀ (by norm_num) hle e
    have h3 := nat_cast_succ_le_two_pow e
    linarith

private lemma prime_factor_bound (eps : ℝ) (heps : 0 < eps) (p e : ℕ) (hp : 2 ≤ p) :
    (e : ℝ) + 1 ≤ divBound eps p * (p : ℝ) ^ (eps * e) := by
  rw [divBound]
  have hpow : (p : ℝ) ^ (eps * e) = ((p : ℝ) ^ eps) ^ e :=
    Real.rpow_mul_natCast (by positivity) eps e
  rw [hpow]
  exact rpow_bound eps (one_lt_rpow_of_two_le eps heps hp) e

theorem card_divisors_le_const_mul_rpow (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ eps := by
  set K : ℕ := ⌊(2 : ℝ) ^ (1 / eps)⌋₊ + 1 with hK
  set C : ℝ := ∏ p ∈ (Finset.range K).filter Nat.Prime, divBound eps p with hC
  refine ⟨C, ?_, ?_⟩
  · rw [hC]
    refine Finset.prod_pos ?_
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact lt_of_lt_of_le zero_lt_one (one_le_divBound eps heps hp.2.two_le)
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, Real.zero_rpow heps.ne']
      simp
    · have hcard := Nat.card_divisors hn
      have hprodR : ∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * n.factorization p) =
          (n : ℝ) ^ eps := by
        have hnat : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
          simpa [Finsupp.prod, Nat.support_factorization] using
            Nat.prod_factorization_pow_eq_self hn
        have hcast : ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) = (n : ℝ) := by
          have h1 := congrArg (fun m : ℕ => (m : ℝ)) hnat
          push_cast at h1
          simpa using h1
        calc ∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * n.factorization p)
            = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ eps := by
              refine Finset.prod_congr rfl ?_
              intro p hp
              rw [mul_comm eps (n.factorization p : ℝ),
                Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ)), Real.rpow_natCast]
          _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) ^ eps :=
              Real.finsetProd_rpow _ _ (fun p hp => by positivity) eps
          _ = (n : ℝ) ^ eps := by rw [hcast]
      have hcC : ∏ p ∈ n.primeFactors, divBound eps p ≤ C := by
        rw [hC]
        have hne : ∀ x ∈ n.primeFactors, divBound eps x ≠ 1 → (x : ℝ) ^ eps < 2 := by
          intro x hx h
          by_contra hlt
          exact h (by rw [divBound, if_neg hlt])
        rw [← Finset.prod_filter_of_ne hne]
        apply Finset.prod_le_prod_of_subset_of_one_le₀
        · intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpP, hpsmall⟩ := hp
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, Nat.prime_of_mem_primeFactors hpP⟩
          have hlt : (p : ℝ) < (2 : ℝ) ^ (1 / eps) := by
            have h2 : (2 : ℝ) = ((2 : ℝ) ^ (1 / eps)) ^ eps := by
              rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (1 / eps) eps,
                one_div_mul_cancel heps.ne', Real.rpow_one]
            rw [h2] at hpsmall
            exact (Real.rpow_lt_rpow_iff (Nat.cast_nonneg p)
              (Real.rpow_nonneg (by norm_num) _) heps).mp hpsmall
          have hple : p ≤ ⌊(2 : ℝ) ^ (1 / eps)⌋₊ := Nat.le_floor (le_of_lt hlt)
          rw [hK]
          exact Nat.lt_succ_of_le hple
        · intro p hp
          rw [Finset.mem_filter] at hp
          exact zero_le_divBound eps heps (Nat.prime_of_mem_primeFactors hp.1).two_le
        · intro p hp hps
          rw [Finset.mem_filter, Finset.mem_range] at hp
          exact one_le_divBound eps heps hp.2.two_le
      have hbound : ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
          ∏ p ∈ n.primeFactors, divBound eps p * (p : ℝ) ^ (eps * n.factorization p) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have h1 : (0 : ℝ) ≤ (n.factorization p : ℝ) := Nat.cast_nonneg _
          linarith
        · intro p hp
          exact prime_factor_bound eps heps p (n.factorization p)
            (Nat.prime_of_mem_primeFactors hp).two_le
      calc (((Nat.divisors n).card : ℕ) : ℝ)
          = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
            rw [hcard]; push_cast; rfl
        _ ≤ ∏ p ∈ n.primeFactors,
              divBound eps p * (p : ℝ) ^ (eps * n.factorization p) := hbound
        _ = (∏ p ∈ n.primeFactors, divBound eps p) *
              (∏ p ∈ n.primeFactors, (p : ℝ) ^ (eps * n.factorization p)) :=
              Finset.prod_mul_distrib
        _ ≤ C * (n : ℝ) ^ eps := by
            rw [hprodR]
            exact mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg (Nat.cast_nonneg n) eps)

end Commons.Data.Nat