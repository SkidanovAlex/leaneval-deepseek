import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Primorial
import Submission.Commons.NumberTheory.Totient.prod_one_add_two_div_mul_pred_le_four
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors

namespace Commons.NumberTheory.DivisorBound

open scoped BigOperators
open Finset

noncomputable section

/-- The Euler-factor weight `2/(p(p-1))`. -/
private def cFun (p : ℕ) : ℝ := 2 / ((p : ℝ) * ((p : ℝ) - 1))

/-- The Euler product `∏_{p | e} 2/(p(p-1))` over the prime factors of `e`. -/
private def gFun (e : ℕ) : ℝ := ∏ p ∈ e.primeFactors, cFun p

private lemma cFun_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 ≤ cFun p := by
  rw [cFun]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  exact div_nonneg (by norm_num) hden.le

private lemma gFun_nonneg (e : ℕ) : 0 ≤ gFun e := by
  apply Finset.prod_nonneg
  intro p hp
  exact cFun_nonneg_of_prime (Nat.prime_of_mem_primeFactors hp)

private lemma card_divisors_squarefree (e : ℕ) (hsq : Squarefree e) :
    (Nat.divisors e).card = 2 ^ e.primeFactors.card := by
  rw [Nat.card_divisors hsq.ne_zero]
  rw [show (∏ x ∈ e.primeFactors, (e.factorization x + 1))
        = ∏ _x ∈ e.primeFactors, (2 : ℕ) from
      Finset.prod_congr rfl (fun p hp => by
        rw [Nat.factorization_eq_one_of_squarefree hsq (Nat.prime_of_mem_primeFactors hp)
          (Nat.mem_primeFactors.mp hp).2.1])]
  rw [Finset.prod_const]

/-- For squarefree `e`, the Euler product `∏_{p | e} 2/(p(p-1))` computes
`τ(e) / (e · φ(e))`. -/
private lemma tau_div_mul_totient_squarefree (e : ℕ) (hsq : Squarefree e) :
    ((Nat.divisors e).card : ℝ) / ((e : ℝ) * (Nat.totient e : ℝ)) = gFun e := by
  have he : e ≠ 0 := hsq.ne_zero
  have hprod : (e : ℝ) = ∏ p ∈ e.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hφ : Nat.totient e = ∏ p ∈ e.primeFactors, (p - 1) := by
    rw [Commons.NumberTheory.Totient.totient_eq_prod_primeFactors e he]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hsq (Nat.prime_of_mem_primeFactors hp)
      (Nat.mem_primeFactors.mp hp).2.1]
    simp
  have hφcast : (Nat.totient e : ℝ) = ∏ p ∈ e.primeFactors, ((p : ℝ) - 1) := by
    rw [hφ, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))]
    simp
  have hcard := card_divisors_squarefree e hsq
  calc
    ((Nat.divisors e).card : ℝ) / ((e : ℝ) * (Nat.totient e : ℝ))
        = ((2 ^ e.primeFactors.card : ℕ) : ℝ) /
            ((∏ p ∈ e.primeFactors, (p : ℝ)) * (∏ p ∈ e.primeFactors, ((p : ℝ) - 1))) := by
          rw [hcard, hprod, hφcast]
    _ = (∏ _p ∈ e.primeFactors, (2 : ℝ)) /
          (∏ p ∈ e.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))) := by
          congr 1
          · rw [Finset.prod_const]
            push_cast
            ring
          · rw [← Finset.prod_mul_distrib]
    _ = ∏ p ∈ e.primeFactors, (2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          rw [Finset.prod_div_distrib]
    _ = gFun e := rfl

/-- The auxiliary multiplicative function: `∏_{p | d} 2/(p(p-1))` on squarefree `d`,
and `0` otherwise. -/
private def hFun (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, cFun p else 0

private lemma hFun_of_squarefree (d : ℕ) (hd : Squarefree d) :
    hFun d = ∏ p ∈ d.primeFactors, cFun p := by
  simp [hFun, hd]

private lemma hFun_of_not_squarefree (d : ℕ) (hd : ¬ Squarefree d) : hFun d = 0 := by
  simp [hFun, hd]

private lemma hFun_one : hFun 1 = 1 := by
  rw [hFun_of_squarefree 1 squarefree_one]
  simp

private lemma hFun_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    hFun (a * b) = hFun a * hFun b := by
  by_cases hsab : Squarefree (a * b)
  · have hsq : Squarefree a ∧ Squarefree b := (Nat.squarefree_mul hab).mp hsab
    rw [hFun_of_squarefree (a * b) hsab, hFun_of_squarefree a hsq.1,
      hFun_of_squarefree b hsq.2]
    rw [Nat.primeFactors_mul hsq.1.ne_zero hsq.2.ne_zero]
    rw [Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  · have hna : ¬ Squarefree a ∨ ¬ Squarefree b := by
      by_contra h
      push Not at h
      exact hsab ((Nat.squarefree_mul hab).mpr ⟨h.1, h.2⟩)
    rcases hna with hna | hnb
    · rw [hFun_of_not_squarefree (a * b) hsab, hFun_of_not_squarefree a hna, zero_mul]
    · rw [hFun_of_not_squarefree (a * b) hsab, hFun_of_not_squarefree b hnb, mul_zero]

private lemma hFun_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    hFun (p ^ k) = 0 := by
  apply hFun_of_not_squarefree
  intro hsq
  have hk1 : k = 1 := ((Nat.squarefree_pow_iff hp.ne_one (by omega : k ≠ 0)).mp hsq).2
  omega

theorem sum_sqfree_tau_div_mul_totient_le_const :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ,
      (∑ e ∈ (Finset.Icc 1 V).filter Squarefree,
          ((Nat.divisors e).card : ℝ) / ((e : ℝ) * (Nat.totient e : ℝ))) ≤ C := by
  refine ⟨4, by norm_num, fun V => ?_⟩
  classical
  -- Replace each summand by the Euler product.
  have hterm : ∀ e ∈ (Finset.Icc 1 V).filter Squarefree,
      ((Nat.divisors e).card : ℝ) / ((e : ℝ) * (Nat.totient e : ℝ)) = gFun e := by
    intro e he
    exact tau_div_mul_totient_squarefree e (Finset.mem_filter.mp he).2
  rw [Finset.sum_congr rfl hterm]
  have hPne : primorial V ≠ 0 := primorial_ne_zero V
  have hPsq : Squarefree (primorial V) := squarefree_primorial V
  -- Every squarefree `e ≤ V` divides `V#`.
  have hsub : (Finset.Icc 1 V).filter Squarefree ⊆ (primorial V).divisors := by
    intro e he
    obtain ⟨heIcc, hesq⟩ := Finset.mem_filter.mp he
    rw [Nat.mem_divisors]
    refine ⟨?_, hPne⟩
    have heV : e ≤ V := (Finset.mem_Icc.mp heIcc).2
    exact (Squarefree.dvd_primorial hesq).trans (primorial_dvd_primorial heV)
  have hle1 : ∑ e ∈ (Finset.Icc 1 V).filter Squarefree, gFun e
      ≤ ∑ e ∈ (primorial V).divisors, gFun e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => gFun_nonneg e)
  -- Replace `gFun` by the multiplicative `hFun` on the divisors of `V#`.
  have hsum_eq : ∑ d ∈ (primorial V).divisors, gFun d
      = ∑ d ∈ (primorial V).divisors, hFun d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdsq : Squarefree d := hPsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    rw [hFun_of_squarefree d hdsq]
    rw [gFun]
  -- Euler product identity.
  have hmain := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    hFun (primorial V) hPne hFun_one hFun_mul hFun_prime_pow
  have hprod_eq : ∏ p ∈ (primorial V).primeFactors, (1 + hFun p)
      = ∏ p ∈ (primorial V).primeFactors, (1 + cFun p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hp_eq : hFun p = cFun p := by
      rw [hFun_of_squarefree p hpp.squarefree, hpp.primeFactors]
      simp
    rw [hp_eq]
  have hPbound : ∏ p ∈ (primorial V).primeFactors, (1 + cFun p) ≤ 4 :=
    Commons.NumberTheory.Totient.prod_one_add_two_div_mul_pred_le_four (primorial V)
  calc ∑ e ∈ (Finset.Icc 1 V).filter Squarefree, gFun e
      ≤ ∑ e ∈ (primorial V).divisors, gFun e := hle1
    _ = ∑ e ∈ (primorial V).divisors, hFun e := hsum_eq
    _ = ∏ p ∈ (primorial V).primeFactors, (1 + hFun p) := hmain.symm
    _ = ∏ p ∈ (primorial V).primeFactors, (1 + cFun p) := hprod_eq
    _ ≤ 4 := hPbound

end

end Commons.NumberTheory.DivisorBound