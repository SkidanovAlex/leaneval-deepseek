import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.squarefree_prod_primes

namespace Commons.NumberTheory.EulerProduct

open scoped BigOperators

set_option linter.unusedVariables false

/-- The function `n ↦ -f n` on primes and `0` elsewhere. -/
private def hf0 (f : ℕ → ℝ) (n : ℕ) : ℝ := if n.Prime then -f n else 0

/-- The finite-set product of `hf0 f` over a finset of naturals. -/
private def hfS (f : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∏ n ∈ S, hf0 f n

private lemma hf0_ne_zero {f : ℕ → ℝ} {n : ℕ} : hf0 f n ≠ 0 ↔ n.Prime ∧ f n ≠ 0 := by
  by_cases hp : n.Prime <;> simp [hf0, hp]

/-- If the finite product is nonzero then every index is prime. -/
private lemma prime_of_hfS_ne_zero {f : ℕ → ℝ} {S : Finset ℕ} (hS : hfS f S ≠ 0) :
    ∀ n ∈ S, n.Prime := by
  intro n hn
  rw [hfS, Finset.prod_ne_zero_iff] at hS
  exact (hf0_ne_zero.mp (hS n hn)).1

/-- On primes, the finite product is the product of `-f`. -/
private lemma hfS_eq_prod_neg {f : ℕ → ℝ} {S : Finset ℕ} (hS : ∀ n ∈ S, n.Prime) :
    hfS f S = ∏ n ∈ S, (-f n) :=
  Finset.prod_congr rfl fun n hn => by simp [hf0, hS n hn]

/-- The moebius function on a squarefree number, as a real number, is the product of `-1`
over its prime factors. -/
private lemma moebius_eq_prod_neg_one_real {n : ℕ} (hn : Squarefree n) :
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) = ∏ _p ∈ n.primeFactors, (-1 : ℝ) := by
  have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardFactors_apply,
      ← List.toFinset_card_of_nodup hn.nodup_primeFactorsList]
    simp
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn, hcard, Finset.prod_const]
  push_cast
  rfl

/-- The main reindexing identity: for a finset `S` of primes, the term of the Möbius sum at
`∏ S` equals the term of the finite-set Euler expansion at `S`. -/
private lemma moebius_term_eq {f : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    {S : Finset ℕ} (hS : ∀ n ∈ S, n.Prime) :
    ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * f (∏ n ∈ S, n) = hfS f S := by
  have hpr : (∏ n ∈ S, n).primeFactors = S := Nat.primeFactors_prod hS
  have hsq : Squarefree (∏ n ∈ S, n) := Commons.Data.Nat.squarefree_prod_primes hS
  have hfprod : f (∏ n ∈ S, n) = ∏ n ∈ S, f n := by
    rw [Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors f hmul h1 hsq, hpr]
  have hmu : ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) = ∏ n ∈ S, (-1 : ℝ) := by
    rw [moebius_eq_prod_neg_one_real hsq, hpr]
  calc ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * f (∏ n ∈ S, n)
      = (∏ n ∈ S, (-1 : ℝ)) * (∏ n ∈ S, f n) := by rw [hmu, hfprod]
    _ = ∏ n ∈ S, ((-1 : ℝ) * f n) := Finset.prod_mul_distrib.symm
    _ = ∏ n ∈ S, (-f n) := Finset.prod_congr rfl fun n _ => by rw [neg_one_mul]
    _ = hfS f S := (hfS_eq_prod_neg hS).symm

theorem tsum_moebius_mul_eq_tprod_of_pow_bound {f : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1)) :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
      = ∏' p : {p : ℕ // p.Prime}, (1 - f p) := by
  classical
  -- only the prime case `k = 1` of the hypothesis is used
  have hbd_prime : ∀ p : ℕ, p.Prime → |f p| ≤ C / (p : ℝ) ^ 2 := by
    intro p hp
    have h := hbd p 1 hp (le_refl 1)
    simpa using h
  -- summability of the prime term
  have hbd_lin : ∀ n : ℕ, ‖hf0 f n‖ ≤ C / (n : ℝ) ^ 2 := by
    intro n
    by_cases hp : n.Prime
    · rw [hf0, if_pos hp, norm_neg, Real.norm_eq_abs]
      exact hbd_prime n hp
    · rw [hf0, if_neg hp, norm_zero]
      exact div_nonneg hC.le (sq_nonneg _)
  have hbase : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)).mul_left C
    simpa [div_eq_mul_inv] using h
  have hsum_F0 : Summable (fun n : ℕ => ‖hf0 f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbd_lin n) hbase
  -- summability of the finite-set product
  have hsum_g : Summable (hfS f) := summable_finsetProd_of_summable_norm hsum_F0
  -- the Euler expansion of the infinite product
  have htprod : ∏' n : ℕ, (1 + hf0 f n) = ∑' S : Finset ℕ, hfS f S := tprod_one_add hsum_g
  have hprod_sub : ∏' n : ℕ, (1 + hf0 f n)
      = ∏' p : {p : ℕ // p.Prime}, (1 - f p) := by
    have hsub : (∏' p : {p : ℕ // p.Prime}, (1 - f p))
        = ∏' n : ℕ, (Set.mulIndicator {n : ℕ | n.Prime} (fun n => 1 - f n)) n :=
      tprod_subtype {n : ℕ | n.Prime} (fun n => 1 - f n)
    rw [hsub]
    refine tprod_congr fun n => ?_
    by_cases hp : n.Prime
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_true]
      ring
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_false]
      ring
  have hHasSum_g : HasSum (hfS f) (∏' p : {p : ℕ // p.Prime}, (1 - f p)) := by
    have hh := hsum_g.hasSum
    rw [← htprod] at hh
    rw [hprod_sub] at hh
    exact hh
  -- transfer along the squarefree reindexing
  have key : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
        (∏' p : {p : ℕ // p.Prime}, (1 - f p))
      ↔ HasSum (hfS f) (∏' p : {p : ℕ // p.Prime}, (1 - f p)) :=
    hasSum_iff_hasSum_of_ne_zero_bij
      (a := ∏' p : {p : ℕ // p.Prime}, (1 - f p))
      (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
      (g := hfS f)
      (i := fun x : ↑(Function.support (hfS f)) => ∏ n ∈ (x : Finset ℕ), n)
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have hxp : ∀ n ∈ x, n.Prime := prime_of_hfS_ne_zero hx
        have hyp : ∀ n ∈ y, n.Prime := prime_of_hfS_ne_zero hy
        have hxy'' : (∏ p ∈ (x : Finset ℕ), p) = (∏ p ∈ (y : Finset ℕ), p) := hxy
        have hxy' : (x : Finset ℕ) = y := by
          rw [← Nat.primeFactors_prod hxp, hxy'', Nat.primeFactors_prod hyp]
        exact Subtype.ext hxy')
      (by
        intro n hn
        rw [Function.mem_support] at hn
        have hmu_ne : ArithmeticFunction.moebius n ≠ 0 := by
          intro hzero
          rw [hzero] at hn
          simp at hn
        have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu_ne
        refine ⟨⟨n.primeFactors, ?_⟩, ?_⟩
        · rw [Function.mem_support,
            ← moebius_term_eq hmul h1 (fun p _ => Nat.prime_of_mem_primeFactors ‹p ∈ n.primeFactors›),
            Nat.prod_primeFactors_of_squarefree hsq]
          exact hn
        · exact Nat.prod_primeFactors_of_squarefree hsq)
      (by
        rintro ⟨S, hS⟩
        exact moebius_term_eq hmul h1 (prime_of_hfS_ne_zero hS))
  exact (key.mpr hHasSum_g).tsum_eq

end Commons.NumberTheory.EulerProduct
