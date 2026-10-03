import Mathlib
import Submission.Commons.NumberTheory.Nat.sum_pow_omega_div_sqrt_rad_le

namespace Commons.NumberTheory.EulerProduct

open Finset
open scoped BigOperators

/-- Multiplicativity on a product of pairwise coprime numbers. -/
private lemma g_prod_of_pairwise {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (h1 : g 1 = 1) :
    ∀ (s : Finset ℕ) (φ : ℕ → ℕ),
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (φ p) (φ q)) →
      g (∏ p ∈ s, φ p) = ∏ p ∈ s, g (φ p) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro φ _; simp [h1]
  | insert a t ha ih =>
    intro φ hpair
    have hpair_t : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime (φ p) (φ q) :=
      fun p hp q hq hpq => hpair p (mem_insert_of_mem hp) q (mem_insert_of_mem hq) hpq
    have hcop : Nat.Coprime (φ a) (∏ p ∈ t, φ p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact hpair a (mem_insert_self a t) p (mem_insert_of_mem hp) (fun h => ha (h ▸ hp))
    rw [Finset.prod_insert ha, hmul (φ a) _ hcop, Finset.prod_insert ha, ih φ hpair_t]

/-- `f` on `n` factors over the prime powers dividing `n`. -/
private lemma f_eq_prod_prime_powers {f : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    {n : ℕ} (hn : n ≠ 0) :
    f n = ∏ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  refine g_prod_of_pairwise hmul h1 n.primeFactors (fun p => p ^ n.factorization p) ?_
  intro p hp q hq hpq
  exact Nat.Coprime.pow (n.factorization p) (n.factorization q)
    ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq)

/-- Pointwise bound: `|f n| ≤ C^{ω(n)} / (n · rad n)`. -/
private lemma abs_f_le {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1))
    {n : ℕ} (hn : 1 ≤ n) :
    |f n| ≤ C ^ n.primeFactors.card / ((n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [f_eq_prod_prime_powers hmul h1 hn0, Finset.abs_prod]
  have hstep : ∏ p ∈ n.primeFactors, |f (p ^ n.factorization p)|
      ≤ ∏ p ∈ n.primeFactors, C / (p : ℝ) ^ (n.factorization p + 1) := by
    refine Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => ?_)
    have hp' := Nat.mem_primeFactors.mp hp
    have hk : 1 ≤ n.factorization p := by
      have : p ∈ n.factorization.support := by
        rw [Nat.support_factorization]; exact hp
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp this)
    exact hbd p (n.factorization p) hp'.1 hk
  refine le_trans hstep ?_
  have heq : ∏ p ∈ n.primeFactors, C / (p : ℝ) ^ (n.factorization p + 1)
      = C ^ n.primeFactors.card / ((n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ)) := by
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [Finset.prod_const]
    · have hsplit : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p + 1))
          = (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p))
            * (∏ p ∈ n.primeFactors, (p : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun p _ => by rw [pow_succ])
      rw [hsplit]
      have h1' : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) = (n : ℝ) := by
        have : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p))
            = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p) : ℕ) : ℝ) := by
          rw [Nat.cast_prod]
          exact Finset.prod_congr rfl (fun p _ => (Nat.cast_pow p (n.factorization p)).symm)
        rw [this, ← Nat.prod_primeFactors_pow_factorization hn0]
      have h2' : (∏ p ∈ n.primeFactors, (p : ℝ)) = ((n.primeFactors.prod id : ℕ) : ℝ) := by
        rw [Nat.cast_prod]; simp
      rw [h1', h2']
  rw [heq]

theorem sum_gt_pow_bound_inv_sqrt_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    (hbd : ∀ p k : ℕ, p.Prime → 1 ≤ k → |f (p ^ k)| ≤ C / (p : ℝ) ^ (k + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N L : ℕ, 1 ≤ L →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => L < n), |f n|)
        ≤ K / Real.sqrt (L : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := Commons.NumberTheory.Nat.sum_pow_omega_div_sqrt_rad_le C hC
  refine ⟨K, hKpos, ?_⟩
  intro N L hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsqrtpos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLpos
  have hterm : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => L < n),
      |f n| ≤ (1 / Real.sqrt (L : ℝ)) *
        (C ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) := by
    intro n hnmem
    rw [Finset.mem_filter, Finset.mem_Icc] at hnmem
    obtain ⟨⟨hn1, _⟩, hnL⟩ := hnmem
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hbase := abs_f_le hC hmul h1 hbd hn1
    have hdec : C ^ n.primeFactors.card / ((n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))
        = (1 / Real.sqrt (n : ℝ)) *
            (C ^ n.primeFactors.card /
              (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) := by
      have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hnpos)
      have hsn : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrtn
      have hRn : ((n.primeFactors.prod id : ℕ) : ℝ) ≠ 0 := by
        rw [Nat.cast_ne_zero]
        exact Finset.prod_ne_zero_iff.mpr
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
      field_simp
      rw [pow_two, hs]
    have hle_sqrt : 1 / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt (L : ℝ) := by
      apply one_div_le_one_div_of_le hsqrtpos
      exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt hnL))
    rw [hdec] at hbase
    exact le_trans hbase (mul_le_mul_of_nonneg_right hle_sqrt
      (div_nonneg (pow_nonneg hC _) (mul_nonneg (le_of_lt hsqrtn) (by positivity))))
  calc (∑ n ∈ (Finset.Icc 1 N).filter (fun n => L < n), |f n|)
      ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => L < n),
          (1 / Real.sqrt (L : ℝ)) *
            (C ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (1 / Real.sqrt (L : ℝ)) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => L < n),
            (C ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / Real.sqrt (L : ℝ)) *
          ∑ n ∈ Finset.Icc 1 N,
            (C ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => ?_)
        exact div_nonneg (pow_nonneg hC _) (by positivity)
    _ ≤ (1 / Real.sqrt (L : ℝ)) * K := by
        apply mul_le_mul_of_nonneg_left (hK N) (by positivity)
    _ = K / Real.sqrt (L : ℝ) := by ring

end Commons.NumberTheory.EulerProduct
