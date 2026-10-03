import Mathlib.Data.Nat.GCD.BigOperators
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_eq_prod_factorization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_eq_prod_factorization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mul_of_coprime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Data.Nat

/-- The gcd with a product of two coprime numbers is the product of the gcds. -/
theorem gcd_mul_of_coprime {m n b : ℕ} (h : Nat.Coprime m n) :
    Nat.gcd b (m * n) = Nat.gcd b m * Nat.gcd b n := by
  have hx : Nat.gcd b (m * n) ∣ m * n := Nat.gcd_dvd_right _ _
  have key := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hx
  simp only [Nat.gcd_assoc, Nat.gcd_eq_right (dvd_mul_right m n),
    Nat.gcd_eq_right (dvd_mul_left n m)] at key
  exact key.symm

/-- The gcd with a product of a pairwise coprime family is the product of the
individual gcds. -/
theorem gcd_prod_of_pairwise_coprime {ι : Type*} (s : Finset ι) (m : ι → ℕ) (b : ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j)) :
    Nat.gcd b (∏ i ∈ s, m i) = ∏ i ∈ s, Nat.gcd b (m i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j) :=
      fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcop : Nat.Coprime (m a) (∏ i ∈ s, m i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai.symm ▸ hi))
    rw [gcd_mul_of_coprime hcop, ih hs]

/-- `(∏ b_i) / (∏ a_i) = ∏ (b_i / a_i)` when each `a_i` divides `b_i`. -/
theorem prod_div_prod {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ s, a i ∣ b i) :
    (∏ i ∈ s, b i) / (∏ i ∈ s, a i) = ∏ i ∈ s, (b i / a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx]
    have hxs : ∀ i ∈ s, a i ∣ b i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hprod : (∏ i ∈ s, a i) ∣ (∏ i ∈ s, b i) := Finset.prod_dvd_prod_of_dvd _ _ hxs
    rw [Nat.mul_div_mul_comm (h x (Finset.mem_insert_self x s)) hprod, ih hxs]

end Commons.Data.Nat

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The number of square roots of `-1` modulo a product of a pairwise coprime
family is the product of the numbers of square roots in each factor. -/
theorem ncard_sq_neg_one_prod_of_pairwise_coprime {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j)) :
    ({α : ZMod (∏ i ∈ s, m i) | α ^ 2 = -1}.ncard) =
      ∏ i ∈ s, ({α : ZMod (m i) | α ^ 2 = -1}.ncard) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    have huniv : ({α : ZMod 1 | α ^ 2 = -1} : Set (ZMod 1)) = Set.univ := by
      ext α; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [huniv, Set.ncard_univ, Nat.card_zmod, Finset.prod_empty]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j) :=
      fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcop : Nat.Coprime (m a) (∏ i ∈ s, m i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai.symm ▸ hi))
    rw [sq_roots_neg_one_mul_of_coprime hcop, ih hs]

open Commons.Data.Nat

/-- The main count identity: the number of roots of `X ^ 2 + b ^ 2 = 0` modulo
`d` equals `gcd (b, ∏_{p | d} p ^ (v_p d / 2))` times the number of square
roots of `-1` modulo `d / gcd (b ^ 2) d`. -/
theorem sq_sum_sq_root_count_eq_gcd_mul {d b : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}.ncard) =
      Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) *
        ({α : ZMod (d / Nat.gcd (b ^ 2) d) | α ^ 2 = -1}.ncard) := by
  classical
  have hd0 : d ≠ 0 := hd.ne'
  -- pairwise coprimality of the prime powers `p ^ v_p d`
  have hpp_coprime : ∀ p ∈ d.primeFactors, ∀ q ∈ d.primeFactors, p ≠ q →
      Nat.Coprime (p ^ d.factorization p) (q ^ d.factorization q) := by
    intro p hp q hq hpq
    have hpc : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hqc : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact ((Nat.coprime_primes hpc hqc).mpr hpq).pow _ _
  -- `d = ∏_{p | d} p ^ v_p d`
  have hd_prod : (∏ p ∈ d.primeFactors, p ^ d.factorization p) = d :=
    (Nat.prod_primeFactors_pow_factorization hd0).symm
  -- the modulus `m p` of the reduced equation and its coprimality
  let m : ℕ → ℕ := fun p => p ^ d.factorization p / Nat.gcd (b ^ 2) (p ^ d.factorization p)
  have hm_dvd : ∀ p ∈ d.primeFactors, m p ∣ p ^ d.factorization p :=
    fun p _ => Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have hm_coprime : ∀ p ∈ d.primeFactors, ∀ q ∈ d.primeFactors, p ≠ q →
      Nat.Coprime (m p) (m q) := by
    intro p hp q hq hpq
    exact ((hpp_coprime p hp q hq hpq).coprime_dvd_left (hm_dvd p hp)).coprime_dvd_right
      (hm_dvd q hq)
  -- `∏_{p|d} m p = d / gcd (b^2) d`
  have hgd : Nat.gcd (b ^ 2) d =
      ∏ p ∈ d.primeFactors, Nat.gcd (b ^ 2) (p ^ d.factorization p) := by
    have h := gcd_prod_of_pairwise_coprime d.primeFactors (fun p => p ^ d.factorization p)
      (b ^ 2) hpp_coprime
    rw [hd_prod] at h
    exact h
  have hD : (∏ p ∈ d.primeFactors, m p) = d / Nat.gcd (b ^ 2) d := by
    have key : (∏ p ∈ d.primeFactors, p ^ d.factorization p) /
          (∏ p ∈ d.primeFactors, Nat.gcd (b ^ 2) (p ^ d.factorization p)) =
        ∏ p ∈ d.primeFactors,
          (p ^ d.factorization p / Nat.gcd (b ^ 2) (p ^ d.factorization p)) :=
      prod_div_prod d.primeFactors (fun p => Nat.gcd (b ^ 2) (p ^ d.factorization p))
        (fun p => p ^ d.factorization p) (fun p _ => Nat.gcd_dvd_right _ _)
    calc
      (∏ p ∈ d.primeFactors, m p)
          = ∏ p ∈ d.primeFactors,
              (p ^ d.factorization p / Nat.gcd (b ^ 2) (p ^ d.factorization p)) := by
              simp only [m]
      _ = (∏ p ∈ d.primeFactors, p ^ d.factorization p) /
            (∏ p ∈ d.primeFactors, Nat.gcd (b ^ 2) (p ^ d.factorization p)) := key.symm
      _ = d / Nat.gcd (b ^ 2) d := by rw [hd_prod, ← hgd]
  -- gcd part
  have hprod_g : (∏ p ∈ d.primeFactors, Nat.gcd b (p ^ (d.factorization p / 2))) =
      Nat.gcd b ((Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))) := by
    have hpc : ∀ p ∈ d.primeFactors, ∀ q ∈ d.primeFactors, p ≠ q →
        Nat.Coprime (p ^ (d.factorization p / 2)) (q ^ (d.factorization q / 2)) := by
      intro p hp q hq hpq
      have hpc' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hqc' : q.Prime := Nat.prime_of_mem_primeFactors hq
      exact ((Nat.coprime_primes hpc' hqc').mpr hpq).pow _ _
    exact (gcd_prod_of_pairwise_coprime d.primeFactors
      (fun p => p ^ (d.factorization p / 2)) b hpc).symm
  -- `-1`-root part
  have hprod_M : (∏ p ∈ d.primeFactors,
        ({α : ZMod (m p) | α ^ 2 = -1}.ncard)) =
      ({α : ZMod (d / Nat.gcd (b ^ 2) d) | α ^ 2 = -1}.ncard) := by
    rw [← ncard_sq_neg_one_prod_of_pairwise_coprime d.primeFactors m hm_coprime, hD]
  -- per-prime identity
  have hstep : ∀ p ∈ d.primeFactors,
      ({α : ZMod (p ^ d.factorization p) |
          α ^ 2 + (b : ZMod (p ^ d.factorization p)) ^ 2 = 0}.ncard) =
        Nat.gcd b (p ^ (d.factorization p / 2)) * ({α : ZMod (m p) | α ^ 2 = -1}.ncard) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hge : 1 ≤ d.factorization p :=
      (hpp.dvd_iff_one_le_factorization hd0).mp (Nat.mem_primeFactors.mp hp).2.1
    exact sq_sum_sq_root_count_prime_pow hpp hge
  rw [sq_sum_sq_root_count_eq_prod_factorization hd]
  have hcongr : (∏ p ∈ d.primeFactors,
        ({α : ZMod (p ^ d.factorization p) |
          α ^ 2 + (b : ZMod (p ^ d.factorization p)) ^ 2 = 0}.ncard)) =
      (∏ p ∈ d.primeFactors, Nat.gcd b (p ^ (d.factorization p / 2)) *
        ({α : ZMod (m p) | α ^ 2 = -1}.ncard)) :=
    Finset.prod_congr rfl hstep
  rw [hcongr, Finset.prod_mul_distrib, hprod_g, hprod_M]

end Commons.NumberTheory.FriedlanderIwaniec