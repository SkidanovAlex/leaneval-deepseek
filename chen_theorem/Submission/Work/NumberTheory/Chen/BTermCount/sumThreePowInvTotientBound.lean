import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.sumInvTotientLogBound

namespace Work.NumberTheory.Chen.BTermCount

open Finset

/-!
## The bound `Σ_{n ≤ X} 3^{ω n} / φ n ≤ C (log X)^3`

We prove the bound via the Dirichlet-convolution ("divisor expansion") method.

### Squarefree divisors vs. subsets of the prime factors
-/

section SquarefreeDivisors

/-- The map `t ↦ ∏_{p ∈ t} p` is injective on subsets of a set of primes. -/
theorem injOn_prod_powerset (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Set.InjOn (fun t => ∏ p ∈ t, p) (↑(s.powerset) : Set (Finset ℕ)) := by
  intro t ht t' ht' heq
  have ht'' : t ⊆ s := Finset.mem_powerset.mp ht
  have ht''' : t' ⊆ s := Finset.mem_powerset.mp ht'
  have h1 : (∏ p ∈ t, p).primeFactors = t :=
    Nat.primeFactors_prod (fun p hp => hs p (ht'' hp))
  have h2 : (∏ p ∈ t', p).primeFactors = t' :=
    Nat.primeFactors_prod (fun p hp => hs p (ht''' hp))
  have heq' : (∏ p ∈ t, p) = (∏ p ∈ t', p) := heq
  have h3 : (∏ p ∈ t, p).primeFactors = (∏ p ∈ t', p).primeFactors := by rw [heq']
  rwa [h1, h2] at h3

/-- On subsets of `n.primeFactors` the map `t ↦ ∏_{p ∈ t} p` has image exactly the
squarefree divisors of `n`. -/
theorem image_prod_powerset_eq (n : ℕ) (hn : n ≠ 0) :
    (n.primeFactors.powerset).image (fun t => ∏ p ∈ t, p)
      = n.divisors.filter Squarefree := by
  classical
  ext d
  constructor
  · intro hd
    rw [Finset.mem_image] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    rw [Finset.mem_powerset] at ht
    have htprime : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (ht hp)
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn⟩, ?_⟩
    · exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id ht).trans
        (Nat.prod_primeFactors_dvd n)
    · refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp => (htprime p hp).squarefree
      intro a ha b hb hab
      show IsRelPrime a b
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (htprime a ha) (htprime b hb)).mpr hab
  · intro hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hsq⟩ := hd
    refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1.trans hdvd, hn⟩
    · exact Nat.prod_primeFactors_of_squarefree hsq

/-- **Reindexing squarefree divisors as subsets of the prime factors.** -/
theorem sum_squarefree_divisors_eq_sum_powerset (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℝ) :
    ∑ d ∈ n.divisors.filter Squarefree, F d
      = ∑ t ∈ n.primeFactors.powerset, F (∏ p ∈ t, p) := by
  rw [← image_prod_powerset_eq n hn, Finset.sum_image]
  exact injOn_prod_powerset n.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp

/-- `φ (∏_{p ∈ s} p) = ∏_{p ∈ s} (p - 1)` for a finite set of primes. -/
theorem totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  have hm : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => (hs p hp).pos
  have hpf : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hs
  have hkey := Nat.totient_mul_prod_primeFactors (∏ p ∈ s, p)
  rw [hpf] at hkey
  have h2 : (∏ p ∈ s, p) * Nat.totient (∏ p ∈ s, p)
      = (∏ p ∈ s, p) * (∏ p ∈ s, (p - 1)) := by
    rw [Nat.mul_comm (∏ p ∈ s, p) (Nat.totient (∏ p ∈ s, p))]
    exact hkey
  exact Nat.eq_of_mul_eq_mul_left hm h2

/-- **`z ^ ω n` expanded over squarefree divisors.** -/
theorem pow_card_primeFactors_eq_sum_squarefree_divisors (z : ℝ) (n : ℕ) (hn : n ≠ 0) :
    z ^ n.primeFactors.card
      = ∑ d ∈ n.divisors.filter Squarefree, (z - 1) ^ d.primeFactors.card := by
  have hprime : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [sum_squarefree_divisors_eq_sum_powerset n hn]
  have hexp : z ^ n.primeFactors.card
      = ∑ t ∈ n.primeFactors.powerset, (z - 1) ^ t.card := by
    rw [← Finset.prod_const (s := n.primeFactors) z]
    rw [show (∏ _p ∈ n.primeFactors, z)
        = ∏ _p ∈ n.primeFactors, (1 + (z - 1)) from
      Finset.prod_congr rfl fun p _ => by ring]
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl fun t _ => Finset.prod_const (s := t) (z - 1)
  rw [hexp]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  rw [Nat.primeFactors_prod (fun p hp => hprime p (ht hp))]

/-- **Euler product form of `n / φ n`.** -/
theorem totient_div_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ)
      = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hkey := Nat.totient_mul_prod_primeFactors n
  have hcast : (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ))
      = (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hkey
    push_cast at h
    rw [show (∏ i ∈ n.primeFactors, (↑(i - 1) : ℝ))
        = (∏ i ∈ n.primeFactors, ((i : ℝ) - 1)) from
      Finset.prod_congr rfl fun p hp => by
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]] at h
    exact h
  have hB : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have hphi : (Nat.totient n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  rw [Finset.prod_div_distrib, div_eq_div_iff hphi hB]
  rw [← hcast]; ring

end SquarefreeDivisors

noncomputable section

open ArithmeticFunction

/-- `gH n = 1 / φ n` (irrelevant/zero value at `n = 0`, since `φ 0 = 0`). -/
def gH : ArithmeticFunction ℝ where
  toFun n := 1 / (Nat.totient n : ℝ)
  map_zero' := by simp

/-- `hSq a n = a ^ ω n / φ n` if `n` is squarefree, and `0` otherwise. -/
def hSq (a : ℝ) : ArithmeticFunction ℝ where
  toFun n := if Squarefree n then a ^ n.primeFactors.card / (Nat.totient n : ℝ) else 0
  map_zero' := by rw [if_neg not_squarefree_zero]

/-- The summatory function `Σ_{n ≤ X} z^{ω n} / φ n`. -/
def A (z : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, z ^ (n.primeFactors.card) / (Nat.totient n : ℝ)

theorem Ioc_zero_eq_Icc_one (X : ℕ) : Finset.Ioc 0 X = Finset.Icc 1 X := by
  ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- The defining equation of `hSq`. -/
theorem hSq_apply (a : ℝ) (n : ℕ) :
    hSq a n = if Squarefree n then a ^ n.primeFactors.card / (Nat.totient n : ℝ) else 0 := rfl

/-- The defining equation of `gH`. -/
theorem gH_apply (n : ℕ) : gH n = 1 / (Nat.totient n : ℝ) := rfl

/-- **Termwise divisor expansion.** For `z ≥ 1` and `1 ≤ n`,
`z^{ω n}/φ n ≤ ((hSq (z-1)) * gH) n`. -/
theorem pow_omega_div_totient_le_mul (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) :
    z ^ n.primeFactors.card / (Nat.totient n : ℝ) ≤ ((hSq (z - 1)) * gH) n := by
  have hn0 : n ≠ 0 := by omega
  have hz0 : (0 : ℝ) ≤ z - 1 := by linarith
  have hL : z ^ n.primeFactors.card / (Nat.totient n : ℝ)
      = ∑ d ∈ n.divisors.filter Squarefree,
          (z - 1) ^ d.primeFactors.card / (Nat.totient n : ℝ) := by
    rw [pow_card_primeFactors_eq_sum_squarefree_divisors z n hn0, Finset.sum_div]
  have hterm : ∀ d, hSq (z - 1) d * gH (n / d)
      = (if Squarefree d then
          (z - 1) ^ d.primeFactors.card / ((Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ))
        else 0) := by
    intro d
    by_cases hd' : Squarefree d
    · rw [if_pos hd', hSq_apply, gH_apply, if_pos hd']
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    · rw [if_neg hd', hSq_apply, if_neg hd', zero_mul]
  have hmul : ((hSq (z - 1)) * gH) n = ∑ d ∈ n.divisors, hSq (z - 1) d * gH (n / d) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun a b => hSq (z - 1) a * gH b)
  have hR : ∑ d ∈ n.divisors, hSq (z - 1) d * gH (n / d)
      = ∑ d ∈ n.divisors.filter Squarefree,
          (z - 1) ^ d.primeFactors.card / ((Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ)) := by
    rw [Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_filter (p := fun d => Squarefree d)]
  rw [hmul, hL, hR]
  refine Finset.sum_le_sum fun d hd => ?_
  obtain ⟨hddiv, hdsq⟩ := Finset.mem_filter.mp hd
  obtain ⟨hddvd, -⟩ := Nat.mem_divisors.mp hddiv
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvd (by omega)
  have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hddvd) hdpos
  have hpd : (0 : ℝ) < (Nat.totient d : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hdpos)
  have hpm : (0 : ℝ) < (Nat.totient (n / d) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hndpos)
  have htot : (Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ) ≤ (Nat.totient n : ℝ) := by
    have h := Nat.totient_super_multiplicative d (n / d)
    rw [Nat.mul_div_cancel' hddvd] at h
    exact_mod_cast h
  have hle : 1 / (Nat.totient n : ℝ) ≤ 1 / ((Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ)) :=
    one_div_le_one_div_of_le (mul_pos hpd hpm) htot
  have hnn : (0 : ℝ) ≤ (z - 1) ^ d.primeFactors.card := pow_nonneg hz0 _
  calc (z - 1) ^ d.primeFactors.card / (Nat.totient n : ℝ)
      = (z - 1) ^ d.primeFactors.card * (1 / (Nat.totient n : ℝ)) := by ring
    _ ≤ (z - 1) ^ d.primeFactors.card
          * (1 / ((Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ))) :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = (z - 1) ^ d.primeFactors.card
          / ((Nat.totient d : ℝ) * (Nat.totient (n / d) : ℝ)) := by ring

/-- `hSq a n ≥ 0` when `a ≥ 0`. -/
theorem hSq_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ hSq a n := by
  rw [hSq_apply]
  split
  · exact div_nonneg (pow_nonneg ha _) (by positivity)
  · exact le_refl 0

/-- `gH n ≥ 0`. -/
theorem gH_nonneg (n : ℕ) : 0 ≤ gH n := by
  rw [gH_apply]
  exact div_nonneg zero_le_one (by positivity)

/-- **The convolution bound**
`Σ_{n ≤ X} z^{ω n}/φ n ≤ (Σ_{n ≤ X} hSq (z-1) n)(Σ_{n ≤ X} 1/φ n)`. -/
theorem A_le (z : ℝ) (hz : 1 ≤ z) (X : ℕ) :
    A z X ≤ (∑ n ∈ Finset.Icc 1 X, hSq (z - 1) n) * (∑ m ∈ Finset.Icc 1 X, gH m) := by
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := Ioc_zero_eq_Icc_one X
  have hIoc' : Finset.Ioc 0 X = Finset.Icc 1 X := Ioc_zero_eq_Icc_one X
  have step1 : A z X ≤ ∑ n ∈ Finset.Ioc 0 X, ((hSq (z - 1)) * gH) n := by
    rw [A, ← hIoc]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    exact pow_omega_div_totient_le_mul z hz n hn.1
  have step3 : ∀ n ∈ Finset.Ioc 0 X,
      ∑ m ∈ Finset.Ioc 0 (X / n), gH m ≤ ∑ m ∈ Finset.Ioc 0 X, gH m := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro m hm
      rw [Finset.mem_Ioc] at hm ⊢
      exact ⟨hm.1, hm.2.trans (Nat.div_le_self X n)⟩
    · intro m _ _
      exact gH_nonneg m
  calc A z X ≤ ∑ n ∈ Finset.Ioc 0 X, ((hSq (z - 1)) * gH) n := step1
    _ = ∑ n ∈ Finset.Ioc 0 X, (hSq (z - 1)) n * ∑ m ∈ Finset.Ioc 0 (X / n), gH m :=
        ArithmeticFunction.sum_Ioc_mul_eq_sum_sum _ _ X
    _ ≤ ∑ n ∈ Finset.Ioc 0 X, (hSq (z - 1)) n * ∑ m ∈ Finset.Ioc 0 X, gH m :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (step3 n hn)
          (hSq_nonneg (by linarith : (0:ℝ) ≤ z - 1) n)
    _ = (∑ n ∈ Finset.Ioc 0 X, (hSq (z - 1)) n) * (∑ m ∈ Finset.Ioc 0 X, gH m) :=
        (Finset.sum_mul ..).symm
    _ = (∑ n ∈ Finset.Icc 1 X, (hSq (z - 1)) n) * (∑ m ∈ Finset.Icc 1 X, gH m) := by rw [hIoc']

/-- The squarefree-restricted `hSq`-sum is bounded by `A`. -/
theorem sum_hSq_le (a : ℝ) (ha : 0 ≤ a) (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, hSq a n ≤ A a X := by
  have h1 : ∑ n ∈ Finset.Icc 1 X, hSq a n
      = ∑ n ∈ (Finset.Icc 1 X).filter Squarefree,
          a ^ n.primeFactors.card / (Nat.totient n : ℝ) := by
    rw [Finset.sum_filter (p := fun n => Squarefree n)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hSq_apply]
  rw [h1, A]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun n => Squarefree n) (Finset.Icc 1 X)) ?_
  intro n _ _
  exact div_nonneg (pow_nonneg ha _) (by positivity)

/-- `A 1 X` is the sum of `1/φ n`. -/
theorem A_one (X : ℕ) : A 1 X = ∑ n ∈ Finset.Icc 1 X, (1:ℝ) / (Nat.totient n : ℝ) := by
  rw [A]
  exact Finset.sum_congr rfl fun n _ => by rw [one_pow]

/-- `A 1 X` expressed through `gH`. -/
theorem A_one_eq (X : ℕ) : A 1 X = ∑ n ∈ Finset.Icc 1 X, gH n := by
  rw [A_one]
  exact Finset.sum_congr rfl fun n _ => (gH_apply n).symm

end

theorem A_two_le (X : ℕ) : A 2 X ≤ A 1 X * A 1 X := by
  have h21 : (2:ℝ) - 1 = 1 := by norm_num
  have hA1nn : 0 ≤ A 1 X := by
    rw [A_one]; exact Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (by positivity)
  calc A 2 X ≤ (∑ n ∈ Finset.Icc 1 X, hSq ((2:ℝ) - 1) n) * (∑ m ∈ Finset.Icc 1 X, gH m) :=
        A_le 2 (by norm_num) X
    _ = (∑ n ∈ Finset.Icc 1 X, hSq 1 n) * A 1 X := by rw [h21, A_one_eq]
    _ ≤ A 1 X * A 1 X := mul_le_mul_of_nonneg_right (sum_hSq_le 1 (by norm_num) X) hA1nn

theorem A_three_le (X : ℕ) : A 3 X ≤ A 2 X * A 1 X := by
  have h31 : (3:ℝ) - 1 = 2 := by norm_num
  have hA1nn : 0 ≤ A 1 X := by
    rw [A_one]; exact Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (by positivity)
  calc A 3 X ≤ (∑ n ∈ Finset.Icc 1 X, hSq ((3:ℝ) - 1) n) * (∑ m ∈ Finset.Icc 1 X, gH m) :=
        A_le 3 (by norm_num) X
    _ = (∑ n ∈ Finset.Icc 1 X, hSq 2 n) * A 1 X := by rw [h31, A_one_eq]
    _ ≤ A 2 X * A 1 X := mul_le_mul_of_nonneg_right (sum_hSq_le 2 (by norm_num) X) hA1nn

theorem sumThreePowInvTotientBound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X, (3 : ℝ) ^ (n.primeFactors.card) / (Nat.totient n : ℝ))
        ≤ C * (Real.log (X : ℝ)) ^ 3 := by
  obtain ⟨C1, hC1pos, hC1⟩ := sumInvTotientLogBound
  refine ⟨C1^3, by positivity, fun X hX => ?_⟩
  have hA1nn : 0 ≤ A 1 X := by
    rw [A_one]; exact Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (by positivity)
  have h1 : A 1 X ≤ C1 * Real.log (X:ℝ) := by
    rw [A_one]; exact hC1 X hX
  have hchange : A 3 X = ∑ n ∈ Finset.Icc 1 X, (3 : ℝ) ^ (n.primeFactors.card) / (Nat.totient n : ℝ) := rfl
  rw [← hchange]
  calc A 3 X ≤ A 2 X * A 1 X := A_three_le X
    _ ≤ (A 1 X * A 1 X) * A 1 X :=
        mul_le_mul_of_nonneg_right (A_two_le X) hA1nn
    _ = A 1 X ^ 3 := by ring
    _ ≤ (C1 * Real.log (X:ℝ)) ^ 3 := by
        exact pow_le_pow_left₀ hA1nn h1 3
    _ = C1 ^ 3 * (Real.log (X:ℝ)) ^ 3 := by ring

end Work.NumberTheory.Chen.BTermCount
