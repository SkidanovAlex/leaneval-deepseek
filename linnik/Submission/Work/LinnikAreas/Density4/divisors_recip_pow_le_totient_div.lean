import Mathlib

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

/-- Auxiliary: multiplicativity of the reciprocal divisor sum over coprime factors. -/
private lemma sum_recip_divisors_mul_coprime {m n : ℕ} (hmn : m.Coprime n) :
    (∑ d ∈ (m * n).divisors, (1 : ℝ) / (d : ℝ))
      = (∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ)) * ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) := by
  rw [Nat.divisors_mul, Finset.mul_def]
  rw [Finset.sum_image (hmn.mul_injOn_divisors)]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [Nat.cast_mul, one_div_mul_one_div]

/-- Auxiliary: the reciprocal divisor sum of a prime power is at most the Euler product factor. -/
private lemma sum_recip_divisors_prime_pow_le (p N : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ N).divisors, (1 : ℝ) / (d : ℝ)) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hpne : (p : ℝ) ≠ 0 := hppos.ne'
  set r : ℝ := (1 : ℝ) / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hppos]
    linarith
  have hgeom : (∑ x ∈ Finset.range (N + 1), r ^ x) ≤ (1 : ℝ) / (1 - r) := by
    have h1 : (0 : ℝ) < 1 - r := by linarith
    rw [le_div_iff₀ h1]
    have hg : (∑ x ∈ Finset.range (N + 1), r ^ x) * (1 - r) = 1 - r ^ (N + 1) := by
      have h := geom_sum_mul r (N + 1)
      nlinarith [h]
    rw [hg]
    have : 0 ≤ r ^ (N + 1) := pow_nonneg hr0 _
    linarith
  have hfinal : (1 : ℝ) / (1 - r) = (p : ℝ) / ((p : ℝ) - 1) := by
    have h1mr : 1 - r = ((p : ℝ) - 1) / (p : ℝ) := by
      rw [hr, sub_div, div_self hpne]
    rw [h1mr, one_div_div]
  calc (∑ d ∈ (p ^ N).divisors, (1 : ℝ) / (d : ℝ))
      = ∑ x ∈ Finset.range (N + 1), (1 : ℝ) / ((p : ℝ) ^ x) := by
        rw [Nat.sum_divisors_prime_pow hp]; simp only [Nat.cast_pow]
    _ = ∑ x ∈ Finset.range (N + 1), r ^ x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hr, one_div_pow]
    _ ≤ (1 : ℝ) / (1 - r) := hgeom
    _ = (p : ℝ) / ((p : ℝ) - 1) := hfinal

theorem divisors_recip_pow_le_totient_div (N k : ℕ) (hk : Squarefree k) :
    (∑ d ∈ (k ^ N).divisors, (1 : ℝ) / (d : ℝ)) ≤ (k : ℝ) / (Nat.totient k : ℝ) := by
  have main : ∀ k : ℕ, Squarefree k →
      (∑ d ∈ (k ^ N).divisors, (1 : ℝ) / (d : ℝ)) ≤ (k : ℝ) / (Nat.totient k : ℝ) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih hk
    rcases eq_or_ne k 0 with rfl | hk0
    · exfalso
      rw [Nat.squarefree_iff_prime_squarefree] at hk
      exact hk 2 Nat.prime_two (by norm_num)
    · rcases eq_or_ne k 1 with rfl | hk1
      · simp
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hk1
        set m : ℕ := k / p with hm
        have hk_eq : k = p * m := by
          rw [hm, mul_comm]
          exact (Nat.div_mul_cancel hpdvd).symm
        have hmpos : 0 < m := by
          rw [hm]
          exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpdvd) hp.pos
        have hm_lt : m < k := by
          rw [hk_eq]
          exact lt_mul_of_one_lt_left hmpos hp.one_lt
        have hmsf : Squarefree m :=
          Squarefree.squarefree_of_dvd ⟨p, by rw [hk_eq, mul_comm]⟩ hk
        have hpm : p.Coprime m :=
          (hp.coprime_iff_not_dvd).mpr fun hdvd =>
            Nat.squarefree_iff_prime_squarefree.mp hk p hp
              (by rw [hk_eq]; exact mul_dvd_mul_left p hdvd)
        have hS2 := ih m hm_lt hmsf
        have hpmN : (p ^ N).Coprime (m ^ N) := hpm.pow N N
        have hmul := sum_recip_divisors_mul_coprime hpmN
        have hprime := sum_recip_divisors_prime_pow_le p N hp
        have hS2nn : 0 ≤ ∑ d ∈ (m ^ N).divisors, (1 : ℝ) / (d : ℝ) := by
          apply Finset.sum_nonneg
          intro d hd
          have hdpos : (0 : ℝ) < (d : ℝ) := by
            exact_mod_cast Nat.pos_of_mem_divisors hd
          exact div_nonneg zero_le_one hdpos.le
        have hBnn : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
          have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
          exact div_nonneg (by positivity) (by linarith)
        have hstep := mul_le_mul hprime hS2 hS2nn hBnn
        have hphi : (Nat.totient k : ℝ) = ((p : ℝ) - 1) * (Nat.totient m : ℝ) := by
          have hnat : Nat.totient k = (p - 1) * Nat.totient m := by
            rw [hk_eq, Nat.totient_mul hpm, Nat.totient_prime hp]
          rw [hnat, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
        have hk' : (k : ℝ) = (p : ℝ) * (m : ℝ) := by rw [hk_eq, Nat.cast_mul]
        have hkey : ((p : ℝ) / ((p : ℝ) - 1)) * ((m : ℝ) / (Nat.totient m : ℝ))
            = (k : ℝ) / (Nat.totient k : ℝ) := by
          have hpne : (p : ℝ) - 1 ≠ 0 := by
            have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
            linarith
          have hφm : (Nat.totient m : ℝ) ≠ 0 := by
            have : 0 < Nat.totient m := Nat.totient_pos.mpr hmpos
            exact_mod_cast this.ne'
          rw [hk', hphi, div_mul_div_comm]
        calc (∑ d ∈ (k ^ N).divisors, (1 : ℝ) / (d : ℝ))
            = (∑ d ∈ (p ^ N).divisors, (1 : ℝ) / (d : ℝ))
                * ∑ d ∈ (m ^ N).divisors, (1 : ℝ) / (d : ℝ) := by
              rw [hk_eq, mul_pow, hmul]
          _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ((m : ℝ) / (Nat.totient m : ℝ)) := hstep
          _ = (k : ℝ) / (Nat.totient k : ℝ) := hkey
  exact main k hk

end Work.LinnikAreas.Density4
