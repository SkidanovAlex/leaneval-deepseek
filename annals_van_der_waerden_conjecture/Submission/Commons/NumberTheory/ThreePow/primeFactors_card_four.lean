import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Submission.Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd
import Submission.Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv

namespace Commons.NumberTheory.ThreePow

open Finset

/-! ## A conditional version of `x ↦ 1 - 1/x` that is monotone on `ℕ`

The natural candidate `fun x ↦ 1 - 1/(x:ℝ)` is *not* monotone (at `x = 0` Lean's
convention gives `1/0 = 0`, so the value is `1`).  For applying
`Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le` we only need a globally
monotone function agreeing with `1 - 1/x` on the nonzero arguments, which are the
only ones that occur (primes). -/

/-- `gg x = 0` for `x = 0`, and `gg x = 1 - 1/x` otherwise. -/
noncomputable def gg : ℕ → ℝ := fun x => if x = 0 then 0 else 1 - 1/(x:ℝ)

lemma gg_zero : gg 0 = 0 := by simp [gg]

lemma gg_of_ne {x : ℕ} (hx : x ≠ 0) : gg x = 1 - 1/(x:ℝ) := by simp [gg, hx]

lemma gg_nonneg : ∀ x, 0 ≤ gg x := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [gg_zero]
  · rw [gg_of_ne hx]
    have h1 : (1:ℝ) ≤ (x:ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx))
    have : (1:ℝ)/(x:ℝ) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < (x:ℝ))]; linarith
    linarith

lemma gg_mono : Monotone gg := by
  intro a b hab
  rcases eq_or_ne a 0 with rfl | ha
  · rw [gg_zero]; exact gg_nonneg b
  · have hb : b ≠ 0 := by omega
    rw [gg_of_ne ha, gg_of_ne hb]
    have ha1 : (0:ℝ) < (a:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha)
    have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
    have : (1:ℝ)/(b:ℝ) ≤ (1:ℝ)/(a:ℝ) := one_div_le_one_div_of_le ha1 hab'
    linarith

/-! ## Values of small primes -/

lemma nth_prime_val3 : Nat.nth Nat.Prime 3 = 7 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 7) (by norm_num)
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rwa [hc] at this
lemma nth_prime_val4 : Nat.nth Nat.Prime 4 = 11 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 11) (by norm_num)
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  rwa [hc] at this
lemma nth_prime_val5 : Nat.nth Nat.Prime 5 = 13 := by
  have := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  rwa [hc] at this

/-! ## Lower bounds for `∏ (1 - 1/p)` over small sets of primes -/

/-- Three distinct primes `≥ 7` give `∏ (1 - 1/p) ≥ (6/7)(10/11)(12/13)`. -/
lemma prod_three_bound (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 7 ≤ x)
    (hcard : S.card = 3) :
    (6:ℝ)/7 * (10/11) * (12/13) ≤ ∏ x ∈ S, (1 - 1/(x:ℝ)) := by
  have h := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S 7 hS hm gg gg_mono gg_nonneg
  rw [hcard] at h
  have hcount7 : Nat.count Nat.Prime 7 = 3 := by decide
  have hL : (∏ i ∈ Finset.range 3, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 7 + i)))
      = (6:ℝ)/7 * (10/11) * (12/13) := by
    rw [hcount7]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    rw [nth_prime_val3, nth_prime_val4, nth_prime_val5]
    norm_num [gg]
  have hR : ∏ x ∈ S, gg x = ∏ x ∈ S, (1 - 1/(x:ℝ)) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [gg_of_ne]
    exact (hS x hx).ne_zero
  rw [hL, hR] at h
  exact h

/-- Two distinct primes `≥ 11` give `∏ (1 - 1/p) ≥ (10/11)(12/13)`. -/
lemma prod_two_bound (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 11 ≤ x)
    (hcard : S.card = 2) :
    (10:ℝ)/11 * (12/13) ≤ ∏ x ∈ S, (1 - 1/(x:ℝ)) := by
  have h := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S 11 hS hm gg gg_mono gg_nonneg
  rw [hcard] at h
  have hcount11 : Nat.count Nat.Prime 11 = 4 := by decide
  have hL : (∏ i ∈ Finset.range 2, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 11 + i)))
      = (10:ℝ)/11 * (12/13) := by
    rw [hcount11]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    rw [nth_prime_val4, nth_prime_val5]
    norm_num [gg]
  have hR : ∏ x ∈ S, gg x = ∏ x ∈ S, (1 - 1/(x:ℝ)) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [gg_of_ne]
    exact (hS x hx).ne_zero
  rw [hL, hR] at h
  exact h

/-- A prime different from `2, 3, 5` is at least `7`. -/
lemma seven_le_of_prime {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2) (h3 : x ≠ 3)
    (h5 : x ≠ 5) : 7 ≤ x := by
  by_contra h
  push_neg at h
  have hx2 : 2 ≤ x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx
  · exact h5 rfl
  · norm_num at hx

/-- A prime different from `2, 3, 5, 7` is at least `11`. -/
lemma eleven_le_of_prime {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2) (h3 : x ≠ 3)
    (h5 : x ≠ 5) (h7 : x ≠ 7) : 11 ≤ x := by
  by_contra h
  push_neg at h
  have hx2 : 2 ≤ x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx
  · exact h5 rfl
  · norm_num at hx
  · exact h7 rfl
  · norm_num at hx
  · norm_num at hx
  · norm_num at hx

/-! ## Orders of `3` modulo `5` and `7` -/

lemma orderOf_three_mod_five : orderOf (((3:ℕ)) : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m hm hpos => by interval_cases m <;> decide⟩

lemma orderOf_three_mod_seven : orderOf (((3:ℕ)) : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m hm hpos => by interval_cases m <;> decide⟩

lemma four_dvd_of_five_dvd (k : ℕ) (h : 5 ∣ 3^k - 1) : 4 ∣ k := by
  have h1 := Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd 3 5 (by norm_num) (by norm_num) h
  rw [orderOf_three_mod_five] at h1
  exact h1

lemma six_dvd_of_seven_dvd (k : ℕ) (h : 7 ∣ 3^k - 1) : 6 ∣ k := by
  have h1 := Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd 3 7 (by norm_num) (by norm_num) h
  rw [orderOf_three_mod_seven] at h1
  exact h1

theorem primeFactors_card_four (k : ℕ) (hk : 2 ≤ k)
    (h : (3 ^ k - 1).primeFactors.card = 4) :
    3 ^ (k - 1) - 1 < Nat.totient (3 ^ k - 1) := by
  set n := 3 ^ k - 1 with hn_def
  have hn0 : n ≠ 0 := by
    have h1 : 1 < 3^k := one_lt_pow₀ (by norm_num : (1:ℕ) < 3) (by omega : k ≠ 0)
    rw [hn_def]; omega
  -- membership facts
  have h2mem : 2 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨by norm_num, ?_, hn0⟩
    rw [hn_def, ← ZMod.natCast_eq_zero_iff (3^k - 1) 2]
    rw [Nat.cast_sub (Nat.one_le_pow k 3 (by norm_num)), Nat.cast_pow]
    have h3 : (((3:ℕ)) : ZMod 2) = 1 := by decide
    rw [h3, one_pow]; simp
  have h3not : 3 ∉ n.primeFactors := by
    intro h3
    rw [Nat.mem_primeFactors] at h3
    obtain ⟨_, hdvd, _⟩ := h3
    rw [hn_def] at hdvd
    have hp1 : 3 ∣ 3^k := dvd_pow_self 3 (by omega)
    have h2 : 3 ∣ 3^k - (3^k - 1) := Nat.dvd_sub hp1 hdvd
    have hpow : 1 ≤ 3^k := Nat.one_le_pow k 3 (by norm_num)
    have heq : 3^k - (3^k - 1) = 1 := by omega
    rw [heq] at h2
    norm_num at h2
  -- Euler product over ℝ
  have heuler : (Nat.totient n : ℝ) / (n:ℝ) = ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) := by
    have hh := Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv n hn0
    have h2 := congrArg (fun x : ℚ => (x:ℝ)) hh
    push_cast at h2
    exact h2
  -- the key lower bound for the Euler product
  have hQ : (1/3:ℝ) ≤ ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) := by
    set T := n.primeFactors.erase 2 with hT_def
    have h2notin : 2 ∉ T := fun h => (Finset.mem_erase.mp h).1 rfl
    have hP : n.primeFactors = insert 2 T := (Finset.insert_erase h2mem).symm
    rw [hP, Finset.prod_insert h2notin]
    have hc2 : (1:ℝ) - 1/(((2:ℕ)):ℝ) = 1/2 := by norm_num
    rw [hc2]
    have hTprime : ∀ x ∈ T, Nat.Prime x :=
      fun x hx => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx)
    have hcardT : T.card = 3 := by
      rw [hT_def, Finset.card_erase_of_mem h2mem]; omega
    by_cases h5 : 5 ∈ n.primeFactors
    · by_cases h7 : 7 ∈ n.primeFactors
      · -- impossible: 5, 7 | n forces 12 | k and hence 13, 73 | n, giving ≥ 5 prime factors
        exfalso
        have hd5 : 5 ∣ 3^k - 1 := by
          have := (Nat.mem_primeFactors.mp h5).2.1; rwa [hn_def] at this
        have hd7 : 7 ∣ 3^k - 1 := by
          have := (Nat.mem_primeFactors.mp h7).2.1; rwa [hn_def] at this
        have h4 : 4 ∣ k := four_dvd_of_five_dvd k hd5
        have h6 : 6 ∣ k := six_dvd_of_seven_dvd k hd7
        have h12 : 12 ∣ k := by
          have := Nat.lcm_dvd h4 h6
          rwa [show Nat.lcm 4 6 = 12 from by decide] at this
        have hdiv : 3^12 - 1 ∣ n := by
          rw [hn_def]; exact Nat.pow_sub_one_dvd_pow_sub_one 3 h12
        have h13mem : 13 ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_trans (by norm_num : 13 ∣ 3^12 - 1) hdiv, hn0⟩
        have h73mem : 73 ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_trans (by norm_num : 73 ∣ 3^12 - 1) hdiv, hn0⟩
        have hsub : ({2,5,7,13,73} : Finset ℕ) ⊆ n.primeFactors := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h' | h' | h' | h' | h'
          · rw [h']; exact h2mem
          · rw [h']; exact h5
          · rw [h']; exact h7
          · rw [h']; exact h13mem
          · rw [h']; exact h73mem
        have h5le : 5 ≤ n.primeFactors.card := by
          have hc := Finset.card_le_card hsub
          have hcard5 : ({2,5,7,13,73} : Finset ℕ).card = 5 := by decide
          omega
        omega
      · -- 5 ∈ P, 7 ∉ P
        have h5T : 5 ∈ T := by rw [hT_def, Finset.mem_erase]; exact ⟨by norm_num, h5⟩
        have hT2prime : ∀ x ∈ T.erase 5, Nat.Prime x :=
          fun x hx => hTprime x (Finset.mem_of_mem_erase hx)
        have hT2_11 : ∀ x ∈ T.erase 5, 11 ≤ x := by
          intro x hx
          have hxT : x ∈ T := Finset.mem_of_mem_erase hx
          have hxP : x ∈ n.primeFactors := Finset.mem_of_mem_erase hxT
          have hxne2 : x ≠ 2 := (Finset.mem_erase.mp hxT).1
          have hxne5 : x ≠ 5 := (Finset.mem_erase.mp hx).1
          exact eleven_le_of_prime (hTprime x hxT) hxne2
            (fun hh => h3not (hh ▸ hxP)) hxne5 (fun hh => h7 (hh ▸ hxP))
        have hT2card : (T.erase 5).card = 2 := by
          rw [Finset.card_erase_of_mem h5T]; omega
        have hbnd := prod_two_bound (T.erase 5) hT2prime hT2_11 hT2card
        have hTn : T = insert 5 (T.erase 5) := (Finset.insert_erase h5T).symm
        rw [hTn, Finset.prod_insert (fun h => (Finset.mem_erase.mp h).1 rfl)]
        have hc5 : (1:ℝ) - 1/(((5:ℕ)):ℝ) = 4/5 := by norm_num
        rw [hc5]
        calc (1/3:ℝ) ≤ (1/2) * ((4:ℝ)/5 * ((10:ℝ)/11 * (12/13))) := by norm_num
          _ ≤ (1/2) * ((4:ℝ)/5 * ∏ x ∈ T.erase 5, (1 - 1/(x:ℝ))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hbnd (by norm_num)
          _ = (1/2) * ((4:ℝ)/5 * ∏ x ∈ T.erase 5, (1 - 1/(x:ℝ))) := rfl
    · -- 5 ∉ P
      have hT7 : ∀ x ∈ T, 7 ≤ x := by
        intro x hx
        have hxP : x ∈ n.primeFactors := Finset.mem_of_mem_erase hx
        have hxne2 : x ≠ 2 := (Finset.mem_erase.mp hx).1
        exact seven_le_of_prime (hTprime x hx) hxne2
          (fun hh => h3not (hh ▸ hxP)) (fun hh => h5 (hh ▸ hxP))
      have hbnd := prod_three_bound T hTprime hT7 hcardT
      calc (1/3:ℝ) ≤ (1/2) * ((6:ℝ)/7 * (10/11) * (12/13)) := by norm_num
        _ ≤ (1/2) * ∏ x ∈ T, (1 - 1/(x:ℝ)) :=
            mul_le_mul_of_nonneg_left hbnd (by norm_num)
        _ = (1/2) * ∏ x ∈ T, (1 - 1/(x:ℝ)) := rfl
  -- conclude: `φ n / n ≥ 1/3` gives `n ≤ 3 φ n`
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have hratio : (1/3:ℝ) ≤ (Nat.totient n : ℝ) / (n:ℝ) := by rw [heuler]; exact hQ
  have h3n : n ≤ 3 * Nat.totient n := by
    have h2 : (n:ℝ) * (1/3) ≤ (n:ℝ) * ((Nat.totient n : ℝ) / (n:ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (le_of_lt hnpos)
    have h3 : (n:ℝ) * ((Nat.totient n : ℝ) / (n:ℝ)) = (Nat.totient n : ℝ) := by
      field_simp
    have h4 : (n:ℝ) ≤ 3 * (Nat.totient n : ℝ) := by
      have : (n:ℝ) * (1/3) = (n:ℝ) / 3 := by ring
      rw [this, h3] at h2
      linarith
    exact_mod_cast h4
  -- final arithmetic
  have hpow : 3 ^ (k-1) * 3 = 3^k := by
    rw [← pow_succ]; congr 1; omega
  set a := 3 ^ (k-1) - 1 with ha_def
  have ha : 3 * a + 2 = n := by
    rw [ha_def, hn_def, Nat.mul_sub_left_distrib]
    have h1 : 1 ≤ 3^(k-1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  omega

end Commons.NumberTheory.ThreePow