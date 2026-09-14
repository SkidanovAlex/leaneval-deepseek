import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv
import Submission.Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le
import Submission.Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd

namespace Commons.NumberTheory.TwoPow

open Finset

/-! ## A monotone factor `gg x = (x-1)/x`

Setting `x ↦ (x-1)/x` on `ℕ` (with `(x-1)/x = 1 - 1/x` for `x ≥ 1`) gives a monotone,
nonnegative function to which the general combinatorial bound
`prod_nth_prime_le_prod_of_le` applies. -/

noncomputable def gg : ℕ → ℝ := fun x => ((x : ℝ) - 1) / (x : ℝ)

private lemma gg_nonneg : ∀ x, 0 ≤ gg x := by
  intro x
  unfold gg
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; norm_num
  · apply div_nonneg
    · have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
      linarith
    · positivity

private lemma gg_mono : Monotone gg := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  unfold gg
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, div_le_div_iff₀ hn hn1]
    nlinarith

private lemma gg_eq (x : ℕ) (hx : 1 ≤ x) : gg x = 1 - 1 / (x : ℝ) := by
  unfold gg
  have hxr : (x : ℝ) ≠ 0 := by
    have : 0 < x := by omega
    exact_mod_cast (ne_of_gt this)
  rw [sub_div, div_self hxr]

/-! ## Small primes: counts and values of `Nat.nth Nat.Prime`. -/

private lemma nth_prime_val (i v : ℕ) (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = i) :
    Nat.nth Nat.Prime i = v := by
  rw [← hc]; exact Nat.nth_count hv

private lemma count_prime_five : Nat.count Nat.Prime 5 = 2 := by decide
private lemma count_prime_seven : Nat.count Nat.Prime 7 = 3 := by decide
private lemma nth_prime_two : Nat.nth Nat.Prime 2 = 5 := nth_prime_val 2 5 (by norm_num) (by decide)
private lemma nth_prime_three : Nat.nth Nat.Prime 3 = 7 := nth_prime_val 3 7 (by norm_num) (by decide)
private lemma nth_prime_four : Nat.nth Nat.Prime 4 = 11 := nth_prime_val 4 11 (by norm_num) (by decide)

/-! ## Numerical product bounds over prime sets.

These are the two "generic" lower bounds needed: three primes all `≥ 5`, and three primes
containing `3` but not `2` or `5`. -/

private lemma prod_nth_ge_five (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x)
    (hge : ∀ x ∈ S, 5 ≤ x) (hcard : S.card = 3) :
    (48 : ℝ) / 77 ≤ ∏ x ∈ S, gg x := by
  have hb := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S 5 hS hge gg gg_mono gg_nonneg
  rw [hcard] at hb
  have hL : (∏ i ∈ Finset.range 3, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 5 + i)))
      = (48 : ℝ) / 77 := by
    rw [count_prime_five]
    simp only [Finset.prod_range_succ, Nat.add_zero, Nat.reduceAdd,
      nth_prime_two, nth_prime_three, nth_prime_four]
    norm_num [gg]
  linarith [hb, hL.le]

private lemma prod_nth_ge_seven (T : Finset ℕ) (hT : ∀ x ∈ T, Nat.Prime x)
    (hge : ∀ x ∈ T, 7 ≤ x) (hcard : T.card = 2) :
    (60 : ℝ) / 77 ≤ ∏ x ∈ T, gg x := by
  have hb := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le T 7 hT hge gg gg_mono gg_nonneg
  rw [hcard] at hb
  have hL : (∏ i ∈ Finset.range 2, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 7 + i)))
      = (60 : ℝ) / 77 := by
    rw [count_prime_seven]
    simp only [Finset.prod_range_succ, Nat.add_zero, Nat.reduceAdd,
      nth_prime_three, nth_prime_four]
    norm_num [gg]
  linarith [hb, hL.le]

/-! ## Elementary prime-position facts. -/

private lemma prime_ge_five_of_ne_two_three {x : ℕ} (hx : Nat.Prime x)
    (h2 : x ≠ 2) (h3 : x ≠ 3) : 5 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have h2x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx

private lemma prime_ge_seven_of_ne_two_three_five {x : ℕ} (hx : Nat.Prime x)
    (h2 : x ≠ 2) (h3 : x ≠ 3) (h5 : x ≠ 5) : 7 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have h2x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx
  · exact h5 rfl
  · norm_num at hx

/-! ## Orders of `2` modulo small primes, and the two consequences used to force extra
prime divisors. -/

private lemma orderOf_two_three : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 2)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_seven : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 3)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_eleven : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 10)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 12)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_thirtyone : orderOf (2 : ZMod 31) = 5 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 5)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

/-- If `q ∣ 2^k - 1` then the order of `2` modulo `q` divides `k`. -/
private lemma order_dvd_of_dvd (q k : ℕ) (hq : Nat.Prime q) (h : q ∣ 2 ^ k - 1) :
    orderOf (2 : ZMod q) ∣ k :=
  Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd 2 q (by norm_num) hq.one_le h

/-- Conversely, if the order of `2` modulo `q` divides `k`, then `q ∣ 2^k - 1`. -/
private lemma dvd_of_order_dvd (q k : ℕ) (h : orderOf (2 : ZMod q) ∣ k) : q ∣ 2 ^ k - 1 := by
  have hpow : (2 : ZMod q) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  have hcast : ((2 ^ k : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [Nat.cast_pow, Nat.cast_one]; exact hpow
  have hmod : 2 ^ k ≡ 1 [MOD q] := by
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    exact hcast
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm

private lemma thirteen_dvd_of_three_five_seven (k : ℕ) (_h3 : 3 ∣ 2 ^ k - 1)
    (h5 : 5 ∣ 2 ^ k - 1) (h7 : 7 ∣ 2 ^ k - 1) : 13 ∣ 2 ^ k - 1 := by
  have d5 : orderOf (2 : ZMod 5) ∣ k := order_dvd_of_dvd 5 k (by norm_num) h5
  rw [orderOf_two_five] at d5
  have d7 : orderOf (2 : ZMod 7) ∣ k := order_dvd_of_dvd 7 k (by norm_num) h7
  rw [orderOf_two_seven] at d7
  have d12 : 12 ∣ k := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 4 3) d5 d7
    norm_num at this ⊢
    exact this
  have : orderOf (2 : ZMod 13) ∣ k := by rw [orderOf_two_thirteen]; exact d12
  exact dvd_of_order_dvd 13 k this

private lemma thirtyone_dvd_of_eleven (k : ℕ) (h11 : 11 ∣ 2 ^ k - 1) : 31 ∣ 2 ^ k - 1 := by
  have d11 : orderOf (2 : ZMod 11) ∣ k := order_dvd_of_dvd 11 k (by norm_num) h11
  rw [orderOf_two_eleven] at d11
  have d5 : 5 ∣ k := dvd_trans (by norm_num : (5 : ℕ) ∣ 10) d11
  have : orderOf (2 : ZMod 31) ∣ k := by rw [orderOf_two_thirtyone]; exact d5
  exact dvd_of_order_dvd 31 k this

private lemma seven_dvd_of_thirteen (k : ℕ) (h13 : 13 ∣ 2 ^ k - 1) : 7 ∣ 2 ^ k - 1 := by
  have d13 : orderOf (2 : ZMod 13) ∣ k := order_dvd_of_dvd 13 k (by norm_num) h13
  rw [orderOf_two_thirteen] at d13
  have d3 : 3 ∣ k := dvd_trans (by norm_num : (3 : ℕ) ∣ 12) d13
  have : orderOf (2 : ZMod 7) ∣ k := by rw [orderOf_two_seven]; exact d3
  exact dvd_of_order_dvd 7 k this

/-! ## The main theorem. -/

theorem primeFactors_card_three (k : ℕ) (hk : 2 ≤ k)
    (h : (2 ^ k - 1).primeFactors.card = 3) :
    2 ^ (k - 1) - 1 < Nat.totient (2 ^ k - 1) := by
  set n : ℕ := 2 ^ k - 1 with hn_def
  have hn0 : n ≠ 0 := by
    rw [hn_def]
    have hp : 4 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      norm_num at this ⊢
      omega
    omega
  have hcard : n.primeFactors.card = 3 := by rw [hn_def]; exact h
  have hSprime : ∀ p ∈ n.primeFactors, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  -- `n` is odd, so `2 ∉ n.primeFactors`.
  have h2not : 2 ∉ n.primeFactors := by
    intro h2m
    have h2dvd : 2 ∣ n := (Nat.mem_primeFactors.mp h2m).2.1
    rw [hn_def] at h2dvd
    have hpow : 2 ∣ 2 ^ k :=
      ⟨2 ^ (k - 1), by rw [mul_comm, ← pow_succ]; congr 1; omega⟩
    have h1 : (2 ^ k - 1) + 1 = 2 ^ k := by
      have := Nat.one_le_two_pow (n := k); omega
    have hone : 2 ∣ 1 := (Nat.dvd_add_iff_right h2dvd).mpr (by rw [h1]; exact hpow)
    norm_num at hone
  -- Euler's product formula in `ℝ`.
  have heuler : (Nat.totient n : ℝ) / (n : ℝ) =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hbase := Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv n hn0
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) hbase
    simpa using h2
  -- The key lower bound on the totient density.
  have hratio : (1 / 2 : ℝ) < (Nat.totient n : ℝ) / (n : ℝ) := by
    rw [heuler]
    by_cases h3 : 3 ∈ n.primeFactors
    · by_cases h5 : 5 ∈ n.primeFactors
      · -- Case C: `3, 5` divide `n`; the third prime is `≥ 17`.
        have h5mem : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by norm_num, h5⟩
        have hcard1 : ((n.primeFactors.erase 3).erase 5).card = 1 := by
          rw [Finset.card_erase_of_mem h5mem, Finset.card_erase_of_mem h3, hcard]
        obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard1
        have hr_mem : r ∈ (n.primeFactors.erase 3).erase 5 := by
          rw [hr]; exact Finset.mem_singleton_self r
        have hr_S : r ∈ n.primeFactors :=
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr_mem)
        have hr_ne3 : r ≠ 3 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr_mem)).1
        have hr_ne5 : r ≠ 5 := (Finset.mem_erase.mp hr_mem).1
        have hr_prime : Nat.Prime r := hSprime r hr_S
        have hr_dvd : r ∣ 2 ^ k - 1 := by
          rw [← hn_def]; exact (Nat.mem_primeFactors.mp hr_S).2.1
        have hr_ge17 : 17 ≤ r := by
          by_contra hlt
          rw [not_le] at hlt
          have hr2 : r ≠ 2 := by intro hh; exact h2not (hh ▸ hr_S)
          have hr_ge7 : 7 ≤ r :=
            prime_ge_seven_of_ne_two_three_five hr_prime hr2 hr_ne3 hr_ne5
          have d3 : 3 ∣ 2 ^ k - 1 := by
            rw [← hn_def]; exact (Nat.mem_primeFactors.mp h3).2.1
          have d5 : 5 ∣ 2 ^ k - 1 := by
            rw [← hn_def]; exact (Nat.mem_primeFactors.mp h5).2.1
          -- If `r ≤ 13` we reach a contradiction via a fourth prime divisor.
          have hr_cases : r = 7 ∨ r = 11 ∨ r = 13 := by
            interval_cases r <;>
              first
                | exact Or.inl rfl
                | exact Or.inr (Or.inl rfl)
                | exact Or.inr (Or.inr rfl)
                | (exfalso; norm_num at hr_prime)
          rcases hr_cases with rfl | rfl | rfl
          · have d13 := thirteen_dvd_of_three_five_seven k d3 d5 hr_dvd
            have h13mem : 13 ∈ n.primeFactors := by
              rw [hn_def]
              exact Nat.mem_primeFactors.mpr ⟨by norm_num, d13, by rw [← hn_def]; exact hn0⟩
            have hsub : ({3, 5, 7, 13} : Finset ℕ) ⊆ n.primeFactors := by
              intro x hx
              fin_cases hx <;> assumption
            have h4 : 4 ≤ n.primeFactors.card := by
              calc (4 : ℕ) = ({3, 5, 7, 13} : Finset ℕ).card := by norm_num
                _ ≤ n.primeFactors.card := Finset.card_le_card hsub
            omega
          · have d31 := thirtyone_dvd_of_eleven k hr_dvd
            have h31mem : 31 ∈ n.primeFactors := by
              rw [hn_def]
              exact Nat.mem_primeFactors.mpr ⟨by norm_num, d31, by rw [← hn_def]; exact hn0⟩
            have hsub : ({3, 5, 11, 31} : Finset ℕ) ⊆ n.primeFactors := by
              intro x hx
              fin_cases hx <;> assumption
            have h4 : 4 ≤ n.primeFactors.card := by
              calc (4 : ℕ) = ({3, 5, 11, 31} : Finset ℕ).card := by norm_num
                _ ≤ n.primeFactors.card := Finset.card_le_card hsub
            omega
          · have d7' := seven_dvd_of_thirteen k hr_dvd
            have h7mem : 7 ∈ n.primeFactors := by
              rw [hn_def]
              exact Nat.mem_primeFactors.mpr ⟨by norm_num, d7', by rw [← hn_def]; exact hn0⟩
            have hsub : ({3, 5, 7, 13} : Finset ℕ) ⊆ n.primeFactors := by
              intro x hx
              fin_cases hx <;> assumption
            have h4 : 4 ≤ n.primeFactors.card := by
              calc (4 : ℕ) = ({3, 5, 7, 13} : Finset ℕ).card := by norm_num
                _ ≤ n.primeFactors.card := Finset.card_le_card hsub
            omega
        have hsplit : ∏ x ∈ n.primeFactors, gg x = gg 3 * gg 5 * gg r := by
          have h1 : ∏ x ∈ n.primeFactors, gg x = gg 3 * ∏ x ∈ n.primeFactors.erase 3, gg x := by
            rw [← Finset.prod_erase_mul n.primeFactors gg h3]; ring
          have h2 : ∏ x ∈ n.primeFactors.erase 3, gg x
              = gg 5 * ∏ x ∈ (n.primeFactors.erase 3).erase 5, gg x := by
            rw [← Finset.prod_erase_mul (n.primeFactors.erase 3) gg h5mem]; ring
          have h3r : ∏ x ∈ (n.primeFactors.erase 3).erase 5, gg x = gg r := by
            rw [hr]; simp
          rw [h1, h2, h3r]
          ring
        have hpe : ∏ x ∈ n.primeFactors, gg x =
            ∏ x ∈ n.primeFactors, (1 - 1 / (x : ℝ)) :=
          Finset.prod_congr rfl (fun x hx => gg_eq x (hSprime x hx).one_le)
        rw [← hpe, hsplit]
        have hg3 : gg 3 = (2 : ℝ) / 3 := by unfold gg; norm_num
        have hg5 : gg 5 = (4 : ℝ) / 5 := by unfold gg; norm_num
        have hg17 : gg 17 = (16 : ℝ) / 17 := by unfold gg; norm_num
        have hgr : gg 17 ≤ gg r := gg_mono hr_ge17
        rw [hg3, hg5]
        have hgr' : (16 : ℝ) / 17 ≤ gg r := hg17 ▸ hgr
        nlinarith [hgr']
      · -- Case B: `3` divides `n`, `5` does not.
        have hcardT : (n.primeFactors.erase 3).card = 2 := by
          rw [Finset.card_erase_of_mem h3, hcard]
        have hge : ∀ x ∈ n.primeFactors.erase 3, 7 ≤ x := by
          intro x hx
          have hxS : x ∈ n.primeFactors := Finset.mem_of_mem_erase hx
          have hx3 : x ≠ 3 := (Finset.mem_erase.mp hx).1
          have hx2 : x ≠ 2 := by intro hh; exact h2not (hh ▸ hxS)
          have hx5 : x ≠ 5 := by intro hh; exact h5 (hh ▸ hxS)
          exact prime_ge_seven_of_ne_two_three_five (hSprime x hxS) hx2 hx3 hx5
        have hbound := prod_nth_ge_seven (n.primeFactors.erase 3)
          (fun x hx => hSprime x (Finset.mem_of_mem_erase hx)) hge hcardT
        have hsplit : ∏ x ∈ n.primeFactors, gg x = gg 3 * ∏ x ∈ n.primeFactors.erase 3, gg x := by
          rw [← Finset.prod_erase_mul n.primeFactors gg h3]; ring
        have hpe : ∏ x ∈ n.primeFactors, gg x =
            ∏ x ∈ n.primeFactors, (1 - 1 / (x : ℝ)) :=
          Finset.prod_congr rfl (fun x hx => gg_eq x (hSprime x hx).one_le)
        rw [← hpe, hsplit]
        have hg3 : gg 3 = (2 : ℝ) / 3 := by unfold gg; norm_num
        rw [hg3]
        nlinarith [hbound]
    · -- Case A: `3` does not divide `n`.
      have hge : ∀ x ∈ n.primeFactors, 5 ≤ x := by
        intro x hx
        have hx2 : x ≠ 2 := by intro hh; exact h2not (hh ▸ hx)
        have hx3 : x ≠ 3 := by intro hh; exact h3 (hh ▸ hx)
        exact prime_ge_five_of_ne_two_three (hSprime x hx) hx2 hx3
      have hbound := prod_nth_ge_five n.primeFactors hSprime hge hcard
      have hpe : ∏ x ∈ n.primeFactors, gg x =
          ∏ x ∈ n.primeFactors, (1 - 1 / (x : ℝ)) :=
        Finset.prod_congr rfl (fun x hx => gg_eq x (hSprime x hx).one_le)
      rw [← hpe]
      linarith [hbound]
  -- From the density bound conclude the natural-number inequality.
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn0
    exact_mod_cast this
  have hltR : (n : ℝ) < 2 * (Nat.totient n : ℝ) := by
    have h1 := (lt_div_iff₀ hnpos).mp hratio
    linarith
  have hltN : n < 2 * Nat.totient n := by exact_mod_cast hltR
  have hkey : n - 1 < 2 * Nat.totient n := by omega
  have hrel : 2 * (2 ^ (k - 1) - 1) = n - 1 := by
    rw [hn_def, Nat.mul_sub_left_distrib]
    have hp : 2 * 2 ^ (k - 1) = 2 ^ k := by rw [mul_comm, ← pow_succ]; congr 1; omega
    rw [hp]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hmul : 2 * (2 ^ (k - 1) - 1) < 2 * Nat.totient n := by
    rw [hrel]; exact hkey
  have hgoal : 2 ^ (k - 1) - 1 < Nat.totient n := Nat.lt_of_mul_lt_mul_left hmul
  rwa [hn_def] at hgoal

end Commons.NumberTheory.TwoPow