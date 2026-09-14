import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Choose.Sum

namespace Commons.Algebra.Polynomial

open Finset

/-- Binomial difference identity: `(x + y)^n - y^n = ∑_{r<n} C(n,r) x^{n-r} y^r`. -/
private lemma pow_add_sub_pow {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    (x + y) ^ n - y ^ n = ∑ r ∈ range n, (n.choose r : R) * x ^ (n - r) * y ^ r := by
  rw [add_pow, sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  rw [← sum_range_reflect (fun r => (n.choose r : R) * x ^ (n - r) * y ^ r) n]
  apply sum_congr rfl
  intro k hk
  have hklt : k < n := mem_range.mp hk
  have h1 : n - (n - 1 - k) = k + 1 := by omega
  have h2 : n - (k + 1) = n - 1 - k := by omega
  have h3 : n.choose (n - 1 - k) = n.choose (k + 1) :=
    Nat.choose_symm_of_eq_add (by omega : n = (n - 1 - k) + (k + 1))
  rw [h1, h2, h3]
  ring

/-- Recursion for the signed inclusion–exclusion sum when a new element is inserted. -/
private lemma key_step {ι : Type*} [DecidableEq ι] (a : ι) (T : Finset ι) (ha : a ∉ T)
    (g : ι → ℤ) (m : ℕ) :
    (∑ S ∈ (insert a T).powerset,
        (-1 : ℤ) ^ ((insert a T).card - S.card) * (∑ i ∈ S, g i) ^ m)
      = ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
          * (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ r) := by
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have hfirst : (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card + 1 - S.card) * (∑ i ∈ S, g i) ^ m)
      = - (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ T := Finset.mem_powerset.mp hS
    have hle : S.card ≤ T.card := Finset.card_le_card hSsub
    have he : T.card + 1 - S.card = (T.card - S.card) + 1 := by omega
    rw [he, pow_succ]
    ring
  have hsecond : (∑ S ∈ T.powerset,
        (-1 : ℤ) ^ (T.card + 1 - (insert a S).card) * (∑ i ∈ insert a S, g i) ^ m)
      = ∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (g a + ∑ i ∈ S, g i) ^ m := by
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ T := Finset.mem_powerset.mp hS
    have haS : a ∉ S := fun h => ha (hSsub h)
    have hc : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
    have hs : ∑ i ∈ insert a S, g i = g a + ∑ i ∈ S, g i := Finset.sum_insert haS
    have he : T.card + 1 - (S.card + 1) = T.card - S.card := by omega
    rw [hc, hs, he]
  have hrec : (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (g a + ∑ i ∈ S, g i) ^ m)
      = (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ m)
        + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
            * (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ r) := by
    have perS : ∀ S ∈ T.powerset,
        (-1 : ℤ) ^ (T.card - S.card) * (g a + ∑ i ∈ S, g i) ^ m
        = (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ m
          + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
              * ((-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ r) := by
      intro S hS
      have hpu : (g a + ∑ i ∈ S, g i) ^ m
          = (∑ i ∈ S, g i) ^ m
            + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r) * (∑ i ∈ S, g i) ^ r := by
        rw [← pow_add_sub_pow (g a) (∑ i ∈ S, g i) m]
        ring
      rw [hpu, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [Finset.sum_congr rfl perS, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  rw [hfirst, hsecond, hrec, neg_add_cancel_left]

/-- The signed inclusion–exclusion sum of `m`-th powers of subset sums: for `m ≤ T.card` it
vanishes unless `m = T.card`, in which case it equals `T.card ! · ∏_{i∈T} g i`. -/
private lemma key {ι : Type*} (T : Finset ι) (g : ι → ℤ) :
    ∀ m, m ≤ T.card →
      (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ m)
        = if m = T.card then (T.card.factorial : ℤ) * ∏ i ∈ T, g i else 0 := by
  classical
  induction T using Finset.induction with
  | empty =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp (by simpa using hm)
    rw [hm0]
    simp
  | insert a T ha ih =>
    intro m hm
    rw [Finset.card_insert_of_notMem ha] at hm
    rw [key_step a T ha g m, Finset.card_insert_of_notMem ha]
    have hQ : ∀ r ∈ range m,
        (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (∑ i ∈ S, g i) ^ r)
          = if r = T.card then (T.card.factorial : ℤ) * ∏ i ∈ T, g i else 0 := by
      intro r hr
      exact ih r (by have := mem_range.mp hr; omega)
    rw [Finset.sum_congr rfl (fun r hr => by rw [hQ r hr])]
    by_cases hmc : m = T.card + 1
    · rw [hmc, if_pos rfl, Finset.sum_eq_single T.card]
      · rw [if_pos rfl, Nat.choose_succ_self_right, Finset.prod_insert ha]
        have hexp : T.card + 1 - T.card = 1 := by omega
        rw [hexp, pow_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      · intro b hb hbne
        rw [if_neg hbne, mul_zero]
      · intro hnotin
        exact absurd (mem_range.mpr (Nat.lt_succ_self T.card)) hnotin
    · rw [if_neg hmc]
      apply Finset.sum_eq_zero
      intro r hr
      rw [if_neg (by have := mem_range.mp hr; omega), mul_zero]

/-- The signed inclusion–exclusion sum computing the `(k-1)`-fold finite difference of `x ↦ x ^ k`
is affine in `x`, with slope `k! · ∏ hᵢ`. -/
theorem signed_sum_pow_linear (k : ℕ) (hk : 2 ≤ k) (h : Fin (k - 1) → ℤ) :
    ∃ c : ℤ, ∀ x : ℤ,
      (∑ S : Finset (Fin (k - 1)), (-1 : ℤ) ^ ((k - 1) - S.card) * (x + ∑ i ∈ S, h i) ^ k)
        = (k.factorial : ℤ) * (∏ i : Fin (k - 1), h i) * x + c := by
  classical
  set U : Finset (Fin (k - 1)) := Finset.univ with hU
  have hUc : U.card = k - 1 := by rw [hU]; simp
  set P : ℕ → ℤ := fun m => ∑ S ∈ U.powerset, (-1 : ℤ) ^ ((k - 1) - S.card) * (∑ i ∈ S, h i) ^ m
    with hP
  refine ⟨P k, ?_⟩
  intro x
  have hLHS : (∑ S : Finset (Fin (k - 1)),
        (-1 : ℤ) ^ ((k - 1) - S.card) * (x + ∑ i ∈ S, h i) ^ k)
      = ∑ S ∈ U.powerset, (-1 : ℤ) ^ ((k - 1) - S.card) * (x + ∑ i ∈ S, h i) ^ k := by
    rw [← Finset.powerset_univ (α := Fin (k - 1)), hU]
  rw [hLHS]
  have hPeval : ∀ m, m ≤ U.card →
      P m = if m = U.card then (U.card.factorial : ℤ) * ∏ i ∈ U, h i else 0 := by
    intro m hm
    have hconv : P m
        = (∑ S ∈ U.powerset, (-1 : ℤ) ^ (U.card - S.card) * (∑ i ∈ S, h i) ^ m) := by
      simp only [hP, hUc]
    rw [hconv, key U h m hm]
  have hassembly : (∑ S ∈ U.powerset, (-1 : ℤ) ^ ((k - 1) - S.card) * (x + ∑ i ∈ S, h i) ^ k)
      = ∑ j ∈ range (k + 1), (k.choose j : ℤ) * x ^ j * P (k - j) := by
    calc ∑ S ∈ U.powerset, (-1 : ℤ) ^ ((k - 1) - S.card) * (x + ∑ i ∈ S, h i) ^ k
        = ∑ S ∈ U.powerset, ∑ j ∈ range (k + 1), (-1 : ℤ) ^ ((k - 1) - S.card) *
            (x ^ j * (∑ i ∈ S, h i) ^ (k - j) * (k.choose j : ℤ)) := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [add_pow, Finset.mul_sum]
      _ = ∑ j ∈ range (k + 1), ∑ S ∈ U.powerset, (-1 : ℤ) ^ ((k - 1) - S.card) *
            (x ^ j * (∑ i ∈ S, h i) ^ (k - j) * (k.choose j : ℤ)) := by
          rw [Finset.sum_comm]
      _ = ∑ j ∈ range (k + 1), (k.choose j : ℤ) * x ^ j * P (k - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [hP]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          ring
  rw [hassembly, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  rw [add_left_inj]
  have hinner : ∀ j ∈ range k,
      P (k - (j + 1)) = if j = 0 then (U.card.factorial : ℤ) * ∏ i ∈ U, h i else 0 := by
    intro j hj
    have hjlt : j < k := mem_range.mp hj
    have hm : k - (j + 1) ≤ U.card := by rw [hUc]; omega
    rw [hPeval (k - (j + 1)) hm, hUc]
    by_cases hj0 : j = 0
    · subst hj0; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hj0, if_neg (by omega)]
  have hsumeq : (∑ j ∈ range k, (k.choose (j + 1) : ℤ) * x ^ (j + 1) * P (k - (j + 1)))
      = ∑ j ∈ range k, (k.choose (j + 1) : ℤ) * x ^ (j + 1)
          * (if j = 0 then (U.card.factorial : ℤ) * ∏ i ∈ U, h i else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hinner j hj]
  rw [hsumeq, Finset.sum_eq_single 0]
  · rw [if_pos rfl, Nat.choose_one_right, pow_one]
    have hfac : (k.factorial : ℤ) = (k : ℤ) * ((k - 1).factorial : ℤ) := by
      have hk1 : k = (k - 1) + 1 := by omega
      have hnat : k.factorial = k * (k - 1).factorial := by
        conv_lhs => rw [hk1]
        rw [Nat.factorial_succ, show ((k - 1) + 1) = k from hk1.symm]
      rw [hnat, Nat.cast_mul]
    rw [hfac, hUc]
    have hprod : (∏ i ∈ U, h i) = ∏ i : Fin (k - 1), h i := by rw [hU]
    rw [hprod]
    ring
  · intro b hb hbne
    rw [if_neg hbne, mul_zero]
  · intro hnotin
    exact absurd (mem_range.mpr (by omega : 0 < k)) hnotin

end Commons.Algebra.Polynomial