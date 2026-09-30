import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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

/-- Insertion recursion for the signed subset sum, carrying the additive shift `z`. -/
private lemma key_step_z {ι : Type*} [DecidableEq ι] (a : ι) (T : Finset ι) (ha : a ∉ T)
    (g : ι → ℤ) (z : ℤ) (m : ℕ) :
    (∑ S ∈ (insert a T).powerset,
        (-1 : ℤ) ^ ((insert a T).card - S.card) * (z + ∑ i ∈ S, g i) ^ m)
      = ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
          * (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ r) := by
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have hfirst : (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card + 1 - S.card) * (z + ∑ i ∈ S, g i) ^ m)
      = - (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ T := Finset.mem_powerset.mp hS
    have hle : S.card ≤ T.card := Finset.card_le_card hSsub
    have he : T.card + 1 - S.card = (T.card - S.card) + 1 := by omega
    rw [he, pow_succ]
    ring
  have hsecond : (∑ S ∈ T.powerset,
        (-1 : ℤ) ^ (T.card + 1 - (insert a S).card) * (z + ∑ i ∈ insert a S, g i) ^ m)
      = ∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + g a + ∑ i ∈ S, g i) ^ m := by
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ T := Finset.mem_powerset.mp hS
    have haS : a ∉ S := fun h => ha (hSsub h)
    have hc : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
    have hs : ∑ i ∈ insert a S, g i = g a + ∑ i ∈ S, g i := Finset.sum_insert haS
    have he : T.card + 1 - (S.card + 1) = T.card - S.card := by omega
    rw [hc, hs, he]
    congr 1
    ring
  have hrec : (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + g a + ∑ i ∈ S, g i) ^ m)
      = (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ m)
        + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
            * (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ r) := by
    have perS : ∀ S ∈ T.powerset,
        (-1 : ℤ) ^ (T.card - S.card) * (z + g a + ∑ i ∈ S, g i) ^ m
        = (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ m
          + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r)
              * ((-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ r) := by
      intro S hS
      have hpu : (z + g a + ∑ i ∈ S, g i) ^ m
          = (z + ∑ i ∈ S, g i) ^ m
            + ∑ r ∈ range m, (m.choose r : ℤ) * (g a) ^ (m - r) * (z + ∑ i ∈ S, g i) ^ r := by
        rw [← pow_add_sub_pow (g a) (z + ∑ i ∈ S, g i) m]
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

/-- The signed inclusion–exclusion sum of `m`-th powers of shifted subset sums: for `m ≤ T.card`
it vanishes unless `m = T.card`, in which case it equals `T.card ! · ∏_{i∈T} g i`. -/
private lemma key_z {ι : Type*} (T : Finset ι) (g : ι → ℤ) (z : ℤ) :
    ∀ m, m ≤ T.card →
      (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ m)
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
    rw [key_step_z a T ha g z m, Finset.card_insert_of_notMem ha]
    have hQ : ∀ r ∈ range m,
        (∑ S ∈ T.powerset, (-1 : ℤ) ^ (T.card - S.card) * (z + ∑ i ∈ S, g i) ^ r)
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

open Finset in
theorem signed_sum_pow_lower {r m : ℕ} (hm : m ≤ r) (h : Fin r → ℤ) (z : ℤ) :
    (∑ S : Finset (Fin r), (-1 : ℤ) ^ (r - S.card) * (z + ∑ i ∈ S, h i) ^ m)
      = if m = r then (r.factorial : ℤ) * ∏ i, h i else 0 := by
  classical
  set U : Finset (Fin r) := Finset.univ with hU
  have hUc : U.card = r := by rw [hU]; simp
  have hgoal : (∑ S : Finset (Fin r), (-1 : ℤ) ^ (r - S.card) * (z + ∑ i ∈ S, h i) ^ m)
      = ∑ S ∈ U.powerset, (-1 : ℤ) ^ (U.card - S.card) * (z + ∑ i ∈ S, h i) ^ m := by
    rw [hUc, ← Finset.powerset_univ (α := Fin r), hU]
  rw [hgoal, key_z U h z m (by rw [hUc]; exact hm), hUc, hU]

end Commons.Algebra.Polynomial
