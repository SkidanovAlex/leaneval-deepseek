import Mathlib

/-!
# The combinatorial identity behind Lemma G (Browning--Le Boudec--Sawin)

If `x, y : Fin (n+1) → R` are two vectors in a commutative monoid satisfying `x i * y j = x j * y i`
for all `i, j`, then for any two exponent vectors `m, m'` of the same total degree `d`,
`∏ i, x i ^ (m i) · ∏ i, y i ^ (m' i) = ∏ i, x i ^ (m' i) · ∏ i, y i ^ (m i)`.

This is the "rank ≤ 1 mod q" statement used to show `gcdMinors2 x y ∣ gcdMinors2 (ν x) (ν y)`.
-/

open Finset

/-- Splitting one factor off a product of powers: if `1 ≤ m a`, then
`∏ i, x i ^ (m i) = x a * ∏ i, x i ^ (update m a (m a - 1) i)`. -/
theorem prod_update_decomp {R : Type*} [CommMonoid R] {n : ℕ} (x : Fin (n + 1) → R)
    (m : Fin (n + 1) → ℕ) (a : Fin (n + 1)) (ha : 1 ≤ m a) :
    (∏ i, x i ^ (m i)) = x a * (∏ i, x i ^ (Function.update m a (m a - 1) i)) := by
  have h1 : (∏ i, x i ^ (m i)) = x a ^ (m a) * ∏ i ∈ univ.erase a, x i ^ (m i) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => x i ^ (m i)) (Finset.mem_univ a)]
  have herase : (∏ i ∈ univ.erase a, x i ^ (Function.update m a (m a - 1) i))
      = ∏ i ∈ univ.erase a, x i ^ (m i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have h2 : (∏ i, x i ^ (Function.update m a (m a - 1) i))
      = x a ^ (m a - 1) * ∏ i ∈ univ.erase a, x i ^ (m i) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => x i ^ (Function.update m a (m a - 1) i)) (Finset.mem_univ a), herase,
      Function.update_self]
  have h3 : x a ^ (m a) = x a * x a ^ (m a - 1) := by
    conv_lhs => rw [show m a = (m a - 1) + 1 from (Nat.succ_pred_eq_of_pos ha).symm]
    rw [pow_succ']
  rw [h1, h2, h3, mul_assoc]

/-- The total degree of `update m a (m a - 1)` is one less than that of `m`, when `m a ≠ 0`. -/
theorem sum_update_decomp {n : ℕ} (m : Fin (n + 1) → ℕ) (a : Fin (n + 1)) (d : ℕ)
    (ha : 1 ≤ m a) (hm : ∑ i, m i = d) :
    ∑ i, Function.update m a (m a - 1) i = d - 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hle : m a ≤ d := by
    rw [← hm]; exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have hsplit : ∑ x ∈ univ \ {a}, m x = d - m a := by
    rw [Finset.sdiff_singleton_eq_erase]
    have h1 : m a + ∑ x ∈ univ.erase a, m x = d := by
      rw [← hm]; exact Finset.add_sum_erase Finset.univ m (Finset.mem_univ a)
    omega
  rw [hsplit]
  omega

/-- The swap identity of Lemma G. -/
theorem veronese_swap {R : Type*} [CommMonoid R] {n : ℕ} (x y : Fin (n + 1) → R)
    (h : ∀ i j, x i * y j = x j * y i) :
    ∀ d (m m' : Fin (n + 1) → ℕ), (∑ i, m i) = d → (∑ i, m' i) = d →
      (∏ i, x i ^ m i) * (∏ i, y i ^ m' i) = (∏ i, x i ^ m' i) * (∏ i, y i ^ m i) := by
  intro d
  refine Nat.strong_induction_on d (fun d ih => ?_)
  intro m m' hm hm'
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hm0 : ∀ i, m i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hm) i (Finset.mem_univ i)
    have hm0' : ∀ i, m' i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hm') i (Finset.mem_univ i)
    simp [hm0, hm0']
  · have hne : (∑ i, m i) ≠ 0 := by rw [hm]; omega
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have ha1 : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr ha
    have hne' : (∑ i, m' i) ≠ 0 := by rw [hm']; omega
    obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have hb1 : 1 ≤ m' b := Nat.one_le_iff_ne_zero.mpr hb
    have hsum1 : ∑ i, Function.update m a (m a - 1) i = d - 1 :=
      sum_update_decomp m a d ha1 hm
    have hsum1' : ∑ i, Function.update m' b (m' b - 1) i = d - 1 :=
      sum_update_decomp m' b d hb1 hm'
    have hlt : d - 1 < d := by omega
    have IH := ih (d - 1) hlt (Function.update m a (m a - 1))
      (Function.update m' b (m' b - 1)) hsum1 hsum1'
    rw [prod_update_decomp x m a ha1, prod_update_decomp y m' b hb1,
        prod_update_decomp x m' b hb1, prod_update_decomp y m a ha1]
    calc (x a * ∏ i, x i ^ Function.update m a (m a - 1) i)
            * (y b * ∏ i, y i ^ Function.update m' b (m' b - 1) i)
          = (x a * y b) * ((∏ i, x i ^ Function.update m a (m a - 1) i)
            * (∏ i, y i ^ Function.update m' b (m' b - 1) i)) := by ac_rfl
      _ = (x b * y a) * ((∏ i, x i ^ Function.update m a (m a - 1) i)
            * (∏ i, y i ^ Function.update m' b (m' b - 1) i)) := by rw [h a b]
      _ = (x b * y a) * ((∏ i, x i ^ Function.update m' b (m' b - 1) i)
            * (∏ i, y i ^ Function.update m a (m a - 1) i)) := by rw [IH]
      _ = (x b * ∏ i, x i ^ Function.update m' b (m' b - 1) i)
            * (y a * ∏ i, y i ^ Function.update m a (m a - 1) i) := by ac_rfl
