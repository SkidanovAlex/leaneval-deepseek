import Submission.ZagierHoffmanProof.ATRec

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Polynomial
open scoped BigOperators

/-!
# The main induction for the Anderson–Thakur coefficients

Assembling the increment lemma (`atCoeff_increment_of_ih`), the one-digit increment
(`oneDigit_increment`) and the peeling of the upper digits, this file proves Chen's Theorem 3.1:

  `atCoeff (atIndex n N) = atForm n N`   for `∑_{i<n} N_i ≤ q - 1`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

omit [Field F] [Finite F] in
lemma sub_two_add_one {q : ℕ} (hq : 2 ≤ q) : (q - 2) + 1 = q - 1 := by omega

omit [Field F] [Finite F] in
lemma sub_two_le_sub_one (q : ℕ) : q - 2 ≤ q - 1 :=
  Nat.sub_le_sub_left (show 1 ≤ 2 by norm_num) q

omit [Field F] [Finite F] in
lemma add_two_le_of_lt_sub_one {r j : ℕ} (h : j < r - 1) : j + 2 ≤ r := by omega

omit [Field F] [Finite F] in
lemma lt_of_lt_sub_one {r j : ℕ} (h : j < r - 1) : j < r := by omega

omit [Field F] [Finite F] in
lemma sub_self_sub_one (r : ℕ) : r - 1 - (r - 1) = 0 := Nat.sub_self _

lemma atIndex_congr {n : ℕ} {N N' : ℕ → ℕ} (h : ∀ i, i < n → N i = N' i) :
    atIndex F n N = atIndex F n N' := by
  rw [atIndex, atIndex]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])

lemma atForm_incr (n : ℕ) (N : ℕ → ℕ) (j : ℕ) (hj : j + 2 ≤ n) :
    atForm F n (shiftShape N j 1) = atR F (n - 1 - j) ^ (Nat.card F ^ j) * atForm F n N := by
  rw [shiftShape_one]
  exact atForm_add_one F n N j hj

lemma atForm_incr_top (r : ℕ) (hr : 1 ≤ r) (N : ℕ → ℕ) :
    atForm F r (shiftShape N (r - 1) 1) = atForm F r N := by
  rw [atForm, atForm]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [shiftShape_apply, if_neg (by omega), add_zero]

lemma atForm_incr_zero (r : ℕ) (hr : 2 ≤ r) (N : ℕ → ℕ) :
    atForm F r (shiftShape N 0 1) = atR F (r - 1) * atForm F r N := by
  rw [shiftShape_one, atForm_add_one F r N 0 (by omega)]
  simp

/-- `atForm` of a one-digit shape. -/
lemma atForm_oneDigit (r : ℕ) (hr : 2 ≤ r) (a : ℕ) :
    atForm F r (oneDigit a) = atR F (r - 1) ^ a := by
  rw [atForm, Finset.prod_eq_single 0]
  · rw [oneDigit_apply, if_pos rfl, Nat.pow_zero, mul_one, Nat.sub_zero]
  · intro i hi hi0
    rw [oneDigit_apply, if_neg hi0, zero_mul, pow_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The increment lemma at level `r`, derived from the closed formula at level `r`.** -/
lemma increment_of_formula (r : ℕ) (hr : 1 ≤ r)
    (hP : ∀ N : ℕ → ℕ, (∑ i ∈ Finset.range r, N i ≤ Nat.card F - 1) →
      atCoeff F (atIndex F r N) = atForm F r N)
    (M : ℕ → ℕ) (hM : ∑ i ∈ Finset.range r, M i ≤ Nat.card F - 2) (j : ℕ) (hj : j ≤ r - 1) :
    atCoeff F (atIndex F r (shiftShape M j 1))
      = atR F (r - 1 - j) ^ (Nat.card F ^ j) * atCoeff F (atIndex F r M) := by
  have hjlt : j < r := lt_of_le_of_lt hj (Nat.pred_lt (Nat.one_le_iff_ne_zero.mp hr))
  have hMj : ∑ i ∈ Finset.range r, shiftShape M j 1 i ≤ Nat.card F - 1 := by
    rw [sum_shiftShape, if_pos hjlt]
    calc ∑ i ∈ Finset.range r, M i + 1 ≤ (Nat.card F - 2) + 1 := Nat.add_le_add_right hM 1
      _ ≤ Nat.card F - 1 := by rw [sub_two_add_one (carlitz_card_ge_two F)]
  have hMle : ∑ i ∈ Finset.range r, M i ≤ Nat.card F - 1 :=
    le_trans hM (sub_two_le_sub_one (Nat.card F))
  rw [hP M hMle, hP (shiftShape M j 1) hMj]
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    rw [sub_self_sub_one, atForm_incr_top F r hr M, atR_zero, one_pow, one_mul]
  · exact atForm_incr F r M j (add_two_le_of_lt_sub_one h)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

omit [Field F] [Finite F] in
lemma prod_Icc_one_eq_prod_range {M : Type*} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∏ i ∈ Finset.Icc 1 n, f i) = ∏ i ∈ Finset.range n, f (i + 1) := by
  have hset : Finset.Icc 1 n = (Finset.range n).image (fun i => i + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [hset, Finset.prod_image]
  intro a _ b _ hab
  have h : a + 1 = b + 1 := hab
  omega

/-- The shape obtained from `N` by decreasing the `j`-th digit by one. -/
def decShape (N : ℕ → ℕ) (j : ℕ) : ℕ → ℕ := fun i => N i - if i = j then 1 else 0

@[simp] lemma decShape_apply (N : ℕ → ℕ) (j i : ℕ) :
    decShape N j i = N i - (if i = j then 1 else 0) := rfl

lemma decShape_ne {N : ℕ → ℕ} {j i : ℕ} (h : i ≠ j) : decShape N j i = N i := by
  rw [decShape_apply, if_neg h, Nat.sub_zero]

lemma shiftShape_decShape {N : ℕ → ℕ} {j : ℕ} (hj : 1 ≤ N j) :
    shiftShape (decShape N j) j 1 = N := by
  funext i
  rw [shiftShape_apply]
  by_cases h : i = j
  · subst h
    rw [decShape_apply, if_pos rfl, Nat.sub_add_cancel hj]
  · rw [decShape_ne h, if_neg h, add_zero]

lemma sum_decShape (r : ℕ) (N : ℕ → ℕ) (j : ℕ) (hj : j < r) (hjpos : 1 ≤ N j) :
    (∑ i ∈ Finset.range r, decShape N j i) = (∑ i ∈ Finset.range r, N i) - 1 := by
  have hmem : j ∈ Finset.range r := Finset.mem_range.mpr hj
  have h1 : (∑ i ∈ Finset.range r, decShape N j i)
      = (∑ i ∈ (Finset.range r).erase j, N i) + (N j - 1) := by
    rw [← Finset.sum_erase_add _ _ hmem]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_erase] at hi
      exact decShape_ne hi.1
    · rw [decShape_apply, if_pos rfl]
  have h2 : (∑ i ∈ Finset.range r, N i) = (∑ i ∈ (Finset.range r).erase j, N i) + N j :=
    (Finset.sum_erase_add _ _ hmem).symm
  rw [h1, h2, Nat.add_sub_assoc hjpos]

/-- The product over the shifted digit. -/
lemma prod_Icc_decShape (r : ℕ) (N : ℕ → ℕ) (j : ℕ)
    (hjmem : j ∈ Finset.Icc 1 (r - 1)) (hjpos : 1 ≤ N j) :
    (∏ i ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - i) ^ (N i * Nat.card F ^ i))
      = atR F (r - 1 - j) ^ (Nat.card F ^ j)
        * (∏ i ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - i) ^ (decShape N j i * Nat.card F ^ i)) := by
  rw [← Finset.prod_erase_mul _ _ hjmem, ← Finset.prod_erase_mul _ _ hjmem]
  have herase : (∏ x ∈ (Finset.Icc 1 (r - 1)).erase j,
        atR F (r - 1 - x) ^ (N x * Nat.card F ^ x))
      = (∏ x ∈ (Finset.Icc 1 (r - 1)).erase j,
        atR F (r - 1 - x) ^ (decShape N j x * Nat.card F ^ x)) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_erase] at hi
    rw [decShape_ne hi.1]
  have hdj : decShape N j j = N j - 1 := by rw [decShape_apply, if_pos rfl]
  have hexp : N j * Nat.card F ^ j = Nat.card F ^ j + (N j - 1) * Nat.card F ^ j := by
    have h1 : N j = (N j - 1) + 1 := (Nat.sub_add_cancel hjpos).symm
    nth_rewrite 1 [h1]
    ring
  rw [herase, hdj, hexp, pow_add]
  ring

omit [Field F] [Finite F] in
lemma sub_one_sub_one {q : ℕ} (hq : 1 ≤ q) : (q - 1) - 1 = q - 2 := by omega

/-- The upper-mass of the decreased shape. -/
lemma sum_Icc_decShape (r : ℕ) (N : ℕ → ℕ) (j : ℕ) (hjmem : j ∈ Finset.Icc 1 (r - 1))
    (hjpos : 1 ≤ N j) :
    (∑ i ∈ Finset.Icc 1 (r - 1), decShape N j i)
      = (∑ i ∈ Finset.Icc 1 (r - 1), N i) - 1 := by
  have h1 : (∑ i ∈ Finset.Icc 1 (r - 1), decShape N j i)
      = (∑ i ∈ (Finset.Icc 1 (r - 1)).erase j, N i) + (N j - 1) := by
    rw [← Finset.sum_erase_add _ _ hjmem]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_erase] at hi
      exact decShape_ne hi.1
    · rw [decShape_apply, if_pos rfl]
  have h2 : (∑ i ∈ Finset.Icc 1 (r - 1), N i)
      = (∑ i ∈ (Finset.Icc 1 (r - 1)).erase j, N i) + N j :=
    (Finset.sum_erase_add _ _ hjmem).symm
  rw [h1, h2, Nat.add_sub_assoc hjpos]

/-- ★ **Peeling the upper digits**: for a shape of level `r` with `∑ N_i ≤ q - 1`, `atCoeff` at
`atIndex r N` is the product of the upper `R`-factors times the one-digit value. -/
theorem peel (r : ℕ) (hr : 2 ≤ r)
    (hincr : ∀ (M : ℕ → ℕ), (∑ i ∈ Finset.range r, M i ≤ Nat.card F - 2) → ∀ k, 1 ≤ k →
      k ≤ r - 1 →
      atCoeff F (atIndex F r (shiftShape M k 1))
        = atR F (r - 1 - k) ^ (Nat.card F ^ k) * atCoeff F (atIndex F r M)) :
    ∀ (N : ℕ → ℕ), (∑ i ∈ Finset.range r, N i ≤ Nat.card F - 1) →
      atCoeff F (atIndex F r N)
        = (∏ j ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - j) ^ (N j * Nat.card F ^ j))
          * atCoeff F (atIndex F r (oneDigit (N 0))) := by
  have aux : ∀ t (N : ℕ → ℕ), (∑ i ∈ Finset.range r, N i ≤ Nat.card F - 1) →
      (∑ j ∈ Finset.Icc 1 (r - 1), N j) = t →
      atCoeff F (atIndex F r N)
        = (∏ j ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - j) ^ (N j * Nat.card F ^ j))
          * atCoeff F (atIndex F r (oneDigit (N 0))) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro N hN ht
      by_cases hzero : (∑ j ∈ Finset.Icc 1 (r - 1), N j) = 0
      · have hprod : (∏ j ∈ Finset.Icc 1 (r - 1),
            atR F (r - 1 - j) ^ (N j * Nat.card F ^ j)) = 1 := by
          refine Finset.prod_eq_one (fun j hj => ?_)
          have hj0 : N j = 0 := by
            have hle := Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _) hj
            omega
          rw [hj0, zero_mul, pow_zero]
        rw [hprod, one_mul]
        congr 1
        refine atIndex_congr F (fun i hi => ?_)
        by_cases hi0 : i = 0
        · rw [hi0, oneDigit_apply, if_pos rfl]
        · have hmem : i ∈ Finset.Icc 1 (r - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hi0' : N i = 0 := by
            have hle := Finset.single_le_sum (f := N) (fun k _ => Nat.zero_le _) hmem
            omega
          rw [hi0', oneDigit_apply, if_neg hi0]
      · obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.Icc 1 (r - 1), N j ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact hzero (Finset.sum_eq_zero (fun j hj => hcon j hj))
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
        have hjr : j ≤ r - 1 := (Finset.mem_Icc.mp hjmem).2
        have hrne : r ≠ 0 := by omega
        have hjlt : j < r := lt_of_le_of_lt hjr (Nat.pred_lt hrne)
        have hjpos : 1 ≤ N j := Nat.one_le_iff_ne_zero.mpr hjne
        have htpos : 0 < t := by
          rw [← ht]
          exact lt_of_lt_of_le (Nat.pos_of_ne_zero hjne)
            (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _) hjmem)
        have hdecle : (∑ i ∈ Finset.range r, decShape N j i)
            = (∑ i ∈ Finset.range r, N i) - 1 := sum_decShape r N j hjlt hjpos
        have hdecN : (∑ i ∈ Finset.range r, decShape N j i) ≤ Nat.card F - 2 := by
          rw [hdecle]
          refine le_trans (Nat.sub_le_sub_right hN 1) ?_
          rw [sub_one_sub_one (le_trans (by norm_num : 1 ≤ 2) (carlitz_card_ge_two F))]
        have hdecNle : (∑ i ∈ Finset.range r, decShape N j i) ≤ Nat.card F - 1 :=
          le_trans hdecN (sub_two_le_sub_one (Nat.card F))
        have hcomm : (∑ i ∈ Finset.Icc 1 (r - 1), decShape N j i) = t - 1 := by
          rw [sum_Icc_decShape r N j hjmem hjpos, ← ht]
        have hstep := hincr (decShape N j) hdecN j hj1 hjr
        rw [shiftShape_decShape hjpos] at hstep
        have hIH := ih (t - 1) (Nat.sub_lt htpos (by omega)) (decShape N j) hdecNle hcomm
        have hz : decShape N j 0 = N 0 := decShape_ne (by omega : (0 : ℕ) ≠ j)
        rw [hstep, hIH, prod_Icc_decShape F r N j hjmem hjpos, hz]
        ring
  intro N hN
  exact aux (∑ j ∈ Finset.Icc 1 (r - 1), N j) N hN rfl

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

omit [Field F] [Finite F] in
lemma sub_one_eq_sub_two_add_one {r : ℕ} (hr : 2 ≤ r) : r - 1 = (r - 2) + 1 := by omega

omit [Field F] [Finite F] in
lemma sub_sub_sub_cancel {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n - 1) - 1 - (k - 1) = n - 1 - k := by omega

/-- The closed formula at the one-digit shapes. -/
theorem oneDigit_formula (r : ℕ) (hr : 2 ≤ r)
    (hincr : ∀ (M : ℕ → ℕ), (∑ i ∈ Finset.range r, M i ≤ Nat.card F - 2) → ∀ k, 1 ≤ k →
      k ≤ r - 1 →
      atCoeff F (atIndex F r (shiftShape M k 1))
        = atR F (r - 1 - k) ^ (Nat.card F ^ k) * atCoeff F (atIndex F r M))
    (a : ℕ) (ha : a ≤ Nat.card F - 1) :
    atCoeff F (atIndex F r (oneDigit a)) = atForm F r (oneDigit a) := by
  induction a with
  | zero =>
    rw [atForm_oneDigit F r hr 0, pow_zero]
    have hidx : atIndex F r (oneDigit 0) = Nat.card F ^ r - 1 := by
      rw [atIndex, oneDigit_weighted F r 0 (by omega)]
      exact Nat.sub_zero _
    rw [hidx, atCoeff_card_pow_sub_one]
  | succ a ih =>
    have haa : a + 1 ≤ Nat.card F - 1 := ha
    have hinc := oneDigit_increment F r hr a haa
      (fun j M hM hj1 hj2 => hincr M hM j hj1 hj2)
    have hia : atCoeff F (atIndex F r (oneDigit a)) = atForm F r (oneDigit a) :=
      ih (Nat.le_of_succ_le ha)
    rw [hinc, hia, atForm_oneDigit F r hr a, atForm_oneDigit F r hr (a + 1), ← pow_succ']

/-- `atForm` splits into the upper `R`-factors and the lowest digit. -/
lemma atForm_eq_prod (r : ℕ) (hr : 2 ≤ r) (N : ℕ → ℕ) :
    atForm F r N
      = (∏ j ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - j) ^ (N j * Nat.card F ^ j))
        * atR F (r - 1) ^ N 0 := by
  have h1 : atForm F r N
      = (∏ i ∈ Finset.range (r - 2),
            atR F (r - 2 + 1 - (i + 1)) ^ (N (i + 1) * Nat.card F ^ (i + 1)))
        * atR F (r - 2 + 1) ^ N 0 := by
    rw [atForm, sub_one_eq_sub_two_add_one hr, Finset.prod_range_succ']
    rw [Nat.sub_zero, Nat.pow_zero, mul_one]
  have h2 : (∏ j ∈ Finset.Icc 1 (r - 1), atR F (r - 1 - j) ^ (N j * Nat.card F ^ j))
      = ∏ i ∈ Finset.range (r - 2),
          atR F (r - 2 + 1 - (i + 1)) ^ (N (i + 1) * Nat.card F ^ (i + 1)) := by
    rw [prod_Icc_one_eq_prod_range (r - 1)
      (fun j => atR F (r - 1 - j) ^ (N j * Nat.card F ^ j)), sub_one_eq_sub_two_add_one hr,
      Finset.prod_range_succ]
    rw [Nat.sub_self, atR_zero, one_pow, mul_one]
  rw [h1, h2, sub_one_eq_sub_two_add_one hr]

/-- ★★★ **Chen's Theorem 3.1**: for a shape `N` of level `n` with `∑_{i<n} N_i ≤ q - 1`, the
Anderson–Thakur coefficient at the special index is the closed product form. -/
theorem atCoeff_atIndex_eq_atForm : ∀ (n : ℕ), 1 ≤ n → ∀ (N : ℕ → ℕ),
    (∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) →
    atCoeff F (atIndex F n N) = atForm F n N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn N hN
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      rw [atForm, Finset.range_zero, Finset.prod_empty]
      refine atCoeff_eq_one_of_lt F ?_
      have hsum : (∑ i ∈ Finset.range 1, N i * Nat.card F ^ i) = N 0 := by
        rw [Finset.sum_range_one, Nat.pow_zero, mul_one]
      have hN0 : N 0 ≤ Nat.card F - 1 := by
        have := hN
        rw [Finset.sum_range_one] at this
        exact this
      rw [atIndex, hsum, pow_one]
      have hlt : Nat.card F - 1 < Nat.card F :=
        Nat.pred_lt (Nat.one_le_iff_ne_zero.mp (le_trans (by norm_num : 1 ≤ 2) (carlitz_card_ge_two F)))
      exact lt_of_le_of_lt (Nat.sub_le _ _) hlt
    · have hn2 : 2 ≤ n := h2
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) hn2
      have hn1 : 1 ≤ n - 1 := Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
      have hP : ∀ M : ℕ → ℕ, (∑ i ∈ Finset.range (n - 1), M i ≤ Nat.card F - 1) →
          atCoeff F (atIndex F (n - 1) M) = atForm F (n - 1) M := by
        intro M hM
        exact ih (n - 1) (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hnpos)) hn1 M hM
      have hincr_prev := increment_of_formula F (n - 1) hn1 hP
      have hincr : ∀ (M : ℕ → ℕ), (∑ i ∈ Finset.range n, M i ≤ Nat.card F - 2) → ∀ k, 1 ≤ k →
          k ≤ n - 1 →
          atCoeff F (atIndex F n (shiftShape M k 1))
            = atR F (n - 1 - k) ^ (Nat.card F ^ k) * atCoeff F (atIndex F n M) := by
        intro M hM k hk1 hkn
        refine atCoeff_increment_of_ih F n hn2 M k hk1 hkn hM ?_
        intro M' hM'
        have h := hincr_prev M' hM' (k - 1) (Nat.sub_le_sub_right hkn 1)
        rw [sub_sub_sub_cancel hk1 (by omega)] at h
        exact h
      have h1d : ∀ a : ℕ, a ≤ Nat.card F - 1 →
          atCoeff F (atIndex F n (oneDigit a)) = atForm F n (oneDigit a) :=
        fun a ha => oneDigit_formula F n hn2 hincr a ha
      have hpeel := peel F n hn2 hincr
      have hN0 : N 0 ≤ Nat.card F - 1 :=
        le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hnpos)) hN
      rw [hpeel N hN, h1d (N 0) hN0, atForm_eq_prod F n hn2 N, atForm_oneDigit F n hn2 (N 0)]

end ZagierHoffmanPositiveChar
