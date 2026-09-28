import Mathlib
import Submission.Work.HP.DyadicDefs

/-!
# Reindexing the dyadic sum: `Kset` vs `Nset`

The two index sets of the dyadic-sum bookkeeping are

* `Kset r M` : monotone `k : Fin r → ℕ` in the box `0 ≤ k ≤ M` with `∑ j, k j ≤ M`;
* `Nset N r M` : `n : Fin r → ℕ` in the box with `∑ i, n i * (r - i) ≤ M`.

They are matched by the prefix-sum / difference-vector correspondence
`n ↦ toK n` and `k ↦ toN k`.  The main content of this file is that `toK`
is a bijection from `Nset N r M` onto `Kset r M` (for `r ≤ N`) which preserves
the exponent, i.e. `bigE N r (toK r n) = bigE' N r n`, whence the two power
sums are equal.
-/

namespace Work.HP.dyadic

open Finset
open Work.HP

/-! ### `toK` as a prefix sum over `Finset.Iic` -/

lemma toK_eq_sum_Iic (r : ℕ) (n : Fin r → ℕ) (i : Fin r) :
    toK r n i = ∑ k ∈ Finset.Iic i, n k := by
  rw [toK]; congr 1; ext k; simp [Finset.mem_Iic]

lemma Iic_eq_filter {r : ℕ} (j : Fin r) :
    Finset.Iic j = Finset.univ.filter (fun k : Fin r => k ≤ j) := by
  ext k; simp [Finset.mem_Iic]

lemma Ici_eq_filter {r : ℕ} (k : Fin r) :
    Finset.Ici k = Finset.univ.filter (fun j : Fin r => k ≤ j) := by
  ext j; simp [Finset.mem_Ici]

lemma Iic_eq_singleton_zero {r : ℕ} (i : Fin r) (h : (i : ℕ) = 0) :
    Finset.Iic i = {i} := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def]
  constructor
  · intro hk; exact Fin.ext (by omega)
  · intro hk; rw [hk]

lemma Iic_pred_eq_Iio {r : ℕ} (i : Fin r) (hi : (i : ℕ) ≠ 0) :
    Finset.Iic (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin r) = Finset.Iio i := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]
  omega

/-! ### Round trips between `toK` and `toN` -/

lemma toN_succ (n : ℕ) (k : Fin (n+1) → ℕ) (i : Fin n) :
    toN (n+1) k i.succ = k i.succ - k i.castSucc := by
  simp only [toN]
  have hne : ¬((i.succ : Fin (n+1)) : ℕ) = 0 := by simp
  rw [ite_eq_right hne]
  congr 2

lemma Iio_succ_eq_Iic_castSucc (n : ℕ) (i : Fin n) :
    Finset.Iio (i.succ : Fin (n+1)) = Finset.Iic (i.castSucc : Fin (n+1)) := by
  ext k
  simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def, Fin.val_succ,
    Fin.val_castSucc]
  omega

theorem toN_toK (r : ℕ) (n : Fin r → ℕ) : toN r (toK r n) = n := by
  funext i
  simp only [toN, toK_eq_sum_Iic]
  by_cases hi : (i : ℕ) = 0
  · rw [ite_eq_left hi, Iic_eq_singleton_zero i hi, Finset.sum_singleton, Nat.sub_zero]
  · rw [ite_eq_right hi]
    rw [Iic_pred_eq_Iio i hi, ← Finset.Iio_insert i,
      Finset.sum_insert (by simp [Finset.mem_Iio])]
    omega

theorem toK_toN (r : ℕ) {k : Fin r → ℕ} (hk : Monotone k) : toK r (toN r k) = k := by
  cases r with
  | zero => funext i; exact i.elim0
  | succ n =>
    funext i
    refine Fin.induction ?base ?step i
    · rw [toK_eq_sum_Iic, Iic_eq_singleton_zero (0 : Fin (n+1)) rfl, Finset.sum_singleton]
      simp [toN]
    · intro i ih
      have hnotmem : (i.succ : Fin (n+1)) ∉ Finset.Iic (i.castSucc : Fin (n+1)) := by
        simp only [Finset.mem_Iic, Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
      have hset : Finset.Iic (i.succ : Fin (n+1)) = insert i.succ (Finset.Iic i.castSucc) := by
        rw [← Finset.Iio_insert i.succ, Iio_succ_eq_Iic_castSucc]
      rw [toK_eq_sum_Iic, hset, Finset.sum_insert hnotmem, toN_succ n k i,
        ← toK_eq_sum_Iic, ih]
      have hle : k i.castSucc ≤ k i.succ := hk (by simp [Fin.le_def])
      omega

/-! ### The total prefix sum -/

theorem sum_toK (r : ℕ) (n : Fin r → ℕ) :
    (∑ j, toK r n j) = ∑ i, n i * wval r i := by
  simp only [toK_eq_sum_Iic, Iic_eq_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter]
  rw [show Finset.univ.filter (fun j : Fin r => k ≤ j) = Finset.Ici k from
    (Ici_eq_filter k).symm]
  rw [Finset.sum_const, Fin.card_Ici]
  simp [wval, smul_eq_mul, mul_comm]

/-! ### The arithmetic identity `∑_{j ≥ i} cval j = Sval i` -/

lemma eq_pred_mul_add (c a : ℕ) (h : 1 ≤ a) : a * c = (a-1)*c + c := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

lemma mul_eq_pred_mul_pred_add (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = (a-1)*(b-1) + (a + b - 1) := by
  have h : a + b - 1 = (a-1) + (b-1) + 1 := by omega
  rw [h]
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-- The one-step recurrence for `S m = (r - m) * (N - max m 2)`. -/
lemma S_eq_succ_add (N r : ℕ) (hrN : r ≤ N) {m : ℕ} (hm : m < r) :
    (r - m) * (N - max m 2) =
      (r - (m+1)) * (N - max (m+1) 2)
        + (if m < 2 then N - 2 else N + r - 1 - 2*m) := by
  rcases m with _ | _ | m
  · have hr1 : 1 ≤ r := hm
    simp only [Nat.zero_add, ite_eq_left (by norm_num : (0:ℕ) < 2),
      max_eq_right (by norm_num : (0:ℕ) ≤ 2), max_eq_right (by norm_num : (1:ℕ) ≤ 2)]
    exact eq_pred_mul_add (N-2) r hr1
  · have hr2 : 1 ≤ r - 1 := by omega
    simp only [Nat.zero_add, ite_eq_left (by norm_num : (1:ℕ) < 2),
      max_eq_right (by norm_num : (1:ℕ) ≤ 2), max_eq_right (by norm_num : (2:ℕ) ≤ 2)]
    exact eq_pred_mul_add (N-2) (r-1) hr2
  · rw [ite_eq_right (by omega : ¬ (m+2 < 2)),
        max_eq_left (by omega : (2:ℕ) ≤ m+2),
        max_eq_left (by omega : (2:ℕ) ≤ m+3)]
    have h1 : r - (m+3) = (r - (m+2)) - 1 := by omega
    have h2 : N - (m+3) = (N - (m+2)) - 1 := by omega
    have h3 : N + r - 1 - 2*(m+2) = (r - (m+2)) + (N - (m+2)) - 1 := by omega
    rw [h1, h2, h3]
    exact mul_eq_pred_mul_pred_add (r - (m+2)) (N - (m+2)) (by omega) (by omega)

lemma Ico_eq_insert_Ico_succ {k r : ℕ} (h : k < r) :
    Finset.Ico k r = insert k (Finset.Ico (k+1) r) := by
  ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega

/-- Telescoping an `Ico`-sum of a recurrence that ends at `0`. -/
lemma sum_Ico_of_recurrence (S g : ℕ → ℕ) (r : ℕ) (hr : S r = 0)
    (h : ∀ m, m < r → S m = S (m+1) + g m) :
    ∀ i, i ≤ r → S i = ∑ m ∈ Finset.Ico i r, g m := by
  intro i hi
  exact Nat.decreasingInduction
    (motive := fun i _ => S i = ∑ m ∈ Finset.Ico i r, g m)
    (fun k hk ih => by
      rw [h k hk, ih, Ico_eq_insert_Ico_succ hk,
        Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
      exact Nat.add_comm _ _)
    (by rw [hr]; simp)
    hi

/-- Closed form of the sum of `cval` over the interval `[i, r)`. -/
theorem cval_Ico_sum (N r : ℕ) (hrN : r ≤ N) (i : ℕ) (hi : i ≤ r) :
    (r - i) * (N - max i 2)
      = ∑ m ∈ Finset.Ico i r, (if m < 2 then N - 2 else N + r - 1 - 2 * m) := by
  have hSr : (r - r) * (N - max r 2) = 0 := by simp
  exact sum_Ico_of_recurrence (fun m => (r - m) * (N - max m 2))
    (fun m => if m < 2 then N - 2 else N + r - 1 - 2 * m) r hSr
    (fun m hm => S_eq_succ_add N r hrN hm) i hi

/-- Reindexing the `Ici`-sum over `Fin r` as an interval sum over `ℕ`. -/
theorem sum_Ici_cval (N r : ℕ) (i : Fin r) :
    (∑ j ∈ Finset.Ici i, cval N r j)
      = ∑ m ∈ Finset.Ico (i : ℕ) r,
          (if m < 2 then N - 2 else N + r - 1 - 2 * m) := by
  rw [← Fin.map_valEmbedding_Ici i]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- The key arithmetic identity behind the reindexing: the suffix sum of `cval` is `Sval`. -/
theorem Sval_eq_sum_cval (N r : ℕ) (hrN : r ≤ N) (i : Fin r) :
    Sval N r i = ∑ j ∈ Finset.Ici i, cval N r j := by
  rw [sum_Ici_cval]
  exact cval_Ico_sum N r hrN (i : ℕ) (le_of_lt i.isLt)

/-! ### The exponent identity -/

theorem bigE_toK (N r : ℕ) (hrN : r ≤ N) (n : Fin r → ℕ) :
    bigE N r (toK r n) = bigE' N r n := by
  rw [bigE, bigE']
  simp only [toK_eq_sum_Iic, Iic_eq_filter, Finset.sum_filter, Finset.sum_mul, ite_mul,
    zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  rw [show Finset.univ.filter (fun j : Fin r => i ≤ j) = Finset.Ici i from
    (Ici_eq_filter i).symm]
  rw [← Finset.mul_sum, ← Sval_eq_sum_cval N r hrN i]

/-! ### Membership of the two index sets -/

lemma one_le_wval {r : ℕ} (i : Fin r) : 1 ≤ wval r i := by
  simp only [wval]; omega

theorem toK_mem_Kset (N r M : ℕ) {n : Fin r → ℕ} (hn : n ∈ Nset N r M) :
    toK r n ∈ Kset r M := by
  rw [Nset, Finset.mem_filter] at hn
  rw [Kset, Finset.mem_filter]
  obtain ⟨hnbox, hnsum⟩ := hn
  simp only [piBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] at hnbox
  refine ⟨?_, ?_, ?_⟩
  · simp only [piBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    intro j
    calc toK r n j = ∑ k ∈ Finset.Iic j, n k := toK_eq_sum_Iic r n j
      _ ≤ ∑ k ∈ Finset.Iic j, n k * wval r k :=
            Finset.sum_le_sum (fun k _ =>
              Nat.le_mul_of_pos_right (n k) (lt_of_lt_of_le Nat.zero_lt_one (one_le_wval k)))
      _ ≤ ∑ k, n k * wval r k := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun k _ _ => Nat.zero_le _)
      _ ≤ M := hnsum
  · intro a b hab
    rw [toK_eq_sum_Iic, toK_eq_sum_Iic]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by
        simp only [Finset.mem_Iic] at hx ⊢
        exact le_trans hx hab)
      (fun x _ _ => Nat.zero_le _)
  · rw [sum_toK]
    exact hnsum

theorem toN_mem_Nset (N r M : ℕ) {k : Fin r → ℕ} (hk : k ∈ Kset r M) :
    toN r k ∈ Nset N r M := by
  rw [Kset, Finset.mem_filter] at hk
  rw [Nset, Finset.mem_filter]
  obtain ⟨hkbox, hkmono, hksum⟩ := hk
  simp only [piBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] at hkbox
  refine ⟨?_, ?_⟩
  · simp only [piBox, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    intro i
    exact le_trans (Nat.sub_le _ _) (hkbox i)
  · rw [← sum_toK, toK_toN r hkmono]
    exact hksum

/-! ### The reindexing theorem -/

theorem reindex (N r : ℕ) (hrN : r ≤ N) (M : ℕ) :
    (∑ k ∈ Kset r M, (2:ℝ) ^ (bigE N r k)) = ∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n) := by
  symm
  refine Finset.sum_bij (fun n _ => toK r n) ?_ ?_ ?_ ?_
  · intro n hn
    exact toK_mem_Kset N r M hn
  · intro n₁ _ n₂ _ heq
    rw [← toN_toK r n₁, heq, toN_toK r n₂]
  · intro k hk
    exact ⟨toN r k, toN_mem_Nset N r M hk,
      toK_toN r ((Finset.mem_filter.mp hk).2.1)⟩
  · intro n _
    exact congrArg (fun e => (2:ℝ) ^ e) (bigE_toK N r hrN n).symm

end Work.HP.dyadic
