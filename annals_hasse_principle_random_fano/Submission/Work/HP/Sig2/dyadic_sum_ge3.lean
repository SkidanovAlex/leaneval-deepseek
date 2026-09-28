import Mathlib
import Submission.Work.HP.DyadicDefs
import Submission.Work.HP.dyadic.SumDefs
import Submission.Work.HP.dyadic.pow_bigE_eq
import Submission.Work.HP.dyadic.L_arith

set_option autoImplicit false

namespace Work.HP.Sig2

open Finset Work.HP
open Work.HP.dyadic

open scoped BigOperators

/-! ## Part 1: the reindexing identity `Kset ↔ Nset` -/

/-- Reindex a sum over the initial segment `{j : j ≤ i}` of `Fin r` as a sum over
`Finset.range (i.1 + 1)`. -/
lemma sum_Iic_range {M : Type*} [AddCommMonoid M] (r : ℕ) (i : Fin r) (F : Fin r → M) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin r => j ≤ i), F j)
      = ∑ m ∈ Finset.range (i.1 + 1), (if h : m < r then F ⟨m, h⟩ else 0) := by
  apply Finset.sum_bij (fun (a : Fin r) (_ : a ∈ Finset.univ.filter (fun j : Fin r => j ≤ i)) => a.1)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Fin.le_def.mp ha.2)
  · intro a1 ha1 a2 ha2 h; exact Fin.ext h
  · intro b hb
    rw [Finset.mem_range] at hb
    exact ⟨⟨b, Nat.lt_of_lt_of_le hb (Nat.succ_le_of_lt i.isLt)⟩, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Fin.le_def.mpr (Nat.lt_succ_iff.mp hb)⟩, rfl⟩
  · intro a ha
    rw [dif_pos a.isLt]

/-- Reindex a sum over the final segment `{i : j ≤ i}` of `Fin r` as a sum over
`Finset.range (r - j.1)`. -/
lemma sum_Ici_range {M : Type*} [AddCommMonoid M] (r : ℕ) (j : Fin r) (F : Fin r → M) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin r => j ≤ i), F i)
      = ∑ m ∈ Finset.range (r - j.1), (if h : j.1 + m < r then F ⟨j.1 + m, h⟩ else 0) := by
  apply Finset.sum_bij (fun (a : Fin r) (_ : a ∈ Finset.univ.filter (fun i : Fin r => j ≤ i)) => a.1 - j.1)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact Nat.sub_lt_sub_right (Fin.le_def.mp ha.2) a.isLt
  · intro a1 ha1 a2 ha2 h
    rw [Finset.mem_filter] at ha1 ha2
    have h1 : j.1 ≤ a1.1 := Fin.le_def.mp ha1.2
    have h2 : j.1 ≤ a2.1 := Fin.le_def.mp ha2.2
    have hh : a1.1 - j.1 + j.1 = a2.1 - j.1 + j.1 := by rw [h]
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at hh
    exact Fin.ext hh
  · intro b hb
    rw [Finset.mem_range] at hb
    have hbr : j.1 + b < r := by omega
    refine ⟨⟨j.1 + b, hbr⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Fin.le_def.mpr (Nat.le_add_right j.1 b)⟩
    · exact Nat.add_sub_cancel_left j.1 b
  · intro a ha
    rw [Finset.mem_filter] at ha
    have h1 : j.1 ≤ a.1 := Fin.le_def.mp ha.2
    rw [dif_pos (by omega : j.1 + (a.1 - j.1) < r)]
    congr 1
    exact Fin.ext (Nat.add_sub_of_le h1).symm

/-- Successive differences are a left inverse to prefix sums. -/
lemma toN_toK (r : ℕ) (n : Fin r → ℕ) : toN r (toK r n) = n := by
  funext i
  have key : ∀ (j : Fin r), toK r n j
      = ∑ m ∈ Finset.range (j.1 + 1), (if h : m < r then n ⟨m, h⟩ else 0) := by
    intro j
    rw [toK]
    exact sum_Iic_range r j n
  rw [toN]
  by_cases h0 : (i : ℕ) = 0
  · rw [if_pos h0, key i, h0, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    rw [dif_pos (by omega : 0 < r)]
    congr 1
    exact Fin.ext (by simp only [Fin.val_mk]; omega)
  · rw [if_neg h0]
    have hidx : (⟨i.1 - 1, by have := i.isLt; omega⟩ : Fin r).1 + 1 = i.1 := by
      simp only [Fin.val_mk]; omega
    rw [key i, key ⟨i.1 - 1, by have := i.isLt; omega⟩, hidx, Finset.sum_range_succ,
      Nat.add_sub_cancel_left, dif_pos i.isLt]

/-- Prefix sums are a left inverse to successive differences, on monotone vectors. -/
lemma toK_toN (r : ℕ) (k : Fin r → ℕ) (hk : Monotone k) : toK r (toN r k) = k := by
  funext i
  rw [toK, sum_Iic_range r i (toN r k)]
  have key : ∀ (n : ℕ) (hn : n < r),
      ∑ m ∈ Finset.range (n+1), (if h : m < r then toN r k ⟨m,h⟩ else 0) = k ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [Finset.sum_range_one, dif_pos (by omega : 0 < r), toN]
      simp only [if_true, Nat.sub_zero]
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, ih (by omega : n < r)]
      have hD : (if h : n + 1 < r then toN r k ⟨n + 1, h⟩ else 0)
          = k ⟨n + 1, hn⟩ - k ⟨n, by omega⟩ := by
        rw [dif_pos (by omega : n + 1 < r), toN]
        simp only [Fin.val_mk]
        rw [if_neg (by omega : ¬ (n + 1 = 0))]
        congr 1
      rw [hD]
      exact Nat.add_sub_of_le (hk (Fin.le_def.mpr (by simp only [Fin.val_mk]; omega)))
  exact key i.1 i.isLt

/-- Summation by parts: swapping the prefix-sum index with a suffix sum. -/
lemma swap_sum (r : ℕ) (n X : Fin r → ℕ) :
    ∑ i, toK r n i * X i
      = ∑ j, n j * (∑ i ∈ Finset.univ.filter (fun i : Fin r => j ≤ i), X i) := by
  simp only [toK, Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : j ≤ i <;> simp [h]

/-- `wval r j` is the cardinality of the final segment `{i : j ≤ i}`. -/
lemma wval_eq_sum_one (r : ℕ) (j : Fin r) :
    wval r j = ∑ i ∈ Finset.univ.filter (fun i : Fin r => j ≤ i), (1:ℕ) := by
  rw [wval, sum_Ici_range]
  have h : ∀ m ∈ Finset.range (r - j.1), (if h : j.1 + m < r then (1:ℕ) else 0) = 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [dif_pos (by omega)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The prefix-sum vector of `n` has total mass `∑ n i * wval r i`. -/
lemma sum_toK (r : ℕ) (n : Fin r → ℕ) :
    ∑ j, toK r n j = ∑ i, n i * wval r i := by
  have h := swap_sum r n (fun _ => (1:ℕ))
  simp only [mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [wval_eq_sum_one]

/-- The local recurrence for `Sval`: `Sval i = Sval (i+1) + cval i`. -/
lemma Sval_shift (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) (i : Fin r) :
    Sval N r i = (if h : (i:ℕ)+1 < r then Sval N r ⟨(i:ℕ)+1,h⟩ else 0) + cval N r i := by
  simp only [Sval, cval, wval, alpha]
  by_cases hi2 : (i:ℕ) < 2
  · have h1 : (i:ℕ)+1 < r := by omega
    rw [dif_pos h1, if_pos hi2]
    rw [max_eq_right (by omega : (i:ℕ) ≤ 2), max_eq_right (by omega : (i:ℕ)+1 ≤ 2)]
    have hR : r - (i:ℕ) = (r - ((i:ℕ)+1)) + 1 := by omega
    rw [hR]; ring
  · rw [if_neg hi2]
    rw [max_eq_left (by omega : 2 ≤ (i:ℕ)), max_eq_left (by omega : 2 ≤ (i:ℕ)+1)]
    by_cases h1 : (i:ℕ)+1 < r
    · rw [dif_pos h1]
      have hR : r - (i:ℕ) = (r - ((i:ℕ)+1)) + 1 := by omega
      have hA : N - (i:ℕ) = (N - ((i:ℕ)+1)) + 1 := by omega
      have hC : N + r - 1 - 2*(i:ℕ) = (N - ((i:ℕ)+1)) + (r - ((i:ℕ)+1)) + 1 := by omega
      rw [hR, hA, hC]; ring
    · rw [dif_neg h1]
      have ha : (i:ℕ) = r - 1 := by omega
      rw [ha]
      have h1' : r - (r-1) = 1 := by omega
      rw [h1']; omega

/-- Splitting the final segment of `j` into `j` and the final segment of its successor. -/
lemma sum_Ici_succ (r : ℕ) (F : Fin r → ℕ) (j : Fin r) (h : j.1 + 1 < r) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => j ≤ i), F i
      = F j + ∑ i ∈ Finset.univ.filter (fun i : Fin r => (⟨j.1 + 1, h⟩ : Fin r) ≤ i), F i := by
  have hset : Finset.univ.filter (fun i : Fin r => j ≤ i)
      = insert j (Finset.univ.filter (fun i : Fin r => (⟨j.1 + 1, h⟩ : Fin r) ≤ i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hji
      rcases eq_or_lt_of_le hji with heq | hlt
      · exact Or.inl heq.symm
      · right
        refine Fin.le_def.mpr ?_
        show j.1 + 1 ≤ i.1
        have := Fin.lt_def.mp hlt
        omega
    · rintro (heq | hle)
      · rw [heq]
      · exact le_trans (Fin.le_def.mpr (by show j.1 ≤ (⟨j.1 + 1, h⟩ : Fin r).1; simp only [Fin.val_mk]; omega)) hle
  rw [hset, Finset.sum_insert]
  · rw [Finset.mem_filter]
    rintro ⟨-, hle⟩
    have := Fin.le_def.mp hle
    simp only [Fin.val_mk] at this
    omega

/-- `Sval` is the closed form of the suffix sum of `cval`. -/
lemma Sval_eq_sum_cval (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) (j : Fin r) :
    Sval N r j = ∑ i ∈ Finset.univ.filter (fun i : Fin r => j ≤ i), cval N r i := by
  have key : ∀ k, ∀ (i : ℕ) (hi : i < r), (r - 1) - i = k →
      Sval N r ⟨i, hi⟩ = ∑ x ∈ Finset.univ.filter (fun x : Fin r => (⟨i,hi⟩ : Fin r) ≤ x), cval N r x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi hk
      by_cases hlast : i = r - 1
      · subst hlast
        rw [Sval_shift N r hr hrN ⟨r-1, hi⟩,
          dif_neg (by simp only [Fin.val_mk]; omega : ¬ ((⟨r-1,hi⟩:Fin r).1 + 1 < r))]
        simp only [zero_add]
        symm
        rw [show Finset.univ.filter (fun x : Fin r => (⟨r-1,hi⟩:Fin r) ≤ x) = {⟨r-1,hi⟩} from by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hle
            refine Fin.ext ?_
            show x.1 = r - 1
            have hd : (⟨r-1,hi⟩:Fin r).1 = r - 1 := rfl
            have hle' := Fin.le_def.mp hle
            rw [hd] at hle'
            omega
          · intro heq; rw [heq], Finset.sum_singleton]
      · have hlt : i + 1 < r := by omega
        have hk' : (r - 1) - (i + 1) < k := by omega
        have ih' := ih ((r-1)-(i+1)) hk' (i+1) hlt rfl
        rw [Sval_shift N r hr hrN ⟨i,hi⟩, dif_pos hlt,
          sum_Ici_succ r (cval N r) ⟨i,hi⟩ hlt, ih']
        ac_rfl
  exact key ((r-1) - j.1) j.1 j.isLt rfl

/-- The exponent identity: prefix sums turn `bigE'` into `bigE`. -/
lemma bigE_toK (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) (n : Fin r → ℕ) :
    bigE N r (toK r n) = bigE' N r n := by
  rw [bigE, bigE', swap_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Sval_eq_sum_cval N r hr hrN i]

lemma toK_monotone (r : ℕ) (n : Fin r → ℕ) : Monotone (toK r n) := by
  intro i j hij
  rw [toK, toK]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, le_trans hx.2 hij⟩
  · intro x _ _; exact Nat.zero_le _

lemma toN_le (r : ℕ) (k : Fin r → ℕ) (i : Fin r) : toN r k i ≤ k i := by
  rw [toN]; exact Nat.sub_le _ _

lemma toK_apply_le (r : ℕ) (n : Fin r → ℕ) (i : Fin r) :
    toK r n i ≤ ∑ j, n j * wval r j := by
  rw [toK]
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => j ≤ i), n j
      ≤ ∑ j, n j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => Nat.zero_le _)
    _ ≤ ∑ j, n j * wval r j :=
        Finset.sum_le_sum (fun j _ => Nat.le_mul_of_pos_right (n j) (by have := Work.HP.dyadic.wval_pos j; omega))

lemma mem_piBox_iff (r M : ℕ) (n : Fin r → ℕ) : n ∈ piBox r M ↔ ∀ i, n i ≤ M := by
  rw [piBox, Fintype.mem_piFinset]
  simp only [Finset.mem_range]
  exact ⟨fun h i => Nat.lt_succ_iff.mp (h i), fun h i => Nat.lt_succ_of_le (h i)⟩

/-- The reindexing identity: summing over monotone vectors `k` of the box with total
mass `≤ M` equals summing over difference vectors `n` with weighted mass `≤ M`. -/
theorem reindex (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) (M : ℕ) :
    (∑ k ∈ Kset r M, (2:ℝ) ^ (bigE N r k)) = ∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n) := by
  apply Finset.sum_bij (fun (k : Fin r → ℕ) (_ : k ∈ Kset r M) => toN r k)
  · intro k hk
    have hk' : k ∈ piBox r M ∧ Monotone k ∧ (∑ j, k j) ≤ M := by
      simpa only [Kset, Finset.mem_filter] using hk
    obtain ⟨hkbox, hkmono, hksum⟩ := hk'
    rw [Nset, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_piBox_iff] at hkbox ⊢
      intro i
      exact le_trans (toN_le r k i) (hkbox i)
    · rw [← sum_toK r (toN r k), toK_toN r k hkmono]
      exact hksum
  · intro k1 hk1 k2 hk2 heq
    have hm1 : Monotone k1 := (by
      simpa only [Kset, Finset.mem_filter] using hk1 : k1 ∈ piBox r M ∧ Monotone k1 ∧ _).2.1
    have hm2 : Monotone k2 := (by
      simpa only [Kset, Finset.mem_filter] using hk2 : k2 ∈ piBox r M ∧ Monotone k2 ∧ _).2.1
    rw [← toK_toN r k1 hm1, heq, toK_toN r k2 hm2]
  · intro n hn
    rw [Nset, Finset.mem_filter] at hn
    obtain ⟨hnbox, hnsum⟩ := hn
    refine ⟨toK r n, ?_, toN_toK r n⟩
    rw [Kset, Finset.mem_filter]
    refine ⟨?_, toK_monotone r n, ?_⟩
    · rw [mem_piBox_iff] at hnbox ⊢
      intro i
      exact le_trans (toK_apply_le r n i) hnsum
    · rw [sum_toK]; exact hnsum
  · intro k hk
    have hkmono : Monotone k := (by
      simpa only [Kset, Finset.mem_filter] using hk : k ∈ piBox r M ∧ Monotone k ∧ _).2.1
    rw [← bigE_toK N r hr hrN (toN r k), toK_toN r k hkmono]

/-! ## Part 2: the counting estimate `sum_bound` -/

lemma headPart_mem_piBox {r M : ℕ} (hr : 3 ≤ r) {n : Fin r → ℕ} (hn : n ∈ piBox r M) :
    headPart r hr n ∈ piBox 3 M := by
  rw [mem_piBox_iff] at hn ⊢
  intro i; exact hn (headIdx r hr i)

lemma tailPart_mem_piBox {r M : ℕ} (hr : 3 ≤ r) {n : Fin r → ℕ} (hn : n ∈ piBox r M) :
    tailPart r hr n ∈ piBox (r-3) M := by
  rw [mem_piBox_iff] at hn ⊢
  intro j; exact hn (tailIdx r hr j)

lemma glue_mem_piBox {r M : ℕ} (hr : 3 ≤ r) {v : Fin 3 → ℕ} {u : Fin (r-3) → ℕ}
    (hv : v ∈ piBox 3 M) (hu : u ∈ piBox (r-3) M) : glue r hr v u ∈ piBox r M := by
  rw [mem_piBox_iff] at hv hu ⊢
  intro i
  simp only [glue]
  split_ifs with h
  · exact hv ⟨(i:ℕ), h⟩
  · exact hu ⟨(i:ℕ)-3, by have := i.isLt; omega⟩

lemma glue_headPart_tailPart (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) :
    glue r hr (headPart r hr n) (tailPart r hr n) = n := by
  funext i
  simp only [glue, headPart, tailPart, headIdx, tailIdx]
  by_cases h : (↑i : ℕ) < 3
  · rw [dif_pos h]
  · rw [dif_neg h]
    congr 1
    exact Fin.ext (by show ↑i - 3 + 3 = (↑i : ℕ); omega)

lemma headPart_glue (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) (u : Fin (r-3) → ℕ) :
    headPart r hr (glue r hr v u) = v := by
  funext i
  simp [headPart, glue, headIdx]

lemma tailPart_glue (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) (u : Fin (r-3) → ℕ) :
    tailPart r hr (glue r hr v u) = u := by
  funext j
  simp [tailPart, glue, tailIdx]

lemma sum_head (r : ℕ) (hr : 3 ≤ r) (f : Fin r → ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => (i:ℕ) < 3), f i
      = ∑ i : Fin 3, f (headIdx r hr i) := by
  apply Finset.sum_bij (fun (i : Fin r)
        (hi : i ∈ Finset.univ.filter (fun i : Fin r => (i:ℕ) < 3)) =>
      (⟨(i:ℕ), (Finset.mem_filter.mp hi).2⟩ : Fin 3))
  · intro i hi; exact Finset.mem_univ _
  · intro i1 h1 i2 h2 heq
    exact Fin.ext (by simpa using congrArg Fin.val heq)
  · intro j _
    refine ⟨headIdx r hr j, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, j.isLt⟩
    · exact Fin.ext rfl
  · intro i hi
    exact congrArg f (Fin.ext rfl)

lemma sum_tail (r : ℕ) (hr : 3 ≤ r) (f : Fin r → ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin r => ¬ (i:ℕ) < 3), f i
      = ∑ j : Fin (r-3), f (tailIdx r hr j) := by
  apply Finset.sum_bij (fun (i : Fin r)
        (hi : i ∈ Finset.univ.filter (fun i : Fin r => ¬ (i:ℕ) < 3)) =>
      (⟨(i:ℕ)-3, by have := (Finset.mem_filter.mp hi).2; have := i.isLt; omega⟩ : Fin (r-3)))
  · intro i hi; exact Finset.mem_univ _
  · intro i1 h1 i2 h2 heq
    have hh : (i1:ℕ) - 3 = (i2:ℕ) - 3 := by simpa using congrArg Fin.val heq
    have e1 : 3 ≤ (i1:ℕ) := by have := (Finset.mem_filter.mp h1).2; omega
    have e2 : 3 ≤ (i2:ℕ) := by have := (Finset.mem_filter.mp h2).2; omega
    exact Fin.ext (by omega)
  · intro j _
    refine ⟨tailIdx r hr j, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp only [tailIdx, Fin.val_mk]; omega⟩
    · exact Fin.ext (by simp only [tailIdx, Fin.val_mk]; omega)
  · intro i hi
    exact congrArg f (Fin.ext (by simp only [tailIdx, Fin.val_mk]; have := (Finset.mem_filter.mp hi).2; omega))

lemma sval_eq_headW_tailW (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) :
    sval r n = headW r hr (headPart r hr n) + tailW r hr (tailPart r hr n) := by
  simp only [sval, headW, tailW, headPart, tailPart]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin r))
        (fun i : Fin r => (i:ℕ) < 3) (fun i => n i * wval r i)]
  rw [sum_head r hr, sum_tail r hr]

lemma Pval_eq_tailD (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) :
    Pval r n = tailD r hr (tailPart r hr n) := by
  simp only [Pval, tailD, tailPart]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin r))
        (fun i : Fin r => (i:ℕ) < 3) (fun i => n i * dval r i)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin r => (i:ℕ) < 3), n i * dval r i = 0 := by
    rw [sum_head r hr]
    apply Finset.sum_eq_zero
    intro i _
    rw [dval_headIdx]; ring
  rw [h0, zero_add, sum_tail r hr]

lemma sval_glue (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) (u : Fin (r-3) → ℕ) :
    sval r (glue r hr v u) = headW r hr v + tailW r hr u := by
  rw [sval_eq_headW_tailW r hr, headPart_glue, tailPart_glue]

lemma Pval_glue (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) (u : Fin (r-3) → ℕ) :
    Pval r (glue r hr v u) = tailD r hr u := by
  rw [Pval_eq_tailD r hr, tailPart_glue]

lemma sum_piBox_glue (r M : ℕ) (hr : 3 ≤ r) (F : (Fin r → ℕ) → ℝ) :
    ∑ n ∈ piBox r M, F n
      = ∑ v ∈ piBox 3 M, ∑ u ∈ piBox (r-3) M, F (glue r hr v u) := by
  have hprod : (∑ v ∈ piBox 3 M, ∑ u ∈ piBox (r-3) M, F (glue r hr v u))
      = ∑ p ∈ (piBox 3 M) ×ˢ (piBox (r-3) M), F (glue r hr p.1 p.2) :=
    (Finset.sum_product (piBox 3 M) (piBox (r-3) M)
      (fun p : (Fin 3 → ℕ) × (Fin (r-3) → ℕ) => F (glue r hr p.1 p.2))).symm
  rw [hprod]
  apply Finset.sum_bij
    (fun (n : Fin r → ℕ) (_ : n ∈ piBox r M) => (headPart r hr n, tailPart r hr n))
  · intro n hn
    rw [Finset.mem_product]
    exact ⟨headPart_mem_piBox hr hn, tailPart_mem_piBox hr hn⟩
  · intro n1 h1 n2 h2 heq
    have e1 : headPart r hr n1 = headPart r hr n2 := congrArg Prod.fst heq
    have e2 : tailPart r hr n1 = tailPart r hr n2 := congrArg Prod.snd heq
    rw [← glue_headPart_tailPart r hr n1, ← glue_headPart_tailPart r hr n2, e1, e2]
  · intro p hp
    rw [Finset.mem_product] at hp
    exact ⟨glue r hr p.1 p.2, glue_mem_piBox hr hp.1 hp.2, by rw [headPart_glue, tailPart_glue]⟩
  · intro n hn
    exact (congrArg F (glue_headPart_tailPart r hr n)).symm

/-- The head weight as an explicit triple sum. -/
def headWt (r : ℕ) (v : Fin 3 → ℕ) : ℕ := r * v 0 + (r-1) * v 1 + (r-2) * v 2

lemma headW_eq (r : ℕ) (hr : 3 ≤ r) (v : Fin 3 → ℕ) : headW r hr v = headWt r v := by
  rw [headW, Fin.sum_univ_three, headWt]
  simp only [headIdx, wval, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.sub_zero]
  ring

/-- The map whose injectivity drives the counting argument for the head. -/
def headΦ (r : ℕ) (hr : 3 ≤ r) : (Fin 3 → ℕ) → ℕ × ℕ × ℕ :=
  fun v => (headW r hr v, v 0, v 2)

lemma headΦ_injective (r : ℕ) (hr : 3 ≤ r) : Function.Injective (headΦ r hr) := by
  intro a b hab
  simp only [headΦ, Prod.mk.injEq] at hab
  obtain ⟨e1, e2, e3⟩ := hab
  have h3 : headWt r a = headWt r b := by
    rw [← headW_eq r hr a, ← headW_eq r hr b, e1]
  rw [headWt, e2, e3] at h3
  have h4 : (r-1) * (a 1) = (r-1) * (b 1) := Nat.add_left_cancel (Nat.add_right_cancel h3)
  have h1 : a 1 = b 1 := Nat.mul_left_cancel (by omega : 0 < r - 1) h4
  funext i
  fin_cases i
  · exact e2
  · exact h1
  · exact e3

lemma sum_range_geom_le_two (x : ℝ) (hx0 : 0 ≤ x) (hx : 2 * x ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i ≤ 2 := by
  have h : ∀ m, ∑ i ∈ Finset.range m, x ^ i ≤ 2 - 2 * x ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih, pow_nonneg hx0 m]
  have h2 := h n
  have h3 : 0 ≤ 2 * x ^ n := by positivity
  linarith

lemma half_pow_le_half (k : ℕ) (hk : 1 ≤ k) : (1/2:ℝ)^k ≤ 1/2 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [hm, pow_succ]
  have h1 : (1/2:ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0:ℝ) ≤ (1/2)^m := by positivity
  nlinarith

lemma sum_half_pow_le_two (k S : ℕ) (hk : 1 ≤ k) :
    ∑ w ∈ Finset.range (S+1), (1/2:ℝ)^(k*(S-w)) ≤ 2 := by
  have hx0 : 0 ≤ (1/2:ℝ)^k := by positivity
  have hx : 2 * (1/2:ℝ)^k ≤ 1 := by
    have := half_pow_le_half k hk
    linarith
  have hrew : ∑ w ∈ Finset.range (S+1), (1/2:ℝ)^(k*(S-w))
      = ∑ d ∈ Finset.range (S+1), ((1/2:ℝ)^k)^d := by
    rw [← Finset.sum_range_reflect (fun d => ((1/2:ℝ)^k)^d) (S+1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [pow_mul, show S+1-1-j = S - j from by omega]
  rw [hrew]
  exact sum_range_geom_le_two ((1/2:ℝ)^k) hx0 hx (S+1)

set_option maxHeartbeats 4000000 in
lemma head_bound (N r M S : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) :
    (∑ v ∈ piBox 3 M, (if headW r hr v ≤ S then (1/2:ℝ)^((N-2)*(S - headW r hr v)) else 0))
      ≤ 2 * ((M:ℝ)+1)^2 := by
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (headΦ r hr) ↑((piBox 3 M).filter (fun v => headW r hr v ≤ S)) :=
    fun a _ b _ h => headΦ_injective r hr h
  have himg : Finset.image (headΦ r hr) ((piBox 3 M).filter (fun v => headW r hr v ≤ S))
      ⊆ (Finset.range (S+1)) ×ˢ ((Finset.range (M+1)) ×ˢ (Finset.range (M+1))) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    rw [Finset.mem_filter] at hv
    obtain ⟨hvbox, hvS⟩ := hv
    rw [mem_piBox_iff] at hvbox
    change (headW r hr v, v 0, v 2) ∈ Finset.range (S + 1) ×ˢ (Finset.range (M + 1) ×ˢ Finset.range (M + 1))
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hvS, Nat.lt_succ_of_le (hvbox 0), Nat.lt_succ_of_le (hvbox 2)⟩
  calc ∑ v ∈ (piBox 3 M).filter (fun v => headW r hr v ≤ S),
          (1/2:ℝ)^((N-2)*(S - headW r hr v))
      = ∑ q ∈ Finset.image (headΦ r hr) ((piBox 3 M).filter (fun v => headW r hr v ≤ S)),
          (1/2:ℝ)^((N-2)*(S - q.1)) := (Finset.sum_image (f := fun q => (1/2:ℝ)^((N-2)*(S - q.1))) hinj).symm
    _ ≤ ∑ q ∈ (Finset.range (S+1)) ×ˢ ((Finset.range (M+1)) ×ˢ (Finset.range (M+1))),
          (1/2:ℝ)^((N-2)*(S - q.1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun q _ _ => by positivity)
    _ = ((M:ℝ)+1)^2 * ∑ w ∈ Finset.range (S+1), (1/2:ℝ)^((N-2)*(S - w)) := by
        rw [Finset.sum_product (Finset.range (S+1)) ((Finset.range (M+1)) ×ˢ (Finset.range (M+1)))
              (fun p : ℕ × (ℕ × ℕ) => (1/2:ℝ)^((N-2)*(S - p.1)))]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        have hb : ∀ y : ℕ × ℕ,
            (1/2:ℝ)^((N-2)*(S - (x, y).1)) = (1/2:ℝ)^((N-2)*(S - x)) := fun y => rfl
        rw [Finset.sum_congr rfl (fun y _ => hb y)]
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((M:ℝ)+1)^2 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_half_pow_le_two (N-2) S (by have : 3 ≤ N := le_trans hr hrN; omega)
    _ = 2 * ((M:ℝ)+1)^2 := by ring

lemma tail_bound (r : ℕ) (hr : 3 ≤ r) (M : ℕ) :
    (∑ u ∈ piBox (r-3) M, (1/2:ℝ)^(tailD r hr u)) ≤ (2:ℝ)^(r-3) := by
  have hfac : ∀ u : Fin (r-3) → ℕ, (1/2:ℝ)^(tailD r hr u)
      = ∏ j : Fin (r-3), ((1/2:ℝ)^(dval r (tailIdx r hr j)))^(u j) := by
    intro u
    rw [tailD, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, mul_comm]
  calc ∑ u ∈ piBox (r-3) M, (1/2:ℝ)^(tailD r hr u)
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin (r-3) => Finset.range (M+1)),
          ∏ j : Fin (r-3), ((1/2:ℝ)^(dval r (tailIdx r hr j)))^(u j) := by
        rw [piBox]; apply Finset.sum_congr rfl; intro u _; exact hfac u
    _ = ∏ j : Fin (r-3),
          ∑ t ∈ Finset.range (M+1), ((1/2:ℝ)^(dval r (tailIdx r hr j)))^t :=
        (Finset.prod_univ_sum (fun _ : Fin (r-3) => Finset.range (M+1))
          (fun j t => ((1/2:ℝ)^(dval r (tailIdx r hr j)))^t)).symm
    _ ≤ ∏ _j : Fin (r-3), (2:ℝ) := by
        apply Finset.prod_le_prod₀
        · intro j _; positivity
        · intro j _
          have h1 : 1 ≤ dval r (tailIdx r hr j) := dval_tailIdx_le r hr j
          have hx0 : 0 ≤ (1/2:ℝ)^(dval r (tailIdx r hr j)) := by positivity
          have hx : 2 * (1/2:ℝ)^(dval r (tailIdx r hr j)) ≤ 1 := by
            have := half_pow_le_half (dval r (tailIdx r hr j)) h1
            linarith
          exact sum_range_geom_le_two _ hx0 hx (M+1)
    _ = (2:ℝ)^(r-3) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Part 3: `sum_bound` and the final assembly -/

theorem sum_bound (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n)) ≤ C * 2 ^ ((N-2)*M) * (M+1)^2 := by
  refine ⟨(2:ℝ)^r, by positivity, ?_⟩
  intro M
  have hT : (∑ n ∈ Nset N r M,
        ((1/2:ℝ)^((N-2)*(M - sval r n)) * (1/2:ℝ)^(Pval r n)))
      ≤ 2 * (2:ℝ)^(r-3) * ((M:ℝ)+1)^2 := by
    rw [Nset, Finset.sum_filter]
    rw [sum_piBox_glue r M hr (fun n => if ∑ i, n i * wval r i ≤ M
        then (1/2:ℝ)^((N-2)*(M - sval r n)) * (1/2:ℝ)^(Pval r n) else 0)]
    have hrw : ∀ (v : Fin 3 → ℕ) (u : Fin (r-3) → ℕ),
        (if ∑ i, (glue r hr v u) i * wval r i ≤ M
          then (1/2:ℝ)^((N-2)*(M - sval r (glue r hr v u)))
            * (1/2:ℝ)^(Pval r (glue r hr v u)) else 0)
        = (if headW r hr v + tailW r hr u ≤ M
          then (1/2:ℝ)^((N-2)*(M - headW r hr v - tailW r hr u))
            * (1/2:ℝ)^(tailD r hr u) else 0) := by
      intro v u
      have h1 : (∑ i, (glue r hr v u) i * wval r i) = headW r hr v + tailW r hr u :=
        sval_glue r hr v u
      have h2 : sval r (glue r hr v u) = headW r hr v + tailW r hr u := sval_glue r hr v u
      have h3 : Pval r (glue r hr v u) = tailD r hr u := Pval_glue r hr v u
      rw [h1, h2, h3, Nat.sub_sub]
    simp only [hrw]
    rw [Finset.sum_comm]
    calc ∑ u ∈ piBox (r-3) M, ∑ v ∈ piBox 3 M,
            (if headW r hr v + tailW r hr u ≤ M
              then (1/2:ℝ)^((N-2)*(M - headW r hr v - tailW r hr u))
                * (1/2:ℝ)^(tailD r hr u) else 0)
        ≤ ∑ u ∈ piBox (r-3) M,
            (1/2:ℝ)^(tailD r hr u) * (2 * ((M:ℝ)+1)^2) := by
          apply Finset.sum_le_sum
          intro u _
          calc ∑ v ∈ piBox 3 M,
                  (if headW r hr v + tailW r hr u ≤ M
                    then (1/2:ℝ)^((N-2)*(M - headW r hr v - tailW r hr u))
                      * (1/2:ℝ)^(tailD r hr u) else 0)
              ≤ ∑ v ∈ piBox 3 M, (1/2:ℝ)^(tailD r hr u)
                  * (if headW r hr v ≤ M - tailW r hr u
                    then (1/2:ℝ)^((N-2)*((M - tailW r hr u) - headW r hr v)) else 0) := by
                apply Finset.sum_le_sum
                intro v _
                by_cases hc : headW r hr v + tailW r hr u ≤ M
                · rw [if_pos hc, if_pos (Nat.le_sub_of_add_le hc)]
                  have hidx : M - headW r hr v - tailW r hr u
                      = (M - tailW r hr u) - headW r hr v := by omega
                  rw [hidx]
                  exact le_of_eq (by ring)
                · rw [if_neg hc]; positivity
            _ = (1/2:ℝ)^(tailD r hr u)
                  * ∑ v ∈ piBox 3 M, (if headW r hr v ≤ M - tailW r hr u
                    then (1/2:ℝ)^((N-2)*((M - tailW r hr u) - headW r hr v)) else 0) := by
                rw [Finset.mul_sum]
            _ ≤ (1/2:ℝ)^(tailD r hr u) * (2 * ((M:ℝ)+1)^2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact head_bound N r M (M - tailW r hr u) hr hrN
      _ = (2 * ((M:ℝ)+1)^2) * ∑ u ∈ piBox (r-3) M, (1/2:ℝ)^(tailD r hr u) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (2 * ((M:ℝ)+1)^2) * (2:ℝ)^(r-3) := by
          apply mul_le_mul_of_nonneg_left (tail_bound r hr M) (by positivity)
      _ = 2 * (2:ℝ)^(r-3) * ((M:ℝ)+1)^2 := by ring
  calc (∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n))
      = (2:ℝ)^((N-2)*M) * ∑ n ∈ Nset N r M,
          ((1/2:ℝ)^((N-2)*(M - sval r n)) * (1/2:ℝ)^(Pval r n)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Nset, Finset.mem_filter] at hn
        rw [pow_bigE_eq N r M hr hrN n hn.2]
        ring
    _ ≤ (2:ℝ)^((N-2)*M) * (2 * (2:ℝ)^(r-3) * ((M:ℝ)+1)^2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2:ℝ)^r * 2 ^ ((N-2)*M) * (M+1)^2 := by
        have h1 : 2 * (2:ℝ)^(r-3) ≤ (2:ℝ)^r := by
          have h2 : (2:ℝ)^(r-3) * (2:ℝ)^3 = (2:ℝ)^r := by
            rw [← pow_add, show r - 3 + 3 = r from by omega]
          rw [← h2]
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (r-3)]
        have hX : 0 ≤ (2:ℝ)^((N-2)*M) := by positivity
        have hY : 0 ≤ ((M:ℝ)+1)^2 := by positivity
        calc (2:ℝ)^((N-2)*M) * (2 * (2:ℝ)^(r-3) * ((M:ℝ)+1)^2)
            = (2 * (2:ℝ)^(r-3)) * (2:ℝ)^((N-2)*M) * ((M:ℝ)+1)^2 := by ring
          _ ≤ (2:ℝ)^r * 2 ^ ((N-2)*M) * (M+1)^2 := by
              apply mul_le_mul_of_nonneg_right _ hY
              exact mul_le_mul_of_nonneg_right h1 hX

theorem dyadic_sum_ge3 (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 ≤ L →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then N - 2 else N + r - 1 - 2 * j.1))
        else 0))
      ≤ C * 2 ^ ((N - 2) * L) * (1 + L) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := sum_bound N r hr hrN
  obtain ⟨C2, hC2pos, hC2⟩ := L_arith N (by omega)
  refine ⟨C1 * C2, by positivity, ?_⟩
  intro L hL
  have hif : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then N - 2 else N + r - 1 - 2 * j.1))
        else 0)) = ∑ k ∈ Kset r ⌈L⌉₊, (2:ℝ)^(bigE N r k) := by
    rw [Kset, piBox, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [bigE, cval]
  rw [hif, reindex N r hr hrN ⌈L⌉₊]
  calc (∑ n ∈ Nset N r ⌈L⌉₊, (2:ℝ)^(bigE' N r n))
      ≤ C1 * 2 ^ ((N-2)*⌈L⌉₊) * (⌈L⌉₊+1)^2 := hC1 ⌈L⌉₊
    _ = C1 * (2 ^ ((N-2)*⌈L⌉₊) * (⌈L⌉₊+1)^2) := by ring
    _ ≤ C1 * (C2 * 2 ^ ((N-2)*L) * (1+L)^2) :=
        mul_le_mul_of_nonneg_left (hC2 L hL) (le_of_lt hC1pos)
    _ = C1 * C2 * 2 ^ ((N-2)*L) * (1+L)^2 := by ring

end Work.HP.Sig2
