import Mathlib
import Submission.Work.SynFFT.axisLeafDefs

/-!
# `Work.SynFFT.leafCost`: the cost of the leaf (blockwise transpose) loop

`Work.SynFFT.lfTC` is the recursive cost upper bound of the loop `lfLoop` (defined in
`Work.SynFFT.axisLeafDefs`), as a function of the remaining list of values, the counter value `c`
and a bound `S` on the accumulated row size; `Work.SynFFT.lfCF` is a closed form suggested by the
same recursion, `Work.SynFFT.lfCloses B c n = (n + B - c) / B` counting the row closings among the
next `n` elements when the counter starts at `c`.

The two claims proved here are the two halves of the cost contract of `lfLoop`:

* `lfTC B l c S ≤ lfCF B S c l` for every admissible counter `1 ≤ c ≤ B` (the closed form really is
  an upper bound of the recursion);
* `lfCF B 0 B blk.reverse ≤ 1000 * (vsz (ofList blk) + 1) +
  1000 * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1)` for `blk.length = t * B`, `t, B ≥ 1`
  (the closed form, at the entry state of a block of `t*B` values, is `O(vsz + t·log B)`).

Pure arithmetic: the decomposition `lfCF = lfA + 20*S + (lfCloses+1)*lfM` turns both claims into
polynomial inequalities which `nlinarith` discharges once the relevant monotonicity/identity of
`lfCloses` is supplied.
-/

set_option autoImplicit false
namespace Work.SynFFT

open HvdH

/-! ## 1. Decomposition of the closed form -/

/-- The per-row-closing cost: `20 * (B + 8) + 16 * (isz B + 1) + 50` (one factor of
`lfCloses + 1`). -/
def lfM (B : ℕ) : ℕ := 20 * (B + 8) + 16 * (isz (B : ℤ) + 1) + 50

/-- The part of `lfCF` depending only on the list (not on the counter or the row-size bound). -/
def lfA (B : ℕ) (l : List Val) : ℕ :=
  80 * (l.map (fun x => vsz x + 1)).sum + 40 * (l.length * (isz (B : ℤ) + 1)) +
    60 * l.length + 20 * (l.map (fun x => vsz x + 2)).sum + 3 * (l.length + 1) + 100

theorem lfCF_eq (B S c : ℕ) (l : List Val) :
    lfCF B S c l = lfA B l + 20 * S + (lfCloses B c l.length + 1) * lfM B := by
  simp only [lfCF, lfA, lfM]
  ring

/-- One element more in the list adds a fixed amount, independent of the counter. -/
theorem lfA_cons (B : ℕ) (x : Val) (l : List Val) :
    lfA B (x :: l) =
      lfA B l + (80 * (vsz x + 1) + 40 * (isz (B : ℤ) + 1) + 60 + 20 * (vsz x + 2) + 3) := by
  simp only [lfA, List.map_cons, List.sum_cons, List.length_cons]
  ring

/-! ## 2. Facts about `lfCloses` -/

theorem lfCloses_B_eq (B n : ℕ) : lfCloses B B n = n / B := by
  simp only [lfCloses, Nat.add_sub_cancel]

/-- `n + 1` elements with counter `c ≥ 1` close as many rows as `n` elements with counter `c - 1`:
the row closing count shifts by one when the counter decrements. -/
theorem lfCloses_shift (B c n : ℕ) (hc : 1 ≤ c) :
    lfCloses B (c - 1) n = lfCloses B c (n + 1) := by
  have h : n + B - (c - 1) = n + 1 + B - c := by omega
  simp only [lfCloses, h]

/-- Starting the counter at `B` and reading one more element closes exactly one more row. -/
theorem lfCloses_one_succ (B n : ℕ) (hB : 1 ≤ B) :
    lfCloses B 1 (n + 1) = lfCloses B B n + 1 := by
  rw [lfCloses_B_eq]
  have h1 : n + 1 + B - 1 = n + B := by omega
  simp only [lfCloses]
  rw [h1]
  simpa using Nat.add_mul_div_right n 1 (show 0 < B by omega)

/-! ## 3. Arithmetic bounds on sizes -/

theorem leaf_isz_ge_four (B : ℕ) (hB : 1 ≤ B) : 4 ≤ isz (B : ℤ) + 1 := by
  simp only [isz, Int.natAbs_natCast]
  have h : 0 < B.size := Nat.size_pos.mpr (by omega)
  omega

/-- The cost of one loop iteration, with `c ≤ B` replaced by `B` (the only size that occurs is
`isz c ≤ isz B`). -/
theorem lfIter_le (B S c : ℕ) (x : Val) (hcB : c ≤ B) :
    lfIter B x c S ≤ 80 * (vsz x + 1) + 40 * (isz (B : ℤ) + 1) + 60 +
      (if c = 1 then 20 * (S + (vsz x + 2) + B + 8) + 16 * (isz (B : ℤ) + 1) + 40 else 0) := by
  have h : isz (c : ℤ) ≤ isz (B : ℤ) := by
    simp only [isz, Int.natAbs_natCast]
    exact Nat.add_le_add_right (Nat.size_le_size hcB) 2
  simp only [lfIter]
  split <;> omega

/-! ## 4. The first claim: `lfTC ≤ lfCF` -/

theorem lfTC_le_lfCF : ∀ (l : List Val) (B S c : ℕ), 1 ≤ c → c ≤ B →
    lfTC B l c S ≤ lfCF B S c l := by
  intro l
  induction l with
  | nil =>
    intro B S c hc hcB
    rw [lfCF_eq]
    have h3 : lfTC B [] c S = 3 := rfl
    rw [h3]
    have hA : lfA B [] = 103 := by simp [lfA]
    rw [hA]
    simp only [lfM]
    nlinarith [Nat.zero_le S]
  | cons x l' ih =>
    intro B S c hc hcB
    have hcB1 : 1 ≤ B := le_trans hc hcB
    rw [lfCF_eq, lfA_cons]
    rw [show lfTC B (x :: l') c S =
        lfIter B x c S + lfTC B l' (if c = 1 then B else c - 1)
          (if c = 1 then 0 else S + (vsz x + 2)) from rfl]
    have h1 : 1 ≤ (if c = 1 then B else c - 1) := by
      split
      · exact hcB1
      · rename_i h; omega
    have h2 : (if c = 1 then B else c - 1) ≤ B := by
      split
      · exact le_rfl
      · rename_i h; omega
    have ih' := ih B (if c = 1 then 0 else S + (vsz x + 2)) (if c = 1 then B else c - 1) h1 h2
    rw [lfCF_eq] at ih'
    have hiter := lfIter_le B S c x hcB
    have hsum := add_le_add hiter ih'
    refine le_trans hsum ?_
    by_cases hc1 : c = 1
    · subst c
      simp only [ite_true, Nat.sub_self, List.length_cons] at hsum ⊢
      rw [lfCloses_one_succ B l'.length hcB1]
      have hI : 4 ≤ isz (B : ℤ) + 1 := leaf_isz_ge_four B hcB1
      simp only [lfM]
      nlinarith [hI]
    · have hif1 : (if c = 1 then B else c - 1) = c - 1 := by simp [hc1]
      have hif0 : (if c = 1 then 0 else S + (vsz x + 2)) = S + (vsz x + 2) := by simp [hc1]
      rw [hif1, hif0] at hsum
      simp only [hc1, ite_false, List.length_cons] at hsum ⊢
      rw [lfCloses_shift B c l'.length hc]
      simp only [lfM]
      nlinarith

/-! ## 5. The second claim: `lfCF` at the entry state, in terms of `vsz (ofList blk)` -/

theorem leaf_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc]

theorem leaf_vsz_ofList_eq : ∀ (l : List Val), vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  intro l
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, leaf_vsz_cons, ih]
    simp [List.length_cons]
    ring

theorem leaf_sum_map_vsz_add (l : List Val) (k : ℕ) :
    (l.map (fun x => vsz x + k)).sum = (l.map vsz).sum + k * l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp [ih, List.length_cons]
    ring

theorem lfA_reverse (B : ℕ) (l : List Val) : lfA B l.reverse = lfA B l := by
  simp [lfA, List.length_reverse, List.map_reverse]

/-- Pure arithmetic core of the second claim: the closed form at the entry state, with
`S = Σ vsz` and `n = t*B` elements, is `O(S + n·log B)`. -/
theorem leaf_arith (S t B : ℕ) (ht : 1 ≤ t) (hB : 1 ≤ B) :
    80 * (S + 1 * (t * B)) + 40 * (t * B * (isz (B : ℤ) + 1)) + 60 * (t * B) +
      20 * (S + 2 * (t * B)) + 3 * (t * B + 1) + 100 + 20 * 0 +
      (t + 1) * (20 * (B + 8) + 16 * (isz (B : ℤ) + 1) + 50)
    ≤ 1000 * (S + t * B + 1 + 1) + 1000 * ((t * B + t + 1) * (isz (B : ℤ) + 1) + 1) := by
  have hI : 4 ≤ isz (B : ℤ) + 1 := leaf_isz_ge_four B hB
  have htB : 1 ≤ t * B :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : (t + 1) * (B + 8) ≤ 18 * (t * B) := by nlinarith [ht, hB]
  have h2 : 18 * (t * B) ≤ 48 * (t * B) * (isz (B : ℤ) + 1) := by nlinarith [htB, hI]
  have h20 : 20 * (t + 1) * (B + 8) ≤ 960 * (t * B) * (isz (B : ℤ) + 1) := by linarith
  nlinarith only [h20, ht, hB, hI]

theorem lfCF_reverse_le (t B : ℕ) (blk : List Val) (hlen : blk.length = t * B)
    (ht : 1 ≤ t) (hB : 1 ≤ B) :
    lfCF B 0 B blk.reverse ≤
      1000 * (vsz (ofList blk) + 1) +
        1000 * ((blk.length + t + 1) * (isz (B : ℤ) + 1) + 1) := by
  rw [lfCF_eq, lfA_reverse]
  rw [List.length_reverse]
  rw [lfCloses_B_eq]
  have hdiv : blk.length / B = t := by
    rw [hlen, Nat.mul_div_cancel t (show 0 < B by omega)]
  rw [hdiv]
  simp only [lfM, lfA]
  rw [leaf_vsz_ofList_eq, leaf_sum_map_vsz_add blk 1, leaf_sum_map_vsz_add blk 2, hlen]
  exact leaf_arith ((blk.map vsz).sum) t B ht hB

/-! ## 6. The leaf cost lemma -/

theorem leafCost :
    (∀ (B S c : ℕ) (l : List HvdH.Val), 1 ≤ c → c ≤ B →
      Work.SynFFT.lfTC B l c S ≤ Work.SynFFT.lfCF B S c l) ∧
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → 1 ≤ t → 1 ≤ B →
      Work.SynFFT.lfCF B 0 B blk.reverse ≤
        1000 * (HvdH.vsz (HvdH.ofList blk) + 1) +
          1000 * ((blk.length + t + 1) * (HvdH.isz (B : ℤ) + 1) + 1)) :=
  ⟨fun B S c l => lfTC_le_lfCF l B S c, lfCF_reverse_le⟩

end Work.SynFFT
