import Mathlib
import Submission.Work.PTCert.EntryDefs

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open scoped BigOperators

/-! ## Helpers for unfolding `kEntry` -/

lemma getD_drop' {α : Type*} (l : List α) (d : α) (i n : ℕ) :
    (l.drop i).getD n d = l.getD (i + n) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_map_lt' {α β : Type*} (l : List α) (f : α → β) (d' : β) (e : α) {n : ℕ}
    (h : n < l.length) : (l.map f).getD n d' = f (l.getD n e) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem l _ h, List.getElem_map]

/-- The `ψ`-th Klein block row of `blockRow` is the map over the columns of the four-term sum. -/
lemma blockRow_getD (cm eM repT : NT) (rowTs : List NT) (r piInvTab Sp : ℕ) (ys : List ℕ) (ψ : ℕ)
    (hψ : ψ < 4) :
    (blockRow cm eM repT rowTs r piInvTab Sp ys).getD ψ [] =
      (ys.map (fun yv => (List.range 4).map (fun a =>
        (bif Nat.beq (((yv >>> (11 * a)) &&& 2047) % 2) 0 then (1 : ℤ) else -1) *
          mVal cm eM repT rowTs r piInvTab Sp (((yv >>> (11 * a)) &&& 2047) / 2)))).map
        (fun m4 => (List.range 4).foldr (fun a acc => acc +
          (bif Nat.beq ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) 1 then -(m4.getD a 0) else m4.getD a 0)) 0) := by
  unfold blockRow
  rw [List.getD_eq_getElem _ _ (show ψ < _ by simp [List.length_map, List.length_range]; omega)]
  rw [List.getElem_map]
  rw [List.getElem_range (by simp [List.length_range]; omega)]

/-- Inside the four-term Klein sum the `a`-th column entry may be unfolded. -/
lemma foldr_col_range4 (g : ℕ → ℤ) (ψ : ℕ) :
    (List.range 4).foldr (fun a acc => acc + (bif Nat.beq ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) 1
        then -(((List.range 4).map g).getD a 0) else (((List.range 4).map g).getD a 0))) 0
    = (List.range 4).foldr (fun a acc => acc + (bif Nat.beq ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) 1
        then -(g a) else g a)) 0 := by
  rw [show (List.range 4 : List ℕ) = [0,1,2,3] from by decide]
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ]

/-- The four-term Klein sum, cast to `ℝ`, is the `Finset` sum over `a < 4`. -/
lemma cast_foldr_range4 (g : ℕ → ℤ) (ψ : ℕ) :
    (((List.range 4).foldr (fun a acc => acc + (bif Nat.beq ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) 1
        then -(g a) else g a)) 0 : ℤ) : ℝ)
      = ∑ a ∈ Finset.range 4, (if ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) = 1 then (-1 : ℝ) else 1) *
          ((g a : ℤ) : ℝ) := by
  rw [show (List.range 4 : List ℕ) = [0,1,2,3] from by decide]
  simp only [List.foldr_cons, List.foldr_nil, Finset.sum_range_succ, Finset.sum_range_zero,
    Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs <;> push_cast <;> ring

/-- Combined form: the cast of the four-term Klein sum of a mapped `range 4`. -/
lemma cast_foldr_col (G : ℕ → ℤ) (ψ : ℕ) :
    ((((List.range 4).foldr (fun a acc => acc + (bif Nat.beq ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) 1
        then -(((List.range 4).map G).getD a 0) else (((List.range 4).map G).getD a 0))) 0) : ℤ) : ℝ)
      = ∑ a ∈ Finset.range 4, (if ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) = 1 then (-1 : ℝ) else 1) *
          ((G a : ℤ) : ℝ) := by
  rw [foldr_col_range4 G ψ]
  exact cast_foldr_range4 G ψ

/-- The low-bit sign of a Klein field, cast from `ℤ` to `ℝ`. -/
lemma cast_col (e : ℕ) (v : ℤ) :
    (((bif Nat.beq (e % 2) 0 then (1 : ℤ) else -1) * v : ℤ) : ℝ)
      = (if e % 2 = 0 then (1 : ℝ) else -1) * (v : ℝ) := by
  rw [Int.cast_mul]
  congr 1
  simp only [Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs <;> simp

/-- `kEntry rowTs k ψ i j` (KernelCert) unfolds to the `ψ`-th Klein block entry; with
`ks = ksL.getD k [] = efKs k` and `ys = ysL.getD k [] = efYs k`, `blockRows4 … i` is
`blockRow` applied to `ys.drop i`, whose `ψ`-th component is the four-term sum over the Klein
elements with the sign `(-1)^{popcount (a &&& ψ)}` and the column entry `mVal (f_a / 2)` weighted by
the sign of the low bit of `f_a = efField k j a` (the `(j - i)`-th column of `blockRows4` is the
`j`-th column of `blockRow`, since `i ≤ j`, and `ys.length = ks.length = efKs k.length`). -/
theorem entryKernelSum (rowTs : List NT) (k ψ i j : ℕ) (hψ : ψ < 4) (hij : i ≤ j)
    (hj : j < (efKs k).length) (hys : (efYs k).length = (efKs k).length) :
    ((kEntry rowTs k ψ i j : ℤ) : ℝ) =
      ∑ a ∈ Finset.range 4,
        (if ((a &&& ψ) % 2 + ((a &&& ψ) / 2) % 2) = 1 then (-1 : ℝ) else 1) *
          ((if (efField k j a) % 2 = 0 then (1 : ℝ) else -1) *
            (mVal cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i) (efField k j a / 2) : ℝ)) := by
  have hys' : (ysL.getD k []).length = (efKs k).length := by
    simpa [efYs] using hys
  unfold kEntry
  simp only [blockRows4]
  rw [show xInfo repInfoT piIT piCodes (Sk k) ((ksL.getD k []).getD i 0)
        = (efRow k i, efTabInv k i, efSp k i) from rfl]
  rw [blockRow_getD cmT eM repT rowTs (efRow k i) (efTabInv k i) (efSp k i)
    (List.drop i (ysL.getD k [])) ψ hψ]
  rw [getD_map_lt' _ _ (0 : ℤ) ([] : List ℤ)
    (by simp only [List.length_map, List.length_drop]; omega)]
  rw [getD_map_lt' _ _ ([] : List ℤ) (0 : ℕ) (by simp only [List.length_drop]; omega)]
  rw [getD_drop']
  rw [Nat.add_sub_cancel' hij]
  rw [cast_foldr_col _ ψ]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [efField]
  rw [cast_col]
  rfl

end Work.PTCert
