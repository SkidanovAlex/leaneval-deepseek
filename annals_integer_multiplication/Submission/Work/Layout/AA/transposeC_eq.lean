import Mathlib
import Submission.Work.Layout.AA.PureDefs
import Submission.Work.Layout.AA.flatten_map_range_length
import Submission.Work.Layout.AA.flatten_map_range_map
import Submission.Work.Layout.AA.rowsOf_facts

/-!
# `transposeC` computes the columns of a flat array

`Work.Layout.AA.transposeC C L` is the recursive "split the columns in half, recurse, concatenate"
transposition of `PureDefs`; this file proves that for a flat `m × C` array `L` (i.e. a list of
length `m * C` read row-major) it returns the `C` columns of `L`, each of length `m`
(`Work.Layout.AA.colsOf m C L`).

The proof is an induction on the fuel `C` of the recursion; the mathematical content is the split
identity `colsOf_split_canonical`: the columns of the left block of columns `0..C1-1` followed by the
columns of the right block `C1..C1+C2-1` are the columns of the whole array.  That identity in turn
rests on `colsOf_block_row`: reading a flattened block of rows through its own row length returns the
entries of the underlying array at the strided indices.
-/

set_option autoImplicit false

namespace Work.Layout.AA

open HvdH

/-- Defining unfolding of `transposeCAux` at fuel `F+1` and a column count `k+2`, with the
`let`-bound halving made explicit.  (Pure `rfl`: the definition is by pattern matching.) -/
lemma transposeCAux_step (F k : ℕ) (L : List Val) :
    transposeCAux (F + 1) (k + 2) L =
      transposeCAux F ((k + 2) / 2)
          (((List.range (L.length / (k + 2))).map fun j =>
            ((List.range ((k + 2) / 2)).map fun i => L.getD (j * (k + 2) + i) default)).flatten)
        ++ transposeCAux F ((k + 2) - (k + 2) / 2)
          (((List.range (L.length / (k + 2))).map fun j =>
            ((List.range ((k + 2) - (k + 2) / 2)).map fun i =>
              L.getD (j * (k + 2) + (k + 2) / 2 + i) default)).flatten) := rfl

/-- One column: `colsOf m 1 L = [L]` when `L` has exactly `m` entries. -/
lemma colsOf_one (m : ℕ) (L : List Val) (h : L.length = m) : colsOf m 1 L = [L] := by
  subst h
  show (List.range 1).map (fun i => (List.range L.length).map fun j => L.getD (j * 1 + i) default)
      = [L]
  rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil]
  rw [show (List.range L.length).map (fun j => L.getD (j * 1 + 0) default) = L from by
        simpa using range_map_getD L default]

/-- Reading the flattened block of `m` rows of `C1` consecutive columns (starting at column `off`
of a stride-`C` flat array) through its own row length `C1` recovers the strided entries. -/
lemma colsOf_block_row (m C C1 off : ℕ) (L : List Val) :
    colsOf m C1 (((List.range m).map fun j => ((List.range C1).map fun i =>
        L.getD (j * C + off + i) default)).flatten)
      = (List.range C1).map (fun i => (List.range m).map (fun j =>
          L.getD (j * C + off + i) default)) := by
  rcases Nat.eq_zero_or_pos C1 with h0 | hpos
  · subst h0
    simp [colsOf]
  unfold colsOf
  rw [flatten_map_range_map m C1 (fun j i => L.getD (j * C + off + i) default)]
  apply List.map_congr_left
  intro i hi
  apply List.map_congr_left
  intro j hj
  have hj' : j < m := List.mem_range.mp hj
  have hi' : i < C1 := List.mem_range.mp hi
  have hlt : j * C1 + i < m * C1 := by
    calc j * C1 + i < j * C1 + C1 := Nat.add_lt_add_left hi' _
      _ = (j + 1) * C1 := by ring
      _ ≤ m * C1 := Nat.mul_le_mul_right C1 (Nat.succ_le_of_lt hj')
  have hdiv : (j * C1 + i) / C1 = j := by
    rw [Nat.mul_comm j C1, Nat.mul_add_div hpos, Nat.div_eq_of_lt hi', Nat.add_zero]
  have hmod : (j * C1 + i) % C1 = i := by
    rw [Nat.add_comm (j * C1) i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some, hdiv, hmod]

/-- `colsOf_block_row` at offset `0`, in the shape in which it occurs in `transposeCAux`. -/
lemma colsOf_block_row_zero (m C C1 : ℕ) (L : List Val) :
    colsOf m C1 (((List.range m).map fun j => ((List.range C1).map fun i =>
        L.getD (j * C + i) default)).flatten)
      = (List.range C1).map (fun i => (List.range m).map (fun j =>
          L.getD (j * C + i) default)) := by
  simpa only [Nat.add_zero] using colsOf_block_row m C C1 0 L

/-- The split identity of the recursive transposition, in the canonical form with stride `C1 + C2`:
the columns of the left block of columns followed by those of the right block are the columns of
the whole array. -/
lemma colsOf_split_canonical (m C1 C2 : ℕ) (L : List Val) :
    colsOf m C1 (((List.range m).map fun j => ((List.range C1).map fun i =>
        L.getD (j * (C1 + C2) + i) default)).flatten)
      ++ colsOf m C2 (((List.range m).map fun j => ((List.range C2).map fun i =>
        L.getD (j * (C1 + C2) + C1 + i) default)).flatten)
      = colsOf m (C1 + C2) L := by
  rw [colsOf_block_row_zero m (C1 + C2) C1 L, colsOf_block_row m (C1 + C2) C2 C1 L]
  unfold colsOf
  rw [List.range_add, List.map_append, List.map_map]
  simp only [Function.comp_def, Nat.add_assoc]

/-- `colsOf_split_canonical` with the column count and the stride identified by `hC`. -/
lemma colsOf_split (m C1 C2 C : ℕ) (L : List Val) (hC : C1 + C2 = C) :
    colsOf m C1 (((List.range m).map fun j => ((List.range C1).map fun i =>
        L.getD (j * C + i) default)).flatten)
      ++ colsOf m C2 (((List.range m).map fun j => ((List.range C2).map fun i =>
        L.getD (j * C + C1 + i) default)).flatten)
      = colsOf m C L := by
  simpa [hC] using colsOf_split_canonical m C1 C2 L

/-- `transposeCAux fuel C L` is the columns of the flat array `L`, whenever `L` is a flat `m × C`
array and the fuel `C` is enough for the recursive halving of `C` columns. -/
lemma transposeCAux_eq_colsOf : ∀ (fuel C : ℕ) (L : List Val) (m : ℕ),
    1 ≤ C → C ≤ fuel → L.length = m * C → transposeCAux fuel C L = colsOf m C L := by
  intro fuel
  induction fuel with
  | zero => intro C L m hC hf h; omega
  | succ F ih =>
    intro C L m hC hf h
    match C with
    | 0 => omega
    | 1 =>
      exact ((show transposeCAux (F + 1) 1 L = [L] from rfl).trans
        (colsOf_one m L (by omega)).symm)
    | k + 2 =>
      rw [transposeCAux_step]
      have hm' : L.length / (k + 2) = m := by
        rw [h, Nat.mul_comm m (k + 2), Nat.mul_div_right m (by omega)]
      rw [hm']
      have hC1lt : (k + 2) / 2 < k + 2 := Nat.div_lt_self (by omega) (by norm_num)
      have hC2lt : (k + 2) - (k + 2) / 2 < k + 2 := by omega
      have hC1le : (k + 2) / 2 ≤ F := by omega
      have hC2le : (k + 2) - (k + 2) / 2 ≤ F := by omega
      have hC1pos : 1 ≤ (k + 2) / 2 := by omega
      have hC2pos : 1 ≤ (k + 2) - (k + 2) / 2 := by omega
      have hAlen : (((List.range m).map fun j =>
            ((List.range ((k + 2) / 2)).map fun i => L.getD (j * (k + 2) + i) default)).flatten).length
          = m * ((k + 2) / 2) := by
        apply flatten_map_range_length
        intro j hj
        simp
      have hBlen : (((List.range m).map fun j =>
            ((List.range ((k + 2) - (k + 2) / 2)).map fun i =>
              L.getD (j * (k + 2) + (k + 2) / 2 + i) default)).flatten).length
          = m * ((k + 2) - (k + 2) / 2) := by
        apply flatten_map_range_length
        intro j hj
        simp
      rw [ih ((k + 2) / 2) _ m hC1pos hC1le hAlen,
          ih ((k + 2) - (k + 2) / 2) _ m hC2pos hC2le hBlen]
      exact colsOf_split m ((k + 2) / 2) ((k + 2) - (k + 2) / 2) (k + 2) L
        (Nat.add_sub_cancel' (Nat.div_le_self (k + 2) 2))

theorem transposeC_eq (m C : ℕ) (L : List HvdH.Val) (h : L.length = m * C) :
    Work.Layout.AA.transposeC C L = Work.Layout.AA.colsOf m C L := by
  match C with
  | 0 => rfl
  | C + 1 =>
    exact transposeCAux_eq_colsOf (C + 1) (C + 1) L m (by omega) (le_refl (C + 1)) h

end Work.Layout.AA
