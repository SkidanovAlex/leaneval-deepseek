import Mathlib
import Submission.Work.SynFFT.axisLeafDefs

/-!
# `Work.SynFFT.leafFinal`: the pure facts closing the leaf step of the blockwise transpose

This file proves the five conjuncts requested from the `SynFFT` area for the leaf (blockwise
transpose) step `HasAxisTranspose`/`axisLeaf`:

1. the invariant of the leaf loop (the row values `lfRV` of the chunks of `W = blk.reverse`, in
   accumulation order, i.e. reversed) is the specification `stateVal ((rowsOf t B blk).map
   exploded)` of the word (the `t` rows of `blk`, each exploded into singleton columns);
2. `vsz (ofList l) = Σ vsz + #l + 1` (the encoding bookkeeping of a list value);
3. `vsz (lfWrap x) = vsz x + 2` (wrapping an element in a singleton column);
4. `ofList (x :: L) = Val.cons x (ofList L)` (definitional);
5. `ofList [x] = lfWrap x` (definitional).

The content is (1): a chunk of the reversed flat array is the reverse of the chunk counted from
the other end (`chunk_reverse`), whence the rows of `blk.reverse` are the rows of `blk` in reverse
order with each row reversed (`rows_reverse`); combined with `lfRV r.reverse = ofList (r.map lfWrap)`
and `grpVal (exploded r) = ofList (r.map lfWrap)` this identifies both sides with
`ofList ((rowsOf t B blk).map (fun r => ofList (r.map lfWrap)))`.
-/

namespace Work.SynFFT

/-! ## Pure list layer -/

/-- The reversal of `List.range n` is the decreasing enumeration of `{0,…,n-1}`. -/
private theorem range_reverse (n : ℕ) :
    (List.range n).reverse = (List.range n).map (fun j => n - 1 - j) := by
  rw [List.range_eq_range', List.reverse_range', List.range_eq_range']
  simp

/-- A chunk of length `B` of the reversed list `L` (where `L` has length `t*B`) is the reverse of
the chunk of length `B` of `L` counted from the other end. -/
private theorem chunk_reverse (L : List HvdH.Val) (t B i : ℕ) (h : L.length = t * B) (hi : i < t) :
    (L.reverse.drop (i * B)).take B = ((L.drop ((t - 1 - i) * B)).take B).reverse := by
  have hmB : (t - 1 - i) * B + B ≤ L.length := by
    have h1 : (t - 1 - i) * B + B = (t - i) * B := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    rw [h1, h]
    exact Nat.mul_le_mul_right B (by omega)
  rw [List.reverse_take, List.length_drop, List.reverse_drop, List.drop_take]
  have ha : L.length - (t - 1 - i) * B - (L.length - (t - 1 - i) * B - B) = B := by omega
  have hb : L.length - (t - 1 - i) * B - B = i * B := by
    have e1 : t - (t - 1 - i) = i + 1 := by omega
    have e2 : L.length - (t - 1 - i) * B = (i + 1) * B := by
      rw [h, ← Nat.sub_mul, e1]
    rw [e2, Nat.succ_mul, Nat.add_sub_cancel]
  rw [ha, hb]

/-- The rows of the reversed flat array `L` (of length `t*B`), listed in increasing row order, are
the rows of `L` with each row reversed. -/
private theorem rows_reverse (L : List HvdH.Val) (t B : ℕ) (h : L.length = t * B) :
    (rowsOf t B L.reverse).reverse = (rowsOf t B L).map List.reverse := by
  show ((List.range t).map (fun j => (L.reverse.drop (j * B)).take B)).reverse
      = ((List.range t).map (fun j => (L.drop (j * B)).take B)).map List.reverse
  rw [← List.map_reverse, range_reverse]
  simp only [List.map_map]
  refine List.map_congr_left (fun j hj => ?_)
  have hj' : j < t := List.mem_range.mp hj
  have hc := chunk_reverse L t B (t - 1 - j) h (by omega)
  have hidx : t - 1 - (t - 1 - j) = j := by omega
  rw [hidx] at hc
  show (L.reverse.drop ((t - 1 - j) * B)).take B = ((L.drop (j * B)).take B).reverse
  exact hc

/-! ## The `Val` layer -/

/-- `lfRV` of a reversed row is the row wrapped elementwise. -/
private theorem lfRV_reverse (r : List HvdH.Val) :
    lfRV r.reverse = HvdH.ofList (r.map lfWrap) := by
  simp [lfRV]

/-- The group value of an exploded row is the row wrapped elementwise. -/
private theorem grpVal_exploded (r : List HvdH.Val) :
    grpVal (exploded r) = HvdH.ofList (r.map lfWrap) := by
  simp only [grpVal, exploded]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  rfl

/-- Size of a `cons` cell. -/
private theorem ofList_cons_vsz (x : HvdH.Val) (l : List HvdH.Val) :
    HvdH.vsz (HvdH.Val.cons x (HvdH.ofList l)) =
      HvdH.vsz x + HvdH.vsz (HvdH.ofList l) + 1 := by
  simp [HvdH.vsz, HvdH.Val.enc]

/-- Size of a concatenated list value: `vsz (ofList l) = Σ vsz + #l + 1`. -/
private theorem ofList_vsz (l : List HvdH.Val) :
    HvdH.vsz (HvdH.ofList l) = (l.map HvdH.vsz).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [show HvdH.ofList (x :: t) = HvdH.Val.cons x (HvdH.ofList t) from rfl,
      ofList_cons_vsz, ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    ring

/-- Size of a wrapped element. -/
private theorem vsz_lfWrap (x : HvdH.Val) : HvdH.vsz (lfWrap x) = HvdH.vsz x + 2 := by
  simp [lfWrap, HvdH.vsz, HvdH.Val.enc]

theorem leafFinal :
    (∀ (t B : ℕ) (blk : List HvdH.Val), blk.length = t * B → 1 ≤ t → 1 ≤ B →
      HvdH.ofList ((List.map Work.SynFFT.lfRV (rowsOf t B blk.reverse)).reverse) =
        Work.SynFFT.stateVal ((rowsOf t B blk).map Work.SynFFT.exploded)) ∧
    (∀ (l : List HvdH.Val), HvdH.vsz (HvdH.ofList l) = (l.map HvdH.vsz).sum + l.length + 1) ∧
    (∀ (x : HvdH.Val), HvdH.vsz (Work.SynFFT.lfWrap x) = HvdH.vsz x + 2) ∧
    (∀ (x : HvdH.Val) (L : List HvdH.Val),
      HvdH.ofList (x :: L) = HvdH.Val.cons x (HvdH.ofList L)) ∧
    (∀ (x : HvdH.Val), HvdH.ofList [x] = Work.SynFFT.lfWrap x) := by
  refine ⟨?_, ofList_vsz, vsz_lfWrap, fun x L => rfl, fun x => rfl⟩
  intro t B blk hlen ht hB
  have hrows := rows_reverse blk t B hlen
  calc HvdH.ofList ((List.map lfRV (rowsOf t B blk.reverse)).reverse)
      = HvdH.ofList ((rowsOf t B blk.reverse).reverse.map lfRV) := by rw [← List.map_reverse]
    _ = HvdH.ofList (((rowsOf t B blk).map List.reverse).map lfRV) := by rw [hrows]
    _ = HvdH.ofList ((rowsOf t B blk).map (fun r => HvdH.ofList (r.map lfWrap))) := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro r _
        exact lfRV_reverse r
    _ = stateVal ((rowsOf t B blk).map exploded) := by
        simp only [stateVal, List.map_map]
        congr 1
        apply List.map_congr_left
        intro r _
        exact (grpVal_exploded r).symm

end Work.SynFFT
