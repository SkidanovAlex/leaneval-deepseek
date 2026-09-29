import Mathlib
import Submission.Work.SynFFT.axisLeafDefs
import Submission.Work.SynFFT.leafRowsL

/-!
# `Work.SynFFT.leafSize`

Size bound for the leaf step of the blockwise transpose (`axisLeafDefs`): the row list produced by
the leaf loop, `lfRowsL t B blk.reverse blk.reverse`, is at most ten times as large as the input
block `blk.length = t * B` elements.

The proof is a direct computation of both sizes.  With `W = blk.reverse` the row list is
`(rowsOf t B W).map lfRV` reversed (`leafRowsL`), so

`vsz (ofList (lfRowsL t B W W)) = Σ_{rows c} vsz (lfRV c) + t + 1`

and `vsz (lfRV c) = Σ_{y ∈ c} (vsz y + 2) + c.length + 1`.  The rows partition `W`, so the double
sum collapses to `Σ_{y ∈ W} (vsz y + 2) = Σ_{y ∈ W} vsz y + 2 * W.length` and the lengths add up to
`W.length = t * B`.  Hence the left-hand side is `Σ vsz + 3 * W.length + 2 * t + 2` while the
right-hand side is `10 * (Σ vsz + W.length + 2)`, and `t ≤ W.length` finishes the estimate.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-! ## Size arithmetic for value lists -/

/-- The size of a `cons` value. -/
private theorem vsz_cons_eq (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

/-- The size of a `cons`-list of values. -/
private theorem vsz_ofList_eq (l : List Val) : vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons a t ih =>
    rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, vsz_cons_eq, ih,
      List.map_cons, List.sum_cons, List.length_cons]
    ring

/-- Sums of mapped lists agree pointwise. -/
private theorem sum_map_congr' {α : Type} (l : List α) (u v : α → ℕ) (h : ∀ x, u x = v x) :
    (l.map u).sum = (l.map v).sum := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, h a]

/-- Reversing a list does not change the sum of a mapped function. -/
private theorem sum_map_reverse' (l : List Val) (f : Val → ℕ) :
    ((l.reverse).map f).sum = (l.map f).sum := by
  rw [List.map_reverse, List.sum_reverse]

/-- `vsz` of a `cons`-list is invariant under reversal. -/
private theorem vsz_ofList_reverse' (l : List Val) : vsz (ofList l.reverse) = vsz (ofList l) := by
  rw [vsz_ofList_eq, vsz_ofList_eq, List.length_reverse, sum_map_reverse' l vsz]

/-- The size of the `cons`-list of the images of a list. -/
private theorem vsz_map_ofList' {α : Type} (l : List α) (f : α → Val) :
    vsz (ofList (l.map f)) = (l.map (fun x => vsz (f x))).sum + l.length + 1 := by
  have h : ((l.map f).map vsz).sum = (l.map (fun x => vsz (f x))).sum := by
    rw [List.map_map]
    exact sum_map_congr' l (vsz ∘ f) (fun x => vsz (f x)) (fun x => rfl)
  rw [vsz_ofList_eq, List.length_map, h]

/-- The size of the wrapped element. -/
private theorem vsz_lfWrap_eq (x : Val) : vsz (lfWrap x) = vsz x + 2 := by
  rw [show lfWrap x = Val.cons x Val.nil from rfl, vsz_cons_eq]
  simp [vsz, Val.enc]

/-- The size of a row value, in terms of the sizes of its elements. -/
private theorem vsz_lfRV_eq (c : List Val) :
    vsz (lfRV c) = (c.map (fun y => vsz y + 2)).sum + (c.length + 1) := by
  have h : ((c.reverse.map lfWrap).map vsz).sum = (c.map (fun y => vsz y + 2)).sum := by
    rw [List.map_map, List.map_reverse, List.sum_reverse]
    exact sum_map_congr' c (vsz ∘ lfWrap) (fun y => vsz y + 2) (fun y => vsz_lfWrap_eq y)
  have h2 : (c.reverse.map lfWrap).length = c.length := by simp
  simp only [lfRV, vsz_ofList_eq, h, h2]
  omega

/-- A constant list sums to its length. -/
private theorem sum_map_one' {α : Type} (l : List α) : (l.map (fun _ => (1 : ℕ))).sum = l.length := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

/-- Shifting a summand by a constant. -/
private theorem sum_map_add_const' (l : List Val) (f : Val → ℕ) (c : ℕ) :
    (l.map (fun y => f y + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

/-! ## The row decomposition -/

/-- `rowsOf` has exactly `t` entries. -/
private theorem rowsOf_len (t B : ℕ) (W : List Val) : (rowsOf t B W).length = t := by
  simp [rowsOf]

/-- The sum over the rows of a list is the sum over its first `t*B` elements (the rows of
`rowsOf t B W` are the consecutive windows of `W`). -/
private theorem rowsOfSum_gen (t B : ℕ) (W : List Val) (f : Val → ℕ) :
    ((rowsOf t B W).map (fun c => (c.map f).sum)).sum = ((W.take (t * B)).map f).sum := by
  induction t with
  | zero => simp [rowsOf]
  | succ t ih =>
    have hsplit : rowsOf (t + 1) B W = rowsOf t B W ++ [(W.drop (t * B)).take B] := by
      unfold rowsOf
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [hsplit, List.map_append, List.sum_append, ih, List.map_singleton, List.sum_singleton,
      ← List.sum_append, ← List.map_append, ← List.take_add, Nat.succ_mul]

/-- When `W` is exactly `t*B` long, summing over the rows of `W` is summing over `W`. -/
private theorem rowsOfSum_local (t B : ℕ) (W : List Val) (h : W.length = t * B) (f : Val → ℕ) :
    ((rowsOf t B W).map (fun c => (c.map f).sum)).sum = (W.map f).sum := by
  have ht : W.take (t * B) = W := by rw [← h]; exact List.take_of_length_le le_rfl
  rw [rowsOfSum_gen t B W f, ht]

/-! ## The size bound -/

theorem leafSize (t B : ℕ) (blk : List HvdH.Val) (hN : blk.length = t * B)
    (ht : 1 ≤ t) (hB : 1 ≤ B) :
    HvdH.vsz (HvdH.ofList (Work.SynFFT.lfRowsL t B blk.reverse blk.reverse)) + 1 ≤
      10 * (HvdH.vsz (HvdH.ofList blk) + 1) := by
  set W : List Val := blk.reverse with hWdef
  have hWlen : W.length = t * B := by rw [hWdef, List.length_reverse]; exact hN
  have hbrev : blk = W.reverse := by rw [hWdef, List.reverse_reverse]
  -- the accumulator is the reversed list of row values
  have hLR : lfRowsL t B W W = (List.map lfRV (rowsOf t B W)).reverse :=
    leafRowsL.2.2 t B W hB hWlen
  -- the total size of the row values
  have hsum : ((rowsOf t B W).map (fun c => vsz (lfRV c))).sum
      = (W.map (fun y => vsz y + 2)).sum + (W.length + t) := by
    have h1 : ((rowsOf t B W).map (fun c => vsz (lfRV c))).sum
        = ((rowsOf t B W).map
            (fun c : List Val => (c.map (fun y => vsz y + 2)).sum + (c.length + 1))).sum := by
      apply sum_map_congr'
      intro c
      exact vsz_lfRV_eq c
    have hlen : ((rowsOf t B W).map List.length).sum = W.length := by
      have h1' : ((rowsOf t B W).map List.length).sum
          = ((rowsOf t B W).map
              (fun c : List Val => (c.map (fun _ => (1 : ℕ))).sum)).sum := by
        apply sum_map_congr'
        intro c
        exact (sum_map_one' c).symm
      rw [h1', rowsOfSum_local t B W hWlen (fun _ => (1 : ℕ)), sum_map_one']
    have hone : ((rowsOf t B W).map (fun _ : List Val => (1 : ℕ))).sum = t := by
      rw [sum_map_one', rowsOf_len t B W]
    have h2 : ((rowsOf t B W).map (fun c : List Val => c.length + 1)).sum = W.length + t := by
      rw [List.sum_map_add (f := fun c : List Val => c.length) (g := fun _ : List Val => (1 : ℕ)),
        hlen, hone]
    rw [h1, List.sum_map_add (f := fun c : List Val => (c.map (fun y => vsz y + 2)).sum)
      (g := fun c : List Val => c.length + 1), h2,
      rowsOfSum_local t B W hWlen (fun y => vsz y + 2)]
  -- the size of the two sums
  have hT : (W.map (fun y => vsz y + 2)).sum = (W.map vsz).sum + 2 * W.length :=
    sum_map_add_const' W vsz 2
  have hAcc : vsz (ofList ((List.map lfRV (rowsOf t B W)).reverse))
      = ((rowsOf t B W).map (fun c => vsz (lfRV c))).sum + t + 1 := by
    rw [vsz_ofList_reverse' ((rowsOf t B W).map lfRV), vsz_map_ofList' (rowsOf t B W) lfRV,
      rowsOf_len t B W]
  have hblk : vsz (ofList blk) = (W.map vsz).sum + W.length + 1 := by
    rw [vsz_ofList_eq, hbrev, List.length_reverse, sum_map_reverse' W vsz]
  have htL : t ≤ W.length := by
    rw [hWlen]
    calc t = t * 1 := (Nat.mul_one t).symm
      _ ≤ t * B := Nat.mul_le_mul_left t hB
  have hLHS : vsz (ofList (lfRowsL t B W W)) + 1
      = ((rowsOf t B W).map (fun c => vsz (lfRV c))).sum + t + 1 + 1 := by
    rw [hLR, hAcc]
  rw [hLHS, hblk]
  omega

end Work.SynFFT
