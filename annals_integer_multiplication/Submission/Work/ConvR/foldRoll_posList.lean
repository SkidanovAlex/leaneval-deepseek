import Mathlib
import Submission.Work.ConvR.permDefs
import Submission.Work.ConvR.compDecomp

/-!
# `foldRoll (posList σ.reverse) (head ++ tail) = σ.map (fun i => head.getD i .nil) ++ tail`

Combinatorial core of the "permute the top of the value stack" word `Work.ConvR.permTop`.

Write `t := σ.reverse` and let `g i := head.getD i .nil`.  Processing `t` in order, rolling the
element `t_j` to the front at each step, the loop invariant after `j` steps is

  `foldRoll (posList (t.take j)) (head ++ tail)
      = (t.take j).reverse.map g ++ ((List.range n).filter (· ∉ t.take j)).map g ++ tail`,

the front holding the already moved elements (most recently moved first) and the middle holding the
untouched remainder of `head` in its original order.  The position of `t_j` inside the untouched
part is `t_j - #{l < j : t_l < t_j}` (the entry supplied by `posList`), which is the content of
`compDecomp` below.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-! ## Basic list manipulations -/

/-- `foldRoll` distributes over appending one position at the end. -/
theorem foldRoll_append_singleton (ps : List ℕ) (p : ℕ) (w : List Val) :
    foldRoll (ps ++ [p]) w = rollL p (foldRoll ps w) := by
  induction ps generalizing w with
  | nil => rfl
  | cons q ps ih => exact ih (rollL q w)

/-- Erasing the element just after a prefix `A` of `A ++ x :: B`. -/
theorem eraseIdx_append_length (A B : List Val) (x : Val) :
    (A ++ x :: B).eraseIdx A.length = A ++ B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, List.length_cons, List.eraseIdx_cons_succ, ih]

/-- `rollL` at the position of the head of the tail: moving the element at position `A.length` of
`A ++ x :: B` to the front. -/
theorem rollL_mid (A B : List Val) (x : Val) :
    rollL A.length (A ++ x :: B) = x :: (A ++ B) := by
  unfold rollL
  rw [List.getD_append_right A (x :: B) Val.nil A.length (le_refl _)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rw [eraseIdx_append_length]

/-- Unfold the `posList` entry corresponding to a new last element. -/
theorem posList_concat (u : List ℕ) (a : ℕ) :
    posList (u ++ [a]) = posList u ++ [u.length + a - ((u.filter (fun i => i < a)).length)] := by
  unfold posList
  rw [show (u ++ [a]).length = u.length + 1 from by simp]
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' : j < u.length := List.mem_range.mp hj
    rw [List.getD_append u [a] 0 j hj', List.take_append_of_le_length (le_of_lt hj')]
  · simp

/-- A list is the map of `getD · d` over its index range. -/
theorem range_map_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero]
    congr 1
    rw [List.map_map]
    have h : (fun i => (x :: xs).getD i d) ∘ Nat.succ = fun i => xs.getD i d := by
      funext i; simp [Function.comp]
    rw [h]
    exact ih

/-! ## Counting `filter (· < a)` in a nodup list -/

/-- For a nodup list `u`, the number of elements `< a` equals the number of `i < a` occurring
in `u`. -/
theorem count_identity (u : List ℕ) (a : ℕ) (hnd : u.Nodup) :
    ((List.range a).filter (fun i => i ∈ u)).length = (u.filter (fun i => i < a)).length := by
  have h1 : ((List.range a).filter (fun i => i ∈ u)).length
      = ((List.range a).filter (fun i => i ∈ u)).toFinset.card :=
    (List.toFinset_card_of_nodup (List.Nodup.filter (fun i => decide (i ∈ u)) List.nodup_range)).symm
  have h2 : (u.filter (fun i => i < a)).length
      = (u.filter (fun i => i < a)).toFinset.card :=
    (List.toFinset_card_of_nodup (hnd.filter (fun i => decide (i < a)))).symm
  rw [h1, h2]
  congr 1
  ext x
  simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset, List.mem_range,
    decide_eq_true_iff]
  tauto

/-- In a nodup list, at most `a` entries are `< a`. -/
theorem filter_lt_length_le {u : List ℕ} {a : ℕ} (hnd : u.Nodup) :
    (u.filter (fun i => i < a)).length ≤ a := by
  rw [← count_identity u a hnd]
  exact le_trans (List.length_filter_le _ _) (by simp [List.length_range])

/-! ## Main theorem -/

theorem foldRoll_posList (head tail : List HvdH.Val) (σ : List ℕ) (n : ℕ)
    (hh : head.length = n) (hσ : σ.length = n) (hperm : σ.Perm (List.range n)) :
    foldRoll (posList σ.reverse) (head ++ tail) =
      σ.map (fun i => head.getD i HvdH.Val.nil) ++ tail := by
  let t : List ℕ := σ.reverse
  let g : ℕ → Val := fun i => head.getD i Val.nil
  have htlen : t.length = n := by simp [t, hσ]
  have htp : t.Perm (List.range n) := by
    have h1 : t.Perm σ := List.reverse_perm σ
    exact h1.trans hperm
  have htnodup : t.Nodup := htp.symm.nodup List.nodup_range
  have htmem : ∀ i ∈ t, i < n := fun i hi => List.mem_range.mp (htp.mem_iff.mp hi)
  have key : ∀ j ≤ n, foldRoll (posList (t.take j)) (head ++ tail) =
      (t.take j).reverse.map g ++ ((List.range n).filter (fun i => i ∉ t.take j)).map g ++ tail := by
    intro j
    induction j with
    | zero =>
      intro _
      have hfilt : (List.range n).filter (fun i => i ∉ ([] : List ℕ)) = List.range n :=
        List.filter_eq_self.mpr (by intro i _; simp)
      have hg : (List.range n).map g = head := by
        rw [← hh]; exact range_map_getD head Val.nil
      rw [List.take_zero, hfilt, hg]
      simp [foldRoll, posList]
    | succ j ih =>
      intro hj1
      have hjn : j < n := Nat.lt_of_succ_le hj1
      have ihj := ih (le_of_lt hjn)
      have hjt : j < t.length := by omega
      set a : ℕ := t.getD j 0 with ha_def
      have htake : t.take (j+1) = t.take j ++ [a] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hjt]
        simp only [Option.toList_some]
        rw [ha_def, List.getD_eq_getElem t 0 hjt]
      have hnodu : (t.take j).Nodup := List.Sublist.nodup (List.take_sublist j t) htnodup
      have hltu : ∀ i ∈ t.take j, i < n := fun i hi => htmem i (List.take_subset j t hi)
      have ha_lt : a < n := by
        rw [ha_def, List.getD_eq_getElem t 0 hjt]
        exact htmem _ (List.getElem_mem hjt)
      have ha_not : a ∉ t.take j := by
        have hnp : (t.take j ++ [a]).Nodup := by
          rw [← htake]
          exact List.Sublist.nodup (List.take_sublist (j+1) t) htnodup
        intro hmem
        exact (List.nodup_append.mp hnp).2.2 a hmem a (by simp) rfl
      obtain ⟨ca, cr, hcd, hclen, hcc⟩ := compDecomp (t.take j) a n hnodu hltu ha_lt ha_not
      have hA : (t.take j ++ [a]).reverse.map g = g a :: (t.take j).reverse.map g := by simp
      have hroll : rollL ((t.take j).length + a - ((t.take j).filter (fun i => i < a)).length)
          ((t.take j).reverse.map g ++ ((List.range n).filter (fun i => i ∉ t.take j)).map g ++ tail) =
          (t.take j ++ [a]).reverse.map g ++
            ((List.range n).filter (fun i => i ∉ (t.take j ++ [a]))).map g ++ tail := by
        have hB : ((List.range n).filter (fun i => i ∉ t.take j)).map g
            = ca.map g ++ g a :: cr.map g := by
          rw [hcd, List.map_append, List.map_cons]
        have hp : (t.take j).length + a - ((t.take j).filter (fun i => i < a)).length
            = ((t.take j).reverse.map g ++ ca.map g).length := by
          simp only [List.length_append, List.length_map, List.length_reverse]
          have hle : ((t.take j).filter (fun i => i < a)).length ≤ a :=
            filter_lt_length_le (u := t.take j) (a := a) hnodu
          omega
        have harg : ((t.take j).reverse.map g ++ (ca.map g ++ g a :: cr.map g)) ++ tail
            = ((t.take j).reverse.map g ++ ca.map g) ++ g a :: (cr.map g ++ tail) := by
          simp [List.append_assoc]
        rw [hB, hp, harg, hA, hcc, List.map_append]
        rw [rollL_mid]
        simp only [List.append_assoc, List.cons_append]
      have hstep : foldRoll (posList (t.take (j+1))) (head ++ tail) =
          (t.take (j+1)).reverse.map g ++
            ((List.range n).filter (fun i => i ∉ t.take (j+1))).map g ++ tail := by
        rw [htake, posList_concat, foldRoll_append_singleton, ihj]
        exact hroll
      exact hstep
  have htn : t.take n = t := by rw [← htlen, List.take_length]
  have hfilt0 : (List.range n).filter (fun i => i ∉ t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    simp only [decide_eq_true_iff, not_not]
    exact htp.mem_iff.mpr hi
  have hσt : σ.reverse = t.take n := by rw [htn]
  rw [hσt, key n le_rfl, htn, hfilt0]
  simp [g, t]

end Work.ConvR
