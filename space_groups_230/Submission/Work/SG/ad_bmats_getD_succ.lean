import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# The `bmats` recursion step, read off at the parent index

`Data.bmats (Ad j)` is the list of blocks of the class-`j` cocycle table, obtained by a left fold
over the BFS parent list `(Ad j).par`.  Entry `i+1` of that list is the block attached to the
`i`-th parent entry `par j i = (par1 j i, par2 j i)`, namely `sgStep (Ad j) acc (par j i)` for the
accumulator `acc` after `i` steps.

The point of this file is to make that unfolding available in terms of the *final* list: the parent
entry `par2 j i` is `≤ i` (`RC.par2_le`), so the block at index `par2 j i` of the accumulator after
`i` steps already equals the block at index `par2 j i` of the completely folded list
(`sgFold_getD_prefix`).

The fold helper below is a local copy of the corresponding (identically defined) machinery of
`Submission.Work.SG.ApplyBDefs`, kept here under its own names so that this file builds
independently of it.
-/

namespace Work.SG

/-! ## A local copy of the "fold left, appending one element per step" machinery -/

/-- Left fold of `List β` over `List α` that appends `f acc p` at each step. -/
def sgFold {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) : List α :=
  l.foldl (fun acc p => acc ++ [f acc p]) init

theorem sgFold_cons {α β : Type*} (p : β) (l : List β) (init : List α)
    (f : List α → β → α) :
    sgFold (p :: l) init f = sgFold l (init ++ [f init p]) f := by
  simp only [sgFold, List.foldl_cons]

theorem sgGetD_concat {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  rw [List.getElem_append_right (le_refl _)]
  simp

theorem sgFold_length {α β : Type*} (l : List β) (init : List α) (f : List α → β → α) :
    (sgFold l init f).length = init.length + l.length := by
  induction l generalizing init with
  | nil => simp [sgFold]
  | cons p l ih =>
    rw [sgFold_cons, ih (init ++ [f init p])]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem sgFold_getD_lt {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) {n : ℕ} (hn : n < init.length) :
    (sgFold l init f).getD n d = init.getD n d := by
  induction l generalizing init with
  | nil => simp [sgFold]
  | cons p l ih =>
    have hn' : n < (init ++ [f init p]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [sgFold_cons, ih _ hn']
    exact List.getD_append init [f init p] d n hn

theorem sgFold_getD_eq {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) (d' : β) (t : ℕ) (ht : t < l.length) :
    (sgFold l init f).getD (init.length + t) d
      = f (sgFold (l.take t) init f) (l.getD t d') := by
  induction l generalizing init t with
  | nil => simp at ht
  | cons p l ih =>
    match t with
    | 0 =>
      rw [sgFold_cons, Nat.add_zero]
      have h1 : (sgFold l (init ++ [f init p]) f).getD init.length d = f init p := by
        rw [sgFold_getD_lt l (init ++ [f init p]) f d (by simp)]
        exact sgGetD_concat init (f init p) d
      rw [h1]
      simp [sgFold]
    | t + 1 =>
      have ht' : t < l.length := by simpa using ht
      have hb : init.length + (t + 1) = (init ++ [f init p]).length + t := by
        rw [List.length_append, List.length_cons, List.length_nil]; omega
      rw [sgFold_cons, hb, ih (init ++ [f init p]) t ht']
      have h1 : sgFold (l.take t) (init ++ [f init p]) f
          = sgFold ((p :: l).take (t + 1)) init f := by
        rw [List.take_succ_cons, sgFold_cons]
      have h2 : l.getD t d' = (p :: l).getD (t + 1) d' := by simp
      rw [h1, h2]

theorem sgFold_append {α β : Type*} (l1 l2 : List β) (init : List α) (f : List α → β → α) :
    sgFold (l1 ++ l2) init f = sgFold l2 (sgFold l1 init f) f := by
  simp only [sgFold, List.foldl_append]

/-- The value at index `e` of the accumulator is already fixed as soon as the accumulated list is
longer than `e` (there `s` steps suffice, and any later prefix gives the same value). -/
theorem sgFold_getD_prefix {α β : Type*} (l : List β) (init : List α) (f : List α → β → α)
    (d : α) (s t e : ℕ) (hst : s ≤ t) (ht : t ≤ l.length) (he : e < init.length + s) :
    (sgFold l init f).getD e d = (sgFold (l.take t) init f).getD e d := by
  conv_lhs => rw [← List.take_append_drop t l]
  rw [sgFold_append]
  rw [sgFold_getD_lt _ _ _ _ (by rw [sgFold_length, List.length_take]; omega)]

/-! ## `Data.bmats` as such a fold, and its recursion step -/

/-- One step of `Data.bmats`: the block attached to `par`-entry `p`, given the accumulator. -/
def sgStep (D : Data.ArithData) (acc : List (List Data.M3)) (p : ℕ × ℕ) : List Data.M3 :=
  (List.range D.gens.length).map (fun g' => Data.M3.add
    (if g' = p.1 then Data.M3.one else Data.M3.zero)
    (Data.M3.mul (D.gens.getD p.1 Data.M3.one) ((acc.getD p.2 []).getD g' Data.M3.zero)))

theorem bmats_sgFold (D : Data.ArithData) :
    Data.bmats D = sgFold D.par [List.replicate D.gens.length Data.M3.zero] (sgStep D) := rfl

/-! ## The requested recursion identity -/

theorem ad_bmats_getD_succ (j : Fin 73) (i : ℕ) (hi : i < (Work.SG.RC.Ad j).par.length) :
    (Work.SG.Data.bmats (Work.SG.RC.Ad j)).getD (i + 1) [] =
      (List.range (Work.SG.RC.KK j)).map (fun g' => Work.SG.Data.M3.add
        (if g' = Work.SG.RC.par1 j i then Work.SG.Data.M3.one else Work.SG.Data.M3.zero)
        (Work.SG.Data.M3.mul (Work.SG.RC.gMt j (Work.SG.RC.par1 j i))
          (((Work.SG.Data.bmats (Work.SG.RC.Ad j)).getD (Work.SG.RC.par2 j i) []).getD g' Work.SG.Data.M3.zero))) := by
  rw [bmats_sgFold]
  -- `i + 1 = init.length + i` for the one-element initial accumulator.
  rw [show i + 1 = List.length [List.replicate (RC.Ad j).gens.length Data.M3.zero] + i by
        simp [Nat.add_comm]]
  -- The `i`-th fold step is the `i`-th parent entry applied to the accumulator after `i` steps.
  rw [sgFold_getD_eq (RC.Ad j).par [List.replicate (RC.Ad j).gens.length Data.M3.zero]
        (sgStep (RC.Ad j)) [] (0, 0) i hi]
  -- Replace the block at index `par2 j i` of the final list by the one in the `i`-step
  -- accumulator: `par2 j i ≤ i`, so that entry is already frozen.
  rw [sgFold_getD_prefix (RC.Ad j).par [List.replicate (RC.Ad j).gens.length Data.M3.zero]
        (sgStep (RC.Ad j)) [] i i (RC.par2 j i) (le_refl i) (le_of_lt hi)
        (by
          have h := RC.par2_le j i hi
          have h1 : List.length [List.replicate (RC.Ad j).gens.length Data.M3.zero] = 1 := by simp
          omega)]
  -- Both sides are now the same expression, up to unfolding of the `RC` accessors.
  rfl

end Work.SG
