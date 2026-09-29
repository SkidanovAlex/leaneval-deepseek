import Mathlib
import Submission.Work.Layout.Base
import Submission.Work.Layout.Move
import Submission.Work.Layout.SortMain
import Submission.Work.Layout.distribute_ev
import Submission.Work.Layout.assemble_ev
import Submission.Work.Layout.listsSpecAlt
import Submission.Work.Layout.sortListAux
import Submission.Work.Layout.mergePair_ev
import Submission.Work.Layout.pass2_ev2

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Layout

open HvdH

/-- `a ≠ b` from a `Nodup` list `a :: l` and a membership `b ∈ l`. -/
theorem ne_of_nodup_cons {a b : Stk} {l : List Stk} (h : (a :: l).Nodup) (hb : b ∈ l) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  exact (List.nodup_cons.mp h).1 hb

/-- **`LayoutLib.sortByKey`**: sort records `cons (int k) payload` with distinct natural keys by key.
Route: bottom-up merge sort on stacks (split into singleton runs, then `⌈log₂ N⌉` merge passes; comparing
two keys = comparing two `int`s on stack 0 with `IntLib.lt`, or a raw comparison).
`Submission/Work/Layout/sortedKeyIndex.lean` (already proved) gives the "sorted permutation of the labels
is `range N`" fact. -/
theorem sortByKeyWord (hI : HvdH.IntLib) : ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val),
    (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int k) v) → (xs.map pairKey).Nodup →
    WordR main p (fun vs => ∃ rest, vs = ofList xs :: rest)
      (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧ ys.Perm xs ∧
        ys.Pairwise fun a b => pairKey a < pairKey b)
      (fun _ => K * (vsz (ofList xs) + 1) * (xs.length.size + 1)) := by
  obtain ⟨pLt, KLt, hLt⟩ := hI.lt
  obtain ⟨pSz, KSz, hSz⟩ := hI.size
  have hLists : Sk.ListsSpec := listsSpecAlt
  have hAux := sortListAux hLists
  have hDist : ∀ main : Cmd, Sk.DistSpec main := by
    intro main
    intro X Y t d hdis g S xs A J1 J2 h0 hX hY
    have hd2 : ([Y, t, d, 0] : List Stk).Nodup := (List.nodup_cons.mp hdis).2
    have hd3 : ([t, d, 0] : List Stk).Nodup := (List.nodup_cons.mp hd2).2
    have hd4 : ([d, 0] : List Stk).Nodup := (List.nodup_cons.mp hd3).2
    exact distribute_ev (main := main) (X := X) (Y := Y) (t := t) (d := d)
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hdis (by simp))
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hd2 (by simp))
      (ne_of_nodup_cons hd2 (by simp)) (ne_of_nodup_cons hd3 (by simp))
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hd2 (by simp))
      (ne_of_nodup_cons hd3 (by simp)) (ne_of_nodup_cons hd4 (by simp))
      h0 hX hY
  have hAsm : ∀ main : Cmd, Sk.AsmSpec main := by
    intro main
    intro X Z t d hdis g S rs J R hX hrs hrec hne h0
    have hd2 : ([Z, t, d, 0] : List Stk).Nodup := (List.nodup_cons.mp hdis).2
    have hd3 : ([t, d, 0] : List Stk).Nodup := (List.nodup_cons.mp hd2).2
    have hd4 : ([d, 0] : List Stk).Nodup := (List.nodup_cons.mp hd3).2
    exact assemble_ev (main := main) (X := X) (Z := Z) (t := t) (d := d)
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hdis (by simp))
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hd2 (by simp))
      (ne_of_nodup_cons hd2 (by simp)) (ne_of_nodup_cons hd3 (by simp))
      (ne_of_nodup_cons hdis (by simp)) (ne_of_nodup_cons hd2 (by simp))
      (ne_of_nodup_cons hd3 (by simp)) (ne_of_nodup_cons hd4 (by simp))
      hX hrs hrec hne h0
  obtain ⟨K, hK⟩ := Sk.sortMain pLt pSz KLt KSz hLists hDist hAsm
    (fun main => pass2_ev2)
    (fun main SX SY T D SA SB F1 F2 t d hdis => mergePair_ev hLt hSz hdis)
    (fun xs => hAux.1 xs) (fun xs ps qs h => hAux.2.1 xs ps qs h)
    (fun rs J h1 h2 => hAux.2.2 rs J h1 h2)
  exact ⟨Sk.sortProg pLt pSz, K, hK⟩

end Work.Layout
