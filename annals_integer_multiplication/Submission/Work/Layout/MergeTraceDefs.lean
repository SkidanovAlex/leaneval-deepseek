import Mathlib
import Submission.Work.Layout.MergeDefs

set_option autoImplicit false

/-!
# The lattice-path decomposition of `cmpCost`

`cmpCost ks ls` compares the heads of the two key lists and drops the head of `ls` when it is the
smaller one (as `Sk.merge2` does), otherwise the head of `ks`.  It is therefore a greedy merge, and
the sequence of compared pairs is a monotone lattice path from `(0,0)`: every step compares the two
heads and consumes exactly one of them.

`decomp`-free presentation used below:

* `colRecs ks ls` records, for every *column* of that path (a `ks` element that is the head while some
  up moves happen), the list of `ls` elements consumed by the up moves of that column.  Its first
  component is the column head `K`, its second the consumed elements (all `< K`, distinct);
* `rowRecs ks ls` dually records, for every *row* (an `ls` element while some right moves happen), the
  list of `ks` elements consumed by the right moves of that row;
* `pCost (K, vs) = |vs| * (K.size).size + Σ v∈vs (v.size).size + 4|vs|` is the cost of one record: one
  comparison per consumed element, each costing the cached key size `(K.size).size` of the head plus
  that of the consumed element plus `4`.

`Work.Layout.mergeRecs_cost` is the resulting identity
`cmpCost ks ls = Σ colRecs pCost + Σ rowRecs pCost`,
`Work.Layout.merge_cmpCost` combines it with the per-record estimate `Work.Layout.mergeLocal`
(coefficient `9`) and the sublist/`Nodup` structure of the records.
-/

namespace Work.Layout

open HvdH

/-- the cost of reading the cached key size of a key `k` -/
def szc (k : ℕ) : ℕ := (k.size).size

/-- the column records of the merge of `ks`, `ls` -/
def colRecs : List ℕ → List ℕ → List (ℕ × List ℕ)
  | [], _ => []
  | k :: ks, ls => (k, ls.takeWhile (· < k)) :: colRecs ks (ls.dropWhile (· < k))
termination_by ks ls => ks.length + ls.length
decreasing_by
  simp_wf
  have := List.length_dropWhile_le (fun x : ℕ => decide (x < k)) ls
  omega

/-- the row records of the merge of `ks`, `ls` -/
def rowRecs : List ℕ → List ℕ → List (ℕ × List ℕ)
  | _, [] => []
  | ks, l :: ls => (l, ks.takeWhile (· ≤ l)) :: rowRecs (ks.dropWhile (· ≤ l)) ls
termination_by ks ls => ks.length + ls.length
decreasing_by
  simp_wf
  have := List.length_dropWhile_le (fun x : ℕ => decide (x ≤ l)) ks
  omega

/-- the cost charged to one record -/
def pCost (p : ℕ × List ℕ) : ℕ := p.2.length * szc p.1 + (p.2.map szc).sum + 4 * p.2.length

/-! ## elementary facts -/

theorem pCost_cons (K l : ℕ) (vs : List ℕ) :
    pCost (K, l :: vs) = pCost (K, vs) + szc K + szc l + 4 := by
  simp only [pCost, List.length_cons, List.map_cons, List.sum_cons]; ring

theorem pCost_nil (K : ℕ) : pCost (K, []) = 0 := by simp [pCost]

theorem pCost_le (K : ℕ) (vs : List ℕ) :
    pCost (K, vs) ≤ vs.length * szc K + (vs.map (fun v => v.size)).sum + 5 * vs.length := by
  have h1 : (vs.map szc).sum ≤ (vs.map (fun v => v.size)).sum :=
    List.sum_le_sum (fun v _ => size_le_self v.size)
  simp only [pCost]
  omega

/-! ## `takeWhile`/`dropWhile` at a head -/

theorem takeWhile_cons_lt {k l : ℕ} {ls : List ℕ} (h : l < k) :
    (l :: ls).takeWhile (fun x => decide (x < k)) = l :: ls.takeWhile (fun x => decide (x < k)) := by
  simp [List.takeWhile_cons_of_pos, h]

theorem dropWhile_cons_lt {k l : ℕ} {ls : List ℕ} (h : l < k) :
    (l :: ls).dropWhile (fun x => decide (x < k)) = ls.dropWhile (fun x => decide (x < k)) := by
  simp [List.dropWhile_cons_of_pos, h]

theorem takeWhile_cons_ge {k l : ℕ} {ls : List ℕ} (h : ¬ l < k) :
    (l :: ls).takeWhile (fun x => decide (x < k)) = [] := by
  simp [List.takeWhile_cons_of_neg, h]

theorem dropWhile_cons_ge {k l : ℕ} {ls : List ℕ} (h : ¬ l < k) :
    (l :: ls).dropWhile (fun x => decide (x < k)) = l :: ls := by
  simp [List.dropWhile_cons_of_neg, h]

theorem takeWhile_cons_le {k l : ℕ} {ks : List ℕ} (h : k ≤ l) :
    (k :: ks).takeWhile (fun x => decide (x ≤ l)) = k :: ks.takeWhile (fun x => decide (x ≤ l)) := by
  simp [List.takeWhile_cons_of_pos, h]

theorem dropWhile_cons_le {k l : ℕ} {ks : List ℕ} (h : k ≤ l) :
    (k :: ks).dropWhile (fun x => decide (x ≤ l)) = ks.dropWhile (fun x => decide (x ≤ l)) := by
  simp [List.dropWhile_cons_of_pos, h]

theorem takeWhile_cons_gt {k l : ℕ} {ks : List ℕ} (h : l < k) :
    (k :: ks).takeWhile (fun x => decide (x ≤ l)) = [] := by
  simp [List.takeWhile_cons_of_neg, h]

theorem dropWhile_cons_gt {k l : ℕ} {ks : List ℕ} (h : l < k) :
    (k :: ks).dropWhile (fun x => decide (x ≤ l)) = k :: ks := by
  simp [List.dropWhile_cons_of_neg, h]

/-! ## the cost identity -/

theorem colSum_cons (k : ℕ) (ks ls : List ℕ) :
    ((colRecs (k :: ks) ls).map pCost).sum
      = pCost (k, ls.takeWhile (fun x => decide (x < k)))
        + ((colRecs ks (ls.dropWhile (fun x => decide (x < k)))).map pCost).sum := by
  simp only [colRecs, List.map_cons, List.sum_cons]

theorem rowSum_cons (ks : List ℕ) (l : ℕ) (ls : List ℕ) :
    ((rowRecs ks (l :: ls)).map pCost).sum
      = pCost (l, ks.takeWhile (fun x => decide (x ≤ l)))
        + ((rowRecs (ks.dropWhile (fun x => decide (x ≤ l))) ls).map pCost).sum := by
  simp only [rowRecs, List.map_cons, List.sum_cons]

theorem colSum_cons_lt {k : ℕ} {ks ls : List ℕ} {l : ℕ} (h : l < k) :
    ((colRecs (k :: ks) (l :: ls)).map pCost).sum
      = ((colRecs (k :: ks) ls).map pCost).sum + szc k + szc l + 4 := by
  rw [colSum_cons, colSum_cons, takeWhile_cons_lt h, dropWhile_cons_lt h, pCost_cons]
  simp only [szc]
  ring

theorem colSum_cons_ge {k : ℕ} {ks ls : List ℕ} {l : ℕ} (h : ¬ l < k) :
    ((colRecs (k :: ks) (l :: ls)).map pCost).sum = ((colRecs ks (l :: ls)).map pCost).sum := by
  rw [colSum_cons, takeWhile_cons_ge h, dropWhile_cons_ge h, pCost_nil]
  simp

theorem rowSum_cons_gt {k : ℕ} {ks ls : List ℕ} {l : ℕ} (h : l < k) :
    ((rowRecs (k :: ks) (l :: ls)).map pCost).sum = ((rowRecs (k :: ks) ls).map pCost).sum := by
  rw [rowSum_cons, takeWhile_cons_gt h, dropWhile_cons_gt h, pCost_nil]
  simp

theorem rowSum_cons_le {k : ℕ} {ks ls : List ℕ} {l : ℕ} (h : k ≤ l) :
    ((rowRecs (k :: ks) (l :: ls)).map pCost).sum
      = ((rowRecs ks (l :: ls)).map pCost).sum + szc k + szc l + 4 := by
  rw [rowSum_cons, rowSum_cons, takeWhile_cons_le h, dropWhile_cons_le h, pCost_cons]
  simp only [szc]
  ring

theorem colRecs_nil_right (ks : List ℕ) : ((colRecs ks []).map pCost).sum = 0 := by
  induction ks with
  | nil => simp [colRecs]
  | cons k ks ih => rw [colRecs]; simp [pCost_nil, ih]

theorem rowRecs_nil_left (ls : List ℕ) : ((rowRecs [] ls).map pCost).sum = 0 := by
  induction ls with
  | nil => simp [rowRecs]
  | cons l ls ih => rw [rowRecs]; simp [pCost_nil, ih]

theorem mergeRecs_cost (ks ls : List ℕ) :
    cmpCost ks ls = ((colRecs ks ls).map pCost).sum + ((rowRecs ks ls).map pCost).sum := by
  suffices h : ∀ n, ∀ ks ls : List ℕ, ks.length + ls.length = n →
      cmpCost ks ls = ((colRecs ks ls).map pCost).sum + ((rowRecs ks ls).map pCost).sum by
    exact h _ ks ls rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ks ls hlen
    match ks, ls with
    | [], _ => simp [cmpCost, colRecs, rowRecs_nil_left]
    | _ :: _, [] => simp [cmpCost, rowRecs, colRecs_nil_right]
    | k :: ks, l :: ls =>
      by_cases hlt : l < k
      · have ih1 := ih ((k :: ks).length + ls.length)
            (by simp only [List.length_cons] at hlen ⊢; omega) (k :: ks) ls rfl
        rw [cmpCost, if_pos hlt, ih1, colSum_cons_lt hlt, rowSum_cons_gt hlt]
        simp only [szc]
        ring
      · have hle : k ≤ l := by omega
        have ih1 := ih (ks.length + (l :: ls).length)
            (by simp only [List.length_cons] at hlen ⊢; omega) ks (l :: ls) rfl
        rw [cmpCost, if_neg hlt, ih1, colSum_cons_ge hlt, rowSum_cons_le hle]
        simp only [szc]
        ring

end Work.Layout
