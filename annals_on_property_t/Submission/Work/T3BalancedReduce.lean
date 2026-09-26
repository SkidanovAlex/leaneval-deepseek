import Submission.Work.T3Rebalance

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# T3 (continued): the balanced middle factor cancels completely

`T3Rebalance.t3_balanced_decomposition` records the balanced half-half state
of a confined interior factor `L_j = A ++ B` (`|A| = |B|`), with the tail of
the left neighbour equal to `invRev A` and the head of the right neighbour
equal to `invRev B`.  The classical aggregate picture ("das von seinen beiden
Nachbarelementen ganz absorbiert wird", Nielsen 1919 p. 270) then says: the
letters of the middle factor vanish entirely when the three neighbouring
words are concatenated and freely reduced — the balanced state is a *full
absorption* of `w_j` into its two neighbours.

This module proves that word content (the pieces the classical rebalancing
protocol consumes at the letter level):

* `reduce_middle_empty` — a middle block that reduces to the empty word
  contributes nothing to the reduction of `X ++ M ++ Z` (so the letter block
  `invRev A ++ A ++ B ++ invRev B` telescopes away in any context);
* **`triple_balanced_reduce_raw`** — the pure word identity
  `reduce ((X ++ invRev A) ++ ((A ++ B) ++ (invRev B ++ Z))) = reduce (X ++ Z)`;
* **`t3_balanced_reduce`** — in the balanced state the three-word reduction
  of `w_{j-1} w_j w_{j+1}` is the reduction of the two neighbour remainders
  (left neighbour without its covering tail, right neighbour without its
  covering head): the middle factor is fully absorbed;
* `t3_balanced_reduce_length` — length form: the reduced triple is no longer
  than the sum of the two remainders `|L_{j-1}| + |L_{j+1}| - 2k`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- A middle block that freely reduces to the empty word contributes nothing:
`X ++ M ++ Z` and `X ++ Z` have the same reduction.  (Free reduction is
associative over concatenation — `reduce_append_reduce` — so the middle can
be pre-reduced to `[]`.) -/
lemma reduce_middle_empty {α : Type*} [DecidableEq α]
    (X M Z : List (α × Bool)) (hM : FreeGroup.reduce M = []) :
    FreeGroup.reduce (X ++ (M ++ Z)) = FreeGroup.reduce (X ++ Z) := by
  have hredMZ : FreeGroup.reduce (M ++ Z) = FreeGroup.reduce Z := by
    calc
      FreeGroup.reduce (M ++ Z)
          = FreeGroup.reduce (FreeGroup.reduce M ++ FreeGroup.reduce Z) :=
            reduce_append_reduce M Z
      _ = FreeGroup.reduce Z := by rw [hM]; simp
  calc
    FreeGroup.reduce (X ++ (M ++ Z))
        = FreeGroup.reduce (FreeGroup.reduce X ++ FreeGroup.reduce (M ++ Z)) :=
          reduce_append_reduce X (M ++ Z)
    _ = FreeGroup.reduce (FreeGroup.reduce X ++ FreeGroup.reduce Z) := by rw [hredMZ]
    _ = FreeGroup.reduce (X ++ Z) := (reduce_append_reduce X Z).symm

/-- **Pure balanced-triple identity.**  If a word splits as `(X ++ invRev A)
++ ((A ++ B) ++ (invRev B ++ Z))` — the `A B` block is written with its
inverse word before it and its inverse word after it — then the whole word
reduces exactly as `X ++ Z` does: the `invRev A ++ A` and `B ++ invRev B`
blocks telescope away and the middle contributes nothing. -/
lemma triple_balanced_reduce_raw {α : Type*} [DecidableEq α]
    (X A B Z : List (α × Bool)) :
    FreeGroup.reduce
        ((X ++ FreeGroup.invRev A) ++ ((A ++ B) ++ (FreeGroup.invRev B ++ Z))) =
      FreeGroup.reduce (X ++ Z) := by
  let M : List (α × Bool) := FreeGroup.invRev A ++ A ++ B ++ FreeGroup.invRev B
  have hC : FreeGroup.reduce (FreeGroup.invRev A ++ A) = [] :=
    FreeGroup.reduce_invRev_left_cancel (L := A)
  have hD : FreeGroup.reduce (B ++ FreeGroup.invRev B) = [] :=
    reduce_append_invRev_self B
  have hAssoc : M = (FreeGroup.invRev A ++ A) ++ (B ++ FreeGroup.invRev B) := by
    simp [M, List.append_assoc]
  have hM : FreeGroup.reduce M = [] := by
    calc
      FreeGroup.reduce M
          = FreeGroup.reduce ((FreeGroup.invRev A ++ A) ++ (B ++ FreeGroup.invRev B)) := by
              rw [hAssoc]
      _ = FreeGroup.reduce
            (FreeGroup.reduce (FreeGroup.invRev A ++ A)
              ++ FreeGroup.reduce (B ++ FreeGroup.invRev B)) :=
            reduce_append_reduce (FreeGroup.invRev A ++ A) (B ++ FreeGroup.invRev B)
      _ = FreeGroup.reduce ([] ++ []) := by rw [hC, hD]
      _ = [] := by rfl
  have hList : ((X ++ FreeGroup.invRev A) ++ ((A ++ B) ++ (FreeGroup.invRev B ++ Z))) =
      X ++ (M ++ Z) := by
    simp [M, List.append_assoc]
  rw [hList]
  exact reduce_middle_empty X M Z hM

/-- **T3, balanced state: the middle factor is fully absorbed by its two
neighbours.**  Under the balanced-state hypotheses (`t3_balanced_decomposition`,
with `k := align L_{j-1} L_j`), the reduced three-word concatenation
`L_{j-1} ++ L_j ++ L_{j+1}` equals the reduction of the two neighbour
remainders — the left neighbour with its covering tail `invRev A` removed and
the right neighbour with its covering head `invRev B` removed. -/
theorem t3_balanced_reduce {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j)
    (hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length)
    (hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length) :
    FreeGroup.reduce (Fs[j - 1] ++ Fs[j] ++ Fs[j + 1]) =
      FreeGroup.reduce
        (Fs[j - 1].take ((Fs[j - 1]).length - align (Fs[j - 1]) (Fs[j]))
          ++ Fs[j + 1].drop (align (Fs[j - 1]) (Fs[j]))) := by
  classical
  rcases t3_balanced_decomposition Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR with
    ⟨k, hk, hlen, hlenA, hlenB, htail, hhead⟩
  -- hk : k = align (Fs[j-1]) (Fs[j])
  -- htail : (Fs[j-1]).drop ((Fs[j-1]).length - k) = invRev ((Fs[j]).take k)
  -- hhead : (Fs[j+1]).take k = invRev ((Fs[j]).drop k)
  let A : List (α × Bool) := Fs[j].take k
  let B : List (α × Bool) := Fs[j].drop k
  let X : List (α × Bool) := Fs[j - 1].take ((Fs[j - 1]).length - k)
  let Z : List (α × Bool) := Fs[j + 1].drop k
  have hleft : Fs[j - 1] = X ++ FreeGroup.invRev A := by
    have hta := List.take_append_drop ((Fs[j - 1]).length - k) (Fs[j - 1])
    have htailA : (Fs[j - 1]).drop ((Fs[j - 1]).length - k) = FreeGroup.invRev A := by
      simpa [A] using htail
    rw [← hta]
    rw [htailA]
  have hmid : Fs[j] = A ++ B := by
    have hta := List.take_append_drop k (Fs[j])
    simp [A, B, hta]
  have hright : Fs[j + 1] = FreeGroup.invRev B ++ Z := by
    have hta := List.take_append_drop k (Fs[j + 1])
    have hheadB : (Fs[j + 1]).take k = FreeGroup.invRev B := by
      simpa [B] using hhead
    rw [← hta]
    rw [hheadB]
  have hconcat : Fs[j - 1] ++ Fs[j] ++ Fs[j + 1] =
      (X ++ FreeGroup.invRev A) ++ ((A ++ B) ++ (FreeGroup.invRev B ++ Z)) := by
    calc
      Fs[j - 1] ++ Fs[j] ++ Fs[j + 1]
          = (Fs[j - 1] ++ Fs[j]) ++ Fs[j + 1] := by rw [List.append_assoc]
      _ = ((X ++ FreeGroup.invRev A) ++ (A ++ B)) ++ (FreeGroup.invRev B ++ Z) := by
          rw [hleft, hmid, hright]
      _ = (X ++ FreeGroup.invRev A) ++ ((A ++ B) ++ (FreeGroup.invRev B ++ Z)) := by
          rw [List.append_assoc]
  have hpure := triple_balanced_reduce_raw (X := X) (A := A) (B := B) (Z := Z)
  rw [hconcat, hpure]
  rw [← hk]

/-- **Length form of the balanced absorption.**  In the balanced state the
letters of the middle factor `L_j` vanish from the reduced three-word product:
its length is at most the sum of the two neighbour remainders,
`|L_{j-1}| + |L_{j+1}| - 2·align L_{j-1} L_j` (in particular `w_j` contributes
nothing). -/
theorem t3_balanced_reduce_length {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j)
    (hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length)
    (hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length) :
    (FreeGroup.reduce (Fs[j - 1] ++ Fs[j] ++ Fs[j + 1])).length ≤
      (Fs[j - 1]).length + (Fs[j + 1]).length
        - 2 * align (Fs[j - 1]) (Fs[j]) := by
  classical
  rcases t3_balanced_decomposition Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR with
    ⟨k, hk, hlen, hlenA, hlenB, htail, hhead⟩
  have hred3 := t3_balanced_reduce Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR
  rw [hred3]
  have hle1 := reduce_length_le
    (Fs[j - 1].take ((Fs[j - 1]).length - align (Fs[j - 1]) (Fs[j]))
      ++ Fs[j + 1].drop (align (Fs[j - 1]) (Fs[j])))
  -- hle1 : |reduce (take … ++ drop …)| ≤ |take … ++ drop …|
  rw [List.length_append] at hle1
  have hkL : align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j - 1]).length := align_le_length_left _ _
  have hkR : align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j + 1]).length := by
    have hEq := t2_balanced_of_not_fallI Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR
    rcases hEq with ⟨hEqA, k0, hlen0, hk0⟩
    rw [hEqA]
    exact align_le_length_right (Fs[j]) (Fs[j + 1])
  -- |take (|L_{j-1}| − a) L_{j-1}| = |L_{j-1}| − a  (a := align …)
  have hlenT : (Fs[j - 1].take ((Fs[j - 1]).length - align (Fs[j - 1]) (Fs[j]))).length
      = (Fs[j - 1]).length - align (Fs[j - 1]) (Fs[j]) := by
    rw [List.length_take]
    rw [min_eq_left]
    omega
  -- |drop a L_{j+1}| = |L_{j+1}| − a
  have hlenD : (Fs[j + 1].drop (align (Fs[j - 1]) (Fs[j]))).length
      = (Fs[j + 1]).length - align (Fs[j - 1]) (Fs[j]) := by
    rw [List.length_drop]
  omega

end Submission.Nielsen
