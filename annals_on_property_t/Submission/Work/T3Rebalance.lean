import Submission.Work.T2HalfHalf
import Submission.Work.NielsenEnergy

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# T3: the balanced decomposition and the rebalancing state

`T2HalfHalf.t2_balanced_of_not_fallI` shows that a confined interior factor
`w_j` whose two junction alignments absorb at most half of its word is in the
**balanced (half-half) state**: `|L_j| = 2k` with both junction alignments
equal to `k`.  This module turns that into the explicit word structure the
classical rebalancing consumes:

    L_j = A ++ B,  |A| = |B| = k,
    the tail of `w_{j-1}` equals `invRev A`   (left neighbour covers A exactly),
    the head of `w_{j+1}` equals `invRev B`   (right neighbour covers B exactly)

(`t3_balanced_decomposition`), via `junction_cancel_iff` (alignment `= k`
forces the drop/take inverse-reverse identities) and
`two_word_reduction_shape` consequences.  It also records the immediate
consequence (`t3_balanced_reduce`): in the balanced state the middle factor
cancels completely against its two neighbours — the reduced three-word
product is the reduction of the neighbours' remainders
`L_{j-1}` without its last `k` letters and `L_{j+1}` without its first `k`.

This is the structural base for the classical rebalancing move (T3): while
`w_j = A·B` sits balanced between neighbours, one combines a further element
that *ends with B* or *begins with A^{±1}* with `w_j`, shifting the balanced
position to an element of higher index; since the index strictly grows, a
strict shortening must reappear, and total length strictly decreases
(`NielsenEnergy.energy_terminates` provides the termination scaffold).  The
rebalancing protocol itself remains open; its state description is the
decomposition below.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **Balanced decomposition.**  Under the balanced-state hypotheses
(confined interior factor, no strict phase on either junction), with
`k := align L_{j-1} L_j`:

* `k` equals the alignment at the left junction and `|L_j| = 2k` (even; the
  split point is the half);
* the first `k` letters `A := L_j.take k` and the last `k` letters
  `B := L_j.drop k` each have length `k` (and concatenate to `L_j`);
* the tail of the left neighbour equals `invRev A` and the head of the right
  neighbour equals `invRev B` — the two halves are covered exactly. -/
theorem t3_balanced_decomposition {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j)
    (hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length)
    (hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length) :
    ∃ k : ℕ,
      k = align (Fs[j - 1]) (Fs[j]) ∧
      (Fs[j]).length = 2 * k ∧
      ((Fs[j]).take k).length = k ∧
      ((Fs[j]).drop k).length = k ∧
      (Fs[j - 1]).drop ((Fs[j - 1]).length - k) = FreeGroup.invRev ((Fs[j]).take k) ∧
      (Fs[j + 1]).take k = FreeGroup.invRev ((Fs[j]).drop k) := by
  classical
  let k : ℕ := align (Fs[j - 1]) (Fs[j])
  have hb := t2_balanced_of_not_fallI Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR
  rcases hb with ⟨hEqA, k0, hlen, hk0⟩
  have hkk : k = k0 := by simpa [k] using hk0
  have hlenK : (Fs[j]).length = 2 * k := by
    calc (Fs[j]).length = 2 * k0 := hlen
    _ = 2 * k := by rw [hkk]
  refine ⟨k, rfl, hlenK, ?_, ?_, ?_, ?_⟩
  · -- (L_j.take k).length = k
    have hle : k ≤ (Fs[j]).length := by
      rw [hlenK]
      omega
    simp [List.length_take, min_eq_left hle]
  · -- (L_j.drop k).length = k
    simp [List.length_drop]
    omega
  · -- left neighbour tail = invRev (L_j.take k)
    have hX : k ≤ (Fs[j - 1]).length := by
      have hbL := align_le_length_left (Fs[j - 1]) (Fs[j])
      omega
    have hY : k ≤ (Fs[j]).length := by
      rw [hlenK]
      omega
    have hc := (junction_cancel_iff (Fs[j - 1]) (Fs[j]) k hX hY).1 (by
      change align (Fs[j - 1]) (Fs[j]) ≤ align (Fs[j - 1]) (Fs[j])
      exact le_rfl)
    exact hc
  · -- right neighbour head = invRev (L_j.drop k)
    have hX : k ≤ (Fs[j]).length := by
      rw [hlenK]
      omega
    have hY : k ≤ (Fs[j + 1]).length := by
      have hbR := align_le_length_right (Fs[j]) (Fs[j + 1])
      omega
    have hc := (junction_cancel_iff (Fs[j]) (Fs[j + 1]) k hX hY).1 (by
      change align (Fs[j - 1]) (Fs[j]) ≤ align (Fs[j]) (Fs[j + 1])
      rw [hEqA])
    have hlen2 : (Fs[j]).length - k = k := by omega
    rw [hlen2] at hc
    have hinv := congrArg FreeGroup.invRev hc
    rw [FreeGroup.invRev_invRev] at hinv
    exact hinv.symm



/-! ## The rebalancing move: `α_q ↦ α_q · α_p⁻¹` is length non-increasing

Classical rebalancing: while the balanced element `α_p = A·B` (halves of
equal length, covered by its two neighbours) has a further element `α_q`
whose word *ends with the second half* `B`, combine it with `α_p` — replace
`α_q` by `α_q · α_p⁻¹`.  The `B`-suffix of `α_q` cancels against the
`invRev B` head of `α_p⁻¹`'s word, leaving the word of `y · A⁻¹` (`y` = the
word of `α_q` without its `B`-suffix): the `B`-block is replaced by
`invRev A` — "`A_p` (up to inversion) takes its place" — and the length does
not increase.  The word-level identity is unconditional:

    reduce ((y ++ B) ++ (invRev B ++ invRev A)) = reduce (y ++ invRev A)

(`B ++ invRev B` telescopes to the empty word), and the length bound follows
from the length of `y ++ invRev A`.
-/


/-- `B ++ invRev B` telescopes to the empty word for every word `B`. -/
lemma reduce_append_invRev_self {α : Type*} [DecidableEq α] (B : List (α × Bool)) :
    FreeGroup.reduce (B ++ FreeGroup.invRev B) = [] := by
  induction B with
  | nil => simp [FreeGroup.invRev]
  | cons x xs ih =>
      have hinv : FreeGroup.invRev (x :: xs) = FreeGroup.invRev xs ++ [letterInv x] := by
        rw [show (x :: xs) = [x] ++ xs by rfl]
        rw [FreeGroup.invRev_append]
        simp [FreeGroup.invRev, letterInv]
      rw [hinv]
      have hrest : FreeGroup.reduce (xs ++ FreeGroup.invRev xs ++ [letterInv x]) = [letterInv x] := by
        rw [reduce_assoc xs (FreeGroup.invRev xs) [letterInv x]]
        rw [ih]
        simp
      have hcancel : FreeGroup.reduce (x :: (xs ++ FreeGroup.invRev xs ++ [letterInv x])) = [] := by
        have hr : FreeGroup.reduce (xs ++ FreeGroup.invRev xs ++ [letterInv x]) =
            letterInv x :: [] := by simpa using hrest
        simpa using (reduce_cons_cancel (t := xs ++ FreeGroup.invRev xs ++ [letterInv x])
          (hd := letterInv x) (tl := []) hr (rfl : letterInv x = letterInv x))
      simpa using hcancel

/-- Reduction of a concatenation is invariant under reducing the second part
first. -/
lemma reduce_append_congr {α : Type*} [DecidableEq α]
    (y W1 W2 : List (α × Bool))
    (h : FreeGroup.reduce W1 = FreeGroup.reduce W2) :
    FreeGroup.reduce (y ++ W1) = FreeGroup.reduce (y ++ W2) := by
  apply FreeGroup.reduce.sound
  have hm1 : FreeGroup.mk (y ++ W1) = FreeGroup.mk y * FreeGroup.mk W1 := by
    rw [← FreeGroup.mul_mk]
  have hm2 : FreeGroup.mk (y ++ W2) = FreeGroup.mk y * FreeGroup.mk W2 := by
    rw [← FreeGroup.mul_mk]
  rw [hm1, hm2]
  have hr1 := congrArg FreeGroup.mk h
  have hw : FreeGroup.mk W1 = FreeGroup.mk W2 := by
    calc
      FreeGroup.mk W1 = FreeGroup.mk (FreeGroup.reduce W1) := (FreeGroup.reduce.self (L := W1)).symm
      _ = FreeGroup.mk (FreeGroup.reduce W2) := hr1
      _ = FreeGroup.mk W2 := FreeGroup.reduce.self (L := W2)
  rw [hw]

/-- Word-level content of the rebalancing move: adjoining `(A·B)⁻¹` (word
`invRev B ++ invRev A`) after a word `y ++ B` removes the `B`-block, leaving
`y ++ invRev A` (up to free reduction). -/
lemma rebalance_join_reduce {α : Type*} [DecidableEq α]
    (A B y : List (α × Bool)) :
    FreeGroup.reduce ((y ++ B) ++ (FreeGroup.invRev B ++ FreeGroup.invRev A)) =
      FreeGroup.reduce (y ++ FreeGroup.invRev A) := by
  calc
    FreeGroup.reduce ((y ++ B) ++ (FreeGroup.invRev B ++ FreeGroup.invRev A))
        = FreeGroup.reduce (y ++ (B ++ (FreeGroup.invRev B ++ FreeGroup.invRev A))) := by
            congr 1
            simp [List.append_assoc]
    _ = FreeGroup.reduce (y ++ FreeGroup.invRev A) := by
            apply reduce_append_congr y (B ++ (FreeGroup.invRev B ++ FreeGroup.invRev A))
              (FreeGroup.invRev A)
            rw [show B ++ (FreeGroup.invRev B ++ FreeGroup.invRev A) =
                (B ++ FreeGroup.invRev B) ++ FreeGroup.invRev A by simp [List.append_assoc]]
            rw [reduce_assoc B (FreeGroup.invRev B) (FreeGroup.invRev A)]
            rw [reduce_append_invRev_self B]
            simp

/-- Free reduction never increases the length of a word. -/
lemma reduce_length_le {α : Type*} [DecidableEq α] (W : List (α × Bool)) :
    (FreeGroup.reduce W).length ≤ W.length := by
  induction W with
  | nil => simp
  | cons l t ih =>
      cases hr : FreeGroup.reduce t with
      | nil =>
          rw [reduce_cons_nil hr]
          simp
      | cons hd tl =>
          have hlenr : (FreeGroup.reduce t).length = tl.length + 1 := by
            rw [hr]
            simp
          by_cases hc : letterInv l = hd
          · rw [reduce_cons_cancel hr hc]
            rw [List.length_cons]
            omega
          · rw [reduce_cons_nocancel hr hc]
            rw [List.length_cons, List.length_cons, List.length_cons]
            omega

/-- The rebalancing replacement is length non-increasing: whatever `y, B` are,
`|reduce ((y ++ B) ++ (invRev B ++ invRev A))| ≤ |y| + |A|`. -/
lemma rebalance_join_le {α : Type*} [DecidableEq α]
    (A B y : List (α × Bool)) :
    (FreeGroup.reduce ((y ++ B) ++ (FreeGroup.invRev B ++ FreeGroup.invRev A))).length
      ≤ y.length + A.length := by
  rw [rebalance_join_reduce A B y]
  have h1 := reduce_length_le (y ++ FreeGroup.invRev A)
  rw [List.length_append] at h1
  rw [FreeGroup.invRev_length] at h1
  omega


/-! ## Assembly: the one-step aggregate reduction and the protocol skeleton -/

/-- **The aggregate one-step reduction is forced.**  For a confined interior
factor `w_j` of a concatenation of reduced words, either a strict phase holds
at a junction — more than half of `w_j`'s word cancels against a neighbour, so
the combination with that neighbour has strictly fewer letters than the
neighbour (`fallI_left_shortens` / `fallI_right_shortens`), the elementary
reduction step — or the balanced half-half state holds with the explicit
decomposition of `t3_balanced_decomposition`.  (Assembly of
`t2_strict_or_balanced` + `fallI_*_shortens` + `t3_balanced_decomposition`.) -/
theorem t3_aggregate_step {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hm : j - 1 < Fs.length) (hconf : Confined Fs j) :
    (FreeGroup.reduce ((Fs[j - 1]) ++ (Fs[j]))).length < (Fs[j - 1]).length ∨
    (FreeGroup.reduce ((Fs[j]) ++ (Fs[j + 1]))).length < (Fs[j + 1]).length ∨
    (∃ k : ℕ,
      (Fs[j]).length = 2 * k ∧
      ((Fs[j]).take k).length = k ∧
      ((Fs[j]).drop k).length = k ∧
      (Fs[j - 1]).drop ((Fs[j - 1]).length - k) = FreeGroup.invRev ((Fs[j]).take k) ∧
      (Fs[j + 1]).take k = FreeGroup.invRev ((Fs[j]).drop k)) := by
  classical
  have hLred : FreeGroup.IsReduced (Fs[j - 1]) := by
    exact hred (Fs[j - 1]) (List.getElem_mem hm)
  have hRred : FreeGroup.IsReduced (Fs[j + 1]) := by
    exact hred (Fs[j + 1]) (List.getElem_mem hjk)
  rcases t2_strict_or_balanced Fs hred (j := j) hj hj0 hjk hm hconf with hsL | hsR | hbal
  · left
    exact fallI_left_shortens (Fs[j - 1]) (Fs[j]) hLred
      (hred (Fs[j]) (List.getElem_mem hj)) hsL
  · right; left
    exact fallI_right_shortens (Fs[j]) (Fs[j + 1])
      (hred (Fs[j]) (List.getElem_mem hj)) hRred hsR
  · right; right
    rcases hbal with ⟨hEq, k0, hlen, hk0⟩
    -- reconstruct the not-Fall-I hypotheses from the balanced conjuncts
    have hk0R : align (Fs[j]) (Fs[j + 1]) = k0 := by
      rw [← hEq]
      exact hk0
    have hnotL : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length := by
      rw [hk0, hlen]
    have hnotR : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length := by
      rw [hk0R, hlen]
    rcases t3_balanced_decomposition Fs hred (j := j) hj hj0 hjk hm hconf hnotL hnotR with
      ⟨k, _hk, hrest⟩
    exact ⟨k, hrest⟩

/-- **Termination skeleton of the rebalancing protocol.**  If a process on
states with a total-length measure `N` and a balanced-index `idx < c` takes
steps that either strictly decrease `N` or keep `N` equal while strictly
increasing `idx`, then it cannot run forever: the step relation is
well-founded (lexicographic measure `(N, c − idx)`; instance of
`energy_terminates`).  This is the formal content of "da n endlich ist und der
Index des zur Komposition verwendeten Elements dauernd wächst, ist dies
Verfahren nicht unbegrenzt fortsetzbar". -/
theorem rebalance_protocol_terminates {α : Type*} (N idx : α → ℕ) (c : ℕ)
    (hbound : ∀ x : α, idx x < c) :
    WellFounded (fun x y : α =>
      N x < N y ∨ (N x = N y ∧ idx y < idx x)) := by
  have hwf := energy_terminates (N := N) (e := fun z : α => c - idx z)
  have hEq : (fun x y : α => N x < N y ∨ (N x = N y ∧ idx y < idx x)) =
      (fun x y : α => N x < N y ∨ (N x = N y ∧ (c - idx x) < (c - idx y))) := by
    funext x y
    apply propext
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · rcases h with ⟨hN, hidx⟩
        right
        exact ⟨hN, by have hx := hbound x; have hy := hbound y; omega⟩
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · rcases h with ⟨hN, he⟩
        right
        exact ⟨hN, by have hx := hbound x; have hy := hbound y; omega⟩
  rwa [hEq]

end Submission.Nielsen
