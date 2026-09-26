import Mathlib
import Submission.Work.PTCert.RedWDefs

/-!
# The stack algorithm `redW`

`Submission.PTCert.redW` is the free-reduction function used by the `PTCert` word model: it scans
the word `w` left to right with the accumulator `acc` held *reversed* (top of stack first), popping
the top `d` of the stack when the new letter `c` is the inverse `d = c ^^^ 1` of it, and pushing `c`
otherwise.

This file proves the two structural facts about `redW` needed by the certificate glue:

* every letter of `redW w` is a letter of `w` (`redW` never invents letters), and
* `redW w` is freely reduced — no two adjacent letters are mutually inverse
  (`Work.PTCert.RedP`), which is the "stack invariant" of the algorithm.

Both are proved by the same induction on the fold: the invariant `RedP acc` (read on the
*top-first* accumulator, which is equivalent to `RedP` on the reversed accumulator by
`redP_reverse_iff`) is preserved by `redStep`, since either the new letter cancels the top of the
stack (a `List.IsChain.of_cons` step) or it is pushed next to a letter that is not its inverse
(a `List.IsChain.cons_cons` step).
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- `^^^ 1` is an involution on `ℕ`: `b = a ^^^ 1` iff `a = b ^^^ 1`. -/
lemma xor1_eq_iff (a b : ℕ) : (b = a ^^^ 1) ↔ (a = b ^^^ 1) := by
  constructor <;> intro h
  · rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Reversing a reduced word keeps it reduced. -/
lemma redP_reverse_iff {l : List ℕ} : RedP l.reverse ↔ RedP l := by
  unfold RedP
  rw [List.isChain_reverse]
  exact List.IsChain.iff fun a b => (not_congr (xor1_eq_iff a b)).symm

/-- One step of the stack algorithm only removes letters of the stack and adds the new letter. -/
lemma redStep_mem {acc : List ℕ} {c x : ℕ} (h : x ∈ redStep acc c) : x = c ∨ x ∈ acc := by
  cases acc with
  | nil => simp [redStep] at h; exact Or.inl h
  | cons d t =>
    by_cases hb : Nat.beq d (c ^^^ 1) = true
    · simp [redStep, hb] at h
      exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · simp [redStep, hb] at h
      rw [List.mem_cons]
      tauto

/-- Every letter left in the accumulator after a fold of `redStep` is a letter of the initial
accumulator or of the word processed. -/
lemma foldl_redStep_mem {w : List ℕ} : ∀ {acc : List ℕ} {x : ℕ},
    x ∈ w.foldl redStep acc → x ∈ acc ∨ x ∈ w := by
  induction w with
  | nil => intro acc x h; exact Or.inl (by simpa using h)
  | cons c t ih =>
      intro acc x h
      rw [List.foldl_cons] at h
      rcases ih h with h | h
      · rcases redStep_mem h with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      · exact Or.inr (by simp [h])

/-- `redStep` preserves reducedness of the stack. -/
lemma redStep_redP {acc : List ℕ} {c : ℕ} (h : RedP acc) : RedP (redStep acc c) := by
  cases acc with
  | nil => exact List.IsChain.singleton c
  | cons d t =>
    by_cases hb : d = c ^^^ 1
    · have hbt : Nat.beq d (c ^^^ 1) = true := by simpa [Nat.beq_eq] using hb
      show List.IsChain (fun a b : ℕ => b ≠ a ^^^ 1) (redStep (d :: t) c)
      rw [redStep, hbt]
      exact List.IsChain.of_cons h
    · have hbf : Nat.beq d (c ^^^ 1) = false := by
        cases hq : Nat.beq d (c ^^^ 1) with
        | true => exact absurd (by simpa [Nat.beq_eq] using hq) hb
        | false => rfl
      show List.IsChain (fun a b : ℕ => b ≠ a ^^^ 1) (redStep (d :: t) c)
      rw [redStep, hbf]
      exact List.IsChain.cons_cons hb h

/-- The stack invariant is preserved by the fold. -/
lemma foldl_redP {w : List ℕ} : ∀ {acc : List ℕ}, RedP acc → RedP (w.foldl redStep acc) := by
  induction w with
  | nil => intro acc h; exact h
  | cons c t ih => intro acc h; rw [List.foldl_cons]; exact ih (redStep_redP h)

/-- Every letter of `redW w` is a letter of `w`. -/
lemma redW_subset (w : List ℕ) (c : ℕ) (hc : c ∈ Submission.PTCert.redW w) : c ∈ w := by
  have h : c ∈ w.foldl redStep [] := by simpa [redW, List.mem_reverse] using hc
  rcases foldl_redStep_mem (w := w) (acc := []) h with h' | h'
  · simp at h'
  · exact h'

/-- `redW w` is freely reduced. -/
lemma redP_redW (w : List ℕ) : RedP (Submission.PTCert.redW w) := by
  have h : RedP (w.foldl redStep []) :=
    foldl_redP (acc := []) (List.IsChain.nil (R := fun a b : ℕ => b ≠ a ^^^ 1))
  have := redP_reverse_iff.mpr h
  simpa [redW] using this

theorem redWStack : (∀ (w : List ℕ) (c : ℕ), c ∈ Submission.PTCert.redW w → c ∈ w) ∧ (∀ w : List ℕ, RedP (Submission.PTCert.redW w)) :=
  ⟨redW_subset, redP_redW⟩

end Work.PTCert
