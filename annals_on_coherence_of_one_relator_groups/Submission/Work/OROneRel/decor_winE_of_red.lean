import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_pow_flatMap

/-!
# The window condition is inherited along a reduction of the decorated word

`FreeGroup.Red L₁ L₂` is the reflexive-transitive closure of the deletion of an adjacent cancelling
pair `(x, b) (x, !b)` (`FreeGroup.Red.Step`).  The decoration `decor c i` keeps *exactly* the symbols
of the surviving letters: deleting the pair `(x, b) (x, !b)` from `L` at running level `i` deletes
the two decorated symbols

* `((x, i), b)` and `((x, i + c x), !b)`  (if `b = true`), or
* `((x, i - c x), b)` and `((x, i), !b)`  (if `b = false`),

and -- because the two letters carry opposite weights -- the running level *after* the pair is again
`i`, so the decoration of the remainder is untouched.  Consequently

  `decor c i L₂` is a **sublist** of `decor c i L₁` whenever `FreeGroup.Red L₁ L₂`.

This is the `i = 0` statement below (`decor_sublist_of_red`), and the lemma of this file is its
immediate consequence: a condition on the *edges* `coverEdge q` of the decorated letters which holds
for all `q ∈ decor c 0 L₁` (here: `coverEdge q ∈ winE c lo hi`, the edge lies in the window) still
holds for all `q ∈ decor c 0 L₂`.  No hypothesis on the weights `c` and no reducedness of `L₁` or
`L₂` is used.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The weight of a two-letter cancelling pair vanishes. -/
theorem lsig_pair_cancelling (c : α → ℤ) (x : α) (b : Bool) : lsig c [(x, b), (x, !b)] = 0 := by
  cases b <;> simp [lsig]

/-- **The decoration of a cancelling pair.**  Decorating at level `i` the letters of a cancelling
pair followed by `B` is the same as decorating the pair alone and then `B` at the *same* level `i`:
the running level returns to `i` after the pair. -/
theorem decor_pair_cancelling (c : α → ℤ) (i : ℤ) (x : α) (b : Bool) (B : List (α × Bool)) :
    decor c i ((x, b) :: (x, !b) :: B) = decor c i [(x, b), (x, !b)] ++ decor c i B := by
  have h : (x, b) :: (x, !b) :: B = [(x, b), (x, !b)] ++ B := rfl
  rw [h, decor_append, lsig_pair_cancelling, add_zero]

/-- The explicit form of a one-step reduction: `L₁` is obtained from `L₂` by inserting an adjacent
cancelling pair. -/
theorem Red_Step_exists_decomp {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    ∃ (A B : List (α × Bool)) (x : α) (b : Bool),
      L₁ = A ++ (x, b) :: (x, !b) :: B ∧ L₂ = A ++ B := by
  cases h with
  | not => exact ⟨_, _, _, _, rfl, rfl⟩

/-- **One reduction step only deletes decorated symbols**: the decoration of the reduced word is a
sublist of the decoration of the original word. -/
theorem decor_step_sublist (c : α → ℤ) (i : ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) : List.Sublist (decor c i L₂) (decor c i L₁) := by
  obtain ⟨A, B, x, b, h1, h2⟩ := Red_Step_exists_decomp h
  subst h1
  subst h2
  cases b
  · -- the pair is `(x, true) (x, false)`
    rw [decor_append, decor_append,
      decor_pair_cancelling c (i + lsig c A) x false B]
    exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)
  · -- the pair is `(x, false) (x, true)`
    rw [decor_append, decor_append,
      decor_pair_cancelling c (i + lsig c A) x true B]
    exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)

/-- **The decoration of a reduction is a sublist of the decoration of the original word.** -/
theorem decor_sublist_of_red (c : α → ℤ) (i : ℤ) {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red L₁ L₂) : List.Sublist (decor c i L₂) (decor c i L₁) := by
  induction h generalizing i with
  | refl => exact List.Sublist.refl _
  | tail hab hbc ih => exact (decor_step_sublist c i hbc).trans (ih i)

theorem decor_winE_of_red {α : Type u} [DecidableEq α] (c : α → ℤ) (lo hi : ℤ)
    {L₁ L₂ : List (α × Bool)} (h : FreeGroup.Red L₁ L₂)
    (hW : ∀ q ∈ Work.OROneRel.decor c 0 L₁, Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi) :
    ∀ q ∈ Work.OROneRel.decor c 0 L₂, Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi := by
  intro q hq
  exact hW q (List.Sublist.mem hq (decor_sublist_of_red c 0 h))

end Work.OROneRel
