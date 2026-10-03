import Mathlib
import Submission.Work.OROneRel.wgtMMDefs

/-!
# The reduced word of a power of a cyclically reduced relator

If the reduced word of an element `u` of a free group is cyclically reduced, then the reduced word
of `u ^ l` is the concatenation of `l` copies of the reduced word of `u`:

`wordOf (u ^ l) = (List.replicate l (wordOf u)).flatten`.

Indeed `FreeGroup.toWord_pow` writes `toWord (u ^ l)` as the maximal reduction of the `l`-fold
concatenation of `toWord u`, and that concatenation is already reduced: a cancellation is possible
only either inside one copy (excluded because `toWord u` is reduced) or at a junction between two
consecutive copies, i.e. between the last and the first letter of `toWord u` (excluded by cyclic
reducedness).  The latter statement is `FreeGroup.IsCyclicallyReduced.flatten_replicate` of
Mathlib, so the maximal reduction does nothing
(`FreeGroup.IsReduced.reduce_eq`).

The lemma `wordOf` of this development is `FreeGroup.toWord` at the `Classical.decEq` instance, and
`IsCyclicallyReducedRelator` is likewise phrased at that instance; since `Decidable _` is a
subsingleton, any two `DecidableEq` instances give the same word, which is how the proof below
moves between the classical instance used in the statement and the ambient instance of the goal.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The general form of `wordOf_pow_flatten`, phrased for `FreeGroup.toWord` at an arbitrary
`DecidableEq` instance. -/
theorem toWord_pow_eq_flatten_replicate {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hcyc : FreeGroup.IsCyclicallyReduced u.toWord) :
    (u ^ l).toWord = List.flatten (List.replicate l u.toWord) := by
  rw [FreeGroup.toWord_pow,
      FreeGroup.IsReduced.reduce_eq ((hcyc.flatten_replicate l).isReduced)]

theorem wordOf_pow_flatten {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u) :
    Work.OROneRel.wordOf (u ^ l) = List.flatten (List.replicate l (Work.OROneRel.wordOf u)) := by
  -- First move `wordOf` (classical instance) to `FreeGroup.toWord` at the ambient instance.
  have hword : ∀ x : FreeGroup α, wordOf x = @FreeGroup.toWord α ‹DecidableEq α› x := fun x => by
    rw [show wordOf x = @FreeGroup.toWord α (Classical.decEq α) x from rfl]
    rw [Subsingleton.elim (Classical.decEq α) ‹DecidableEq α›]
  -- The same transfer for the hypothesis `IsCyclicallyReducedRelator u`.
  have hcyc0 : FreeGroup.IsCyclicallyReduced (wordOf u) := hcyc
  have hcyc' : FreeGroup.IsCyclicallyReduced u.toWord := by
    rw [hword u] at hcyc0
    exact hcyc0
  rw [hword (u ^ l), hword u, toWord_pow_eq_flatten_replicate u l hcyc']

end Work.OROneRel
