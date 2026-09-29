import Mathlib
import Submission.Work.TMC14Core.InvSumAux

/-!
# `TMC14Core.wordSumAux`: shared vocabulary for the word-sum recursion

`wordSum ω n a` sums `ω ^ invCount n f` over the words `f : Fin n → Bool × Bool`
of length `n` whose letters all lie in `{U, V} = {(true,true), (false,true)}` and
that contain exactly `a` letters `U`.

Here we isolate the *letter constraint* as a named, reducible predicate so that
statements about `wordSum` can be written without repeating it.
-/

noncomputable section

namespace Work.TMC14Core

/-- `letterOK n f` says every letter of the length-`n` word `f` is one of the two
admissible letters `U = (true,true)` and `V = (false,true)`.  It is the letter
constraint appearing in the definition of `wordSum`. -/
abbrev letterOK (n : ℕ) (f : Fin n → Bool × Bool) : Prop :=
  ∀ i, f i = (true, true) ∨ f i = (false, true)

end Work.TMC14Core
