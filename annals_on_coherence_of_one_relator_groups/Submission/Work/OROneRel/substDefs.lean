import Mathlib
import Submission.Work.OROneRel.HNNStep

/-!
# The Magnus/Putman substitution `t ↦ t^p`, `x ↦ x * t^(-q)` at the level of words

The endomorphism `subst t x p q` of `F β` (`Submission.Work.OROneRel.HNNStep`) sends
`t ↦ t ^ p`, `x ↦ x * t ^ (-q)` and fixes every other generator.  For the transport of a
counterexample along this substitution one needs to control the *reduced word* of the image of a
reduced word.  This file introduces the letter-level description.

* `runLetters a n` is the signed run `a ^ n` as a word: `(a, true)` repeated `n` times if `n ≥ 0`
  and `(a, false)` repeated `|n|` times if `n < 0`.
* `blkLetter t x p q c` is the *block* of a letter `c = (a, b)`: the word of `substFun t x p q a`
  (resp. of its inverse if `b = false`), namely `t ^ p` for `a = t`, `x * t ^ (-q)` for `a = x`
  and the single letter `a` otherwise.
* `substList t x p q L` is the concatenation of the blocks of the letters of `L`.

The point of this description is that a block has at most one letter different from `t`, and its
first letter is its own generator (except for the block of `x⁻¹`, whose first letter is `t`); hence
free reduction of a concatenation of blocks never deletes a letter different from `t` and never
cancels two such letters, which makes the substituted word of a subword of a power of the relator
again a subword of a power of the substituted relator.
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-- The signed run `a ^ n` as a word: `(a, true)` repeated `n` times for `n ≥ 0`, and `(a, false)`
repeated `-n` times for `n < 0`. -/
def runLetters (a : β) (n : ℤ) : List (β × Bool) :=
  List.replicate n.natAbs (a, decide (0 < n))

@[simp] theorem runLetters_zero (a : β) : runLetters a 0 = [] := rfl

/-- The block substituted for a single letter `c = (a, b)`. -/
noncomputable def blkLetter (t x : β) (p q : ℤ) (c : β × Bool) : List (β × Bool) := by
  classical
  exact
    if c.1 = t then runLetters t (if c.2 then p else -p)
    else if c.1 = x then
      (if c.2 then [c] ++ runLetters t (-q) else runLetters t q ++ [c])
    else [c]

/-- The word obtained from `L` by substituting every letter by its block. -/
noncomputable def substList (t x : β) (p q : ℤ) (L : List (β × Bool)) : List (β × Bool) :=
  (L.map (blkLetter t x p q)).flatten

/-- A letter `c` is *safe as the first letter of an arc* (with respect to the substitution
`t ↦ t^p`, `x ↦ x t^(-q)`) if its block has no *leading* run of `t`-letters, so that the block does
not merge with the block to its left: this holds for `c.1 ∉ {t, x}` and also for `c = x⁺`
(the block `x * t^(-q)` begins with the letter `x`). -/
def SafeFirst (t x : β) (c : β × Bool) : Prop :=
  c.1 ≠ t ∧ ¬(c.1 = x ∧ c.2 = false)

/-- A letter `c` is *safe as the last letter of an arc* if its block has no *trailing* run of
`t`-letters, so that it does not merge with the block to its right: this holds for `c.1 ∉ {t, x}`
and also for `c = x⁻` (the block `t^q x⁻¹` ends with the letter `x⁻¹`). -/
def SafeLast (t x : β) (c : β × Bool) : Prop :=
  c.1 ≠ t ∧ ¬(c.1 = x ∧ c.2 = true)

end Work.OROneRel
