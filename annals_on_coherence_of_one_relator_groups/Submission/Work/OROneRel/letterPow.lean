/-
Auxiliary vocabulary for the norm-`≤ 2` case of Weinbaum's theorem.

A length-`2` reduced word is `mk [(a,s),(b,t)]`, i.e. the product of the two one-letter words
`mk [(a,true)] = of a` and `mk [(a,false)] = (of a)⁻¹`.  We package the one-letter word as
`letterPow a s` and record the elementary API (reduced word, length, letters, nontriviality, inverse,
and the product decomposition of a two-letter word).
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.relatorLetters_mul_subset

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The one-letter word `of a` (if `s = true`) or its inverse (if `s = false`), i.e.
`FreeGroup.mk [(a, s)]`. -/
def letterPow (a : α) (s : Bool) : FreeGroup α := FreeGroup.mk [(a, s)]

@[simp] theorem letterPow_true (a : α) : letterPow a true = FreeGroup.of a := rfl

@[simp] theorem letterPow_false (a : α) : letterPow a false = (FreeGroup.of a)⁻¹ := rfl

theorem toWord_letterPow [DecidableEq α] (a : α) (s : Bool) :
    FreeGroup.toWord (letterPow a s) = [(a, s)] := by
  show FreeGroup.toWord (FreeGroup.mk [(a, s)]) = [(a, s)]
  rw [FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq FreeGroup.IsReduced.singleton]

theorem relatorNorm_letterPow (a : α) (s : Bool) : relatorNorm (letterPow a s) = 1 := by
  classical
  simp [relatorNorm, FreeGroup.norm, toWord_letterPow]

theorem relatorLetters_letterPow (a : α) (s : Bool) : relatorLetters (letterPow a s) = {a} := by
  classical
  ext c
  simp only [relatorLetters, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [toWord_letterPow]
  constructor
  · rintro ⟨b, hb⟩
    have h' : c = a ∧ b = s := by simpa using hb
    exact h'.1
  · intro h
    subst h
    exact ⟨s, by simp⟩

theorem letterPow_ne_one (a : α) (s : Bool) : letterPow a s ≠ 1 := by
  classical
  intro h
  have hw := congrArg FreeGroup.toWord h
  rw [toWord_letterPow, FreeGroup.toWord_one] at hw
  exact List.cons_ne_nil _ _ hw

theorem letterPow_inv (a : α) (s : Bool) : (letterPow a s)⁻¹ = letterPow a (!s) := by
  cases s <;> rfl

/-- `FreeGroup.mk` of a two-letter word is the product of the two one-letter words. -/
theorem mk_pair (a b : α) (s t : Bool) :
    FreeGroup.mk [(a, s), (b, t)] = letterPow a s * letterPow b t := by
  change FreeGroup.mk ([(a, s)] ++ [(b, t)]) =
    FreeGroup.mk [(a, s)] * FreeGroup.mk [(b, t)]
  rw [FreeGroup.mul_mk]

/-- The letters of `letterPow a s * letterPow b t` are among `a` and `b`. -/
theorem relatorLetters_letterPow_mul_subset (a b : α) (s t : Bool) :
    relatorLetters (letterPow a s * letterPow b t) ⊆ ({a, b} : Set α) := by
  intro c hc
  rcases relatorLetters_mul_subset (letterPow a s) (letterPow b t) hc with h | h
  · rw [relatorLetters_letterPow] at h
    simp only [Set.mem_singleton_iff] at h
    subst h; simp
  · rw [relatorLetters_letterPow] at h
    simp only [Set.mem_singleton_iff] at h
    subst h; simp

end Work.OROneRel
