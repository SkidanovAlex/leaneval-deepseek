import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The generators occurring in a positive power `u ^ l` (import-hygiene copy)

This is a verbatim copy of `Work.OROneRel.relatorLetters_pow`
(`Submission/Work/OROneRel/relatorLetters_pow.lean`), moved into the namespace `Work.ORLyndon` and
stripped of its (unused) import of `Submission.Work.OROneRel.weinbaum_at`.  That import makes the
original reach `Submission.Work.OROneRel.mrslAux`, which currently redeclares
`Work.OROneRel.toWord_pow_of_isCyclicallyReduced` (already declared in
`Submission/Work/OROneRel/magnus_step_root.lean`); any module importing both copies fails with
`environment already contains ...`, so the `ORLyndon` chain cannot use the original.

Delete this file (and switch the two imports back) as soon as the duplicate declaration is removed
on the `OROneRel` side.

## Main declaration

* `Work.ORLyndon.relatorLetters_pow`
-/

set_option autoImplicit false

namespace Work.ORLyndon

universe u

/-- The set of generators occurring in a list of signed letters, i.e. the projection of the list to
its first coordinate. -/
def listLetters {α : Type*} (L : List (α × Bool)) : Set α := {a | ∃ b, (a, b) ∈ L}

/-- The letters of a concatenation are the union of the letters of the two factors. -/
lemma listLetters_append {α : Type*} (L M : List (α × Bool)) :
    listLetters (L ++ M) = listLetters L ∪ listLetters M := by
  ext a
  simp only [listLetters, Set.mem_ofPred_eq, Set.mem_union, List.mem_append, exists_or]

/-- Flattening `l ≥ 1` copies of a list does not change its set of letters: every copy has the same
letters, and (`l ≥ 1`) every letter of `L` occurs in some copy. -/
lemma listLetters_flatten_replicate {α : Type*} (L : List (α × Bool)) {l : ℕ} (hl : 1 ≤ l) :
    listLetters (List.replicate l L).flatten = listLetters L := by
  ext a
  simp only [listLetters, Set.mem_ofPred_eq, List.mem_flatten, List.mem_replicate]
  constructor
  · rintro ⟨b, M, ⟨_, hML⟩, hb⟩
    rw [hML] at hb
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, L, ⟨⟨by omega, rfl⟩, hb⟩⟩

/-- `FreeGroup.invRev` reverses a word and flips the exponent bits, so it preserves the set of
generators occurring in the word (the existential quantifier over the sign makes the flipped bits
irrelevant). -/
lemma listLetters_invRev {α : Type*} (L : List (α × Bool)) :
    listLetters (FreeGroup.invRev L) = listLetters L := by
  ext a
  simp only [listLetters, Set.mem_ofPred_eq, FreeGroup.invRev, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨b, g, hg, hgb⟩
    refine ⟨g.2, ?_⟩
    have h1 : g.1 = a := by
      have := congrArg Prod.fst hgb
      simpa using this
    have : g = (a, g.2) := by cases g; simp_all
    rwa [this] at hg
  · rintro ⟨b, hb⟩
    exact ⟨!b, (a, b), hb, rfl⟩

/-- For `l ≥ 1` the generators occurring in `u ^ l` are exactly those occurring in `u`. -/
theorem relatorLetters_pow {β : Type u} (u : FreeGroup β) {l : ℕ} (hl : 1 ≤ l) :
    Work.OROneRel.relatorLetters (u ^ l) = Work.OROneRel.relatorLetters u := by
  classical
  have hred : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  have hkey : FreeGroup.reduce (List.replicate l u.toWord).flatten =
      FreeGroup.reduceCyclically.conjugator u.toWord
        ++ (List.replicate l (FreeGroup.reduceCyclically u.toWord)).flatten
        ++ FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator u.toWord) := by
    rw [FreeGroup.reduceCyclically.reduce_flatten_replicate hred l, if_neg (by omega)]
  have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically u.toWord
  have hmain : listLetters ((u ^ l).toWord) = listLetters u.toWord := by
    rw [FreeGroup.toWord_pow u l, hkey]
    rw [show listLetters (FreeGroup.reduceCyclically.conjugator u.toWord
          ++ (List.replicate l (FreeGroup.reduceCyclically u.toWord)).flatten
          ++ FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator u.toWord))
        = listLetters (FreeGroup.reduceCyclically.conjugator u.toWord
          ++ FreeGroup.reduceCyclically u.toWord
          ++ FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator u.toWord)) from by
      simp only [listLetters_append,
        listLetters_flatten_replicate (FreeGroup.reduceCyclically u.toWord) hl,
        listLetters_invRev]]
    rw [hconj]
  have h1 : Work.OROneRel.relatorLetters (u ^ l) = listLetters ((u ^ l).toWord) := rfl
  have h2 : Work.OROneRel.relatorLetters u = listLetters u.toWord := rfl
  rw [h1, h2, hmain]

end Work.ORLyndon
