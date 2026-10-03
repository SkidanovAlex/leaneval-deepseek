import Mathlib
import Submission.Work.OROneRel.weinbaum_at

/-!
# The generators occurring in a positive power `u ^ l`

For a nontrivial power `u ^ l` (`l ≥ 1`) of a free-group element, the set of generators occurring
in `u ^ l` is exactly the set of generators occurring in `u`:
`relatorLetters (u ^ l) = relatorLetters u`.

The interesting direction is `⊇`: `relatorLetters (u ^ l) ⊆ relatorLetters u` holds for *every*
`n` (`relatorLetters_pow_subset`), but a generator of `u` need not survive in a general power —
cancellation can remove letters.  What saves the day for `l ≥ 1` is that cancellation in
`u ^ l = u * ⋯ * u` only eats into the two ends of the reduced word of `u`: writing
`w = u.toWord`, Mathlib's `FreeGroup.reduceCyclically.reduce_flatten_replicate` gives

`reduce (replicate l w).flatten = conj w ++ (replicate l (reduceCyclically w)).flatten ++ invRev (conj w)`,

whereas `w` itself is the conjugate `conj w ++ reduceCyclically w ++ invRev (conj w)`
(`conj_conjugator_reduceCyclically`).  So both words consist of the same "conjugator" pieces glued
around the cyclically reduced core, and the only difference is that the core is repeated `l ≥ 1`
times.  Repeating a nonempty list (or an empty one) does not change its set of letters, and `invRev`
preserves it too; hence the two letter sets agree.

## Main declaration

* `relatorLetters_pow`
-/

namespace Work.OROneRel

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

theorem relatorLetters_pow {β : Type u} (u : FreeGroup β) {l : ℕ} (hl : 1 ≤ l) :
    Work.OROneRel.relatorLetters (u ^ l) = Work.OROneRel.relatorLetters u := by
  classical
  -- `toWord` is obtained by reducing the concatenation of `l` copies of `u.toWord`.
  have hred : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  have hkey : FreeGroup.reduce (List.replicate l u.toWord).flatten =
      FreeGroup.reduceCyclically.conjugator u.toWord
        ++ (List.replicate l (FreeGroup.reduceCyclically u.toWord)).flatten
        ++ FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator u.toWord) := by
    rw [FreeGroup.reduceCyclically.reduce_flatten_replicate hred l, if_neg (by omega)]
  -- `u.toWord` is the same word with the cyclically reduced core appearing only once.
  have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically u.toWord
  have hmain : listLetters ((u ^ l).toWord) = listLetters u.toWord := by
    rw [FreeGroup.toWord_pow u l, hkey]
    -- The repeated core contributes the same letters once as `l ≥ 1` times.
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
  have h1 : relatorLetters (u ^ l) = listLetters ((u ^ l).toWord) := rfl
  have h2 : relatorLetters u = listLetters u.toWord := rfl
  rw [h1, h2, hmain]

end Work.OROneRel
