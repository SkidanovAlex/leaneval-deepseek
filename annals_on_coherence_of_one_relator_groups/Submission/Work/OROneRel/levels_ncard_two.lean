import Mathlib
import Submission.Work.OROneRel.GaugeDefs

/-!
# The set of levels of the decorated word has at least two elements

Let `c : α → ℤ` be a weight function and `u : FreeGroup α` a word.  The decorated word
`decor c 0 (wordOf u)` is a list of symbols `((x, i), b)`, and each such symbol "runs" from the level
`coverSrc c ·` to the level `coverTgt c ·`; the two differ by `± c x`.

Hence if some letter `a` of the reduced word of `u` has nonzero weight, the set of levels

`{coverSrc c p | p ∈ decor c 0 (wordOf u)} ∪ {coverTgt c p | p ∈ decor c 0 (wordOf u)}`

contains the two distinct levels `coverSrc c p₀ ≠ coverTgt c p₀` of the corresponding decorated
symbol `p₀`, and therefore has at least two elements.  This is the "at least one edge" input to the
gauge argument: the levels spanned by the edges of the `ℤ`-cover of the one-relator presentation
`⟨α | u⟩` form a connected interval with at least two points.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **Decoration preserves the underlying letters.**  If the letter `(x, b)` occurs in the word `L`,
then for any initial level `i` some decorated symbol with underlying letter `x` and sign `b` occurs in
`decor c i L`.

The level of that symbol is the running weight of the prefix preceding the occurrence of the letter:
`i + (weight of the prefix)` for a positive letter, `i + (weight of the prefix) - c x` for a negative
one.  We only need existence, not the value. -/
theorem exists_mem_decor_of_mem (c : α → ℤ) :
    ∀ (i : ℤ) (L : List (α × Bool)) (x : α) (b : Bool), (x, b) ∈ L →
      ∃ j : ℤ, ((x, j), b) ∈ decor c i L := by
  intro i L
  induction L generalizing i with
  | nil => intro x b h; simp at h
  | cons q L' ih =>
      intro x b h
      obtain ⟨x', b'⟩ := q
      rw [List.mem_cons] at h
      rcases h with h | h
      · -- the head of the list is the letter we are looking for
        have hx : x = x' := congrArg Prod.fst h
        have hb : b = b' := congrArg Prod.snd h
        subst hx; subst hb
        cases b
        · exact ⟨i - c x, by
            rw [show decor c i ((x, false) :: L') =
              ((x, i - c x), false) :: decor c (i - c x) L' from rfl]
            exact List.mem_cons_self⟩
        · exact ⟨i, by
            rw [show decor c i ((x, true) :: L') =
              ((x, i), true) :: decor c (i + c x) L' from rfl]
            exact List.mem_cons_self⟩
      · -- the letter occurs deeper in the list; recurse at the shifted level
        cases b'
        · obtain ⟨j, hj⟩ := ih (i - c x') x b h
          exact ⟨j, by
            rw [show decor c i ((x', false) :: L') =
              ((x', i - c x'), false) :: decor c (i - c x') L' from rfl]
            exact List.mem_cons_of_mem _ hj⟩
        · obtain ⟨j, hj⟩ := ih (i + c x') x b h
          exact ⟨j, by
            rw [show decor c i ((x', true) :: L') =
              ((x', i), true) :: decor c (i + c x') L' from rfl]
            exact List.mem_cons_of_mem _ hj⟩

/-- **A decorated letter of nonzero weight spans two distinct levels.**  The level at which the
symbol starts and the level at which it ends differ by `c x`. -/
theorem coverSrc_ne_coverTgt (c : α → ℤ) (x : α) (hx : c x ≠ 0) (j : ℤ) (b : Bool) :
    coverSrc c ((x, j), b) ≠ coverTgt c ((x, j), b) := by
  cases b
  · simp only [coverSrc, coverTgt, Bool.false_eq_true, if_false]
    intro h
    exact hx (by linarith)
  · simp only [coverSrc, coverTgt, if_true]
    intro h
    exact hx (by linarith)

theorem levels_ncard_two {α : Type*} (c : α → ℤ) (u : FreeGroup α) {a : α}
    (ha : a ∈ relatorLetters u) (hca : c a ≠ 0) :
    2 ≤ (({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i}
            ∪ {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}) : Set ℤ).ncard := by
  classical
  -- some letter `(a, b)` occurs in the reduced word of `u`
  simp only [relatorLetters] at ha
  obtain ⟨b, hb⟩ := ha
  -- hence some decorated symbol `((a, j), b)` occurs in `decor c 0 (wordOf u)`
  obtain ⟨j, hj⟩ := exists_mem_decor_of_mem c 0 (wordOf u) a b (show (a, b) ∈ wordOf u from hb)
  -- the two level-sets, named
  set A : Set ℤ := {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i} with hAdef
  set B : Set ℤ := {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i} with hBdef
  -- both are finite: they are the sets of values of `coverSrc c`/`coverTgt c` on a finite list
  have hA : A = ↑((decor c 0 (wordOf u)).map (coverSrc c)).toFinset := by
    rw [hAdef]; ext i; simp [List.mem_map]
  have hB : B = ↑((decor c 0 (wordOf u)).map (coverTgt c)).toFinset := by
    rw [hBdef]; ext i; simp [List.mem_map]
  have hfin : (A ∪ B).Finite := by
    rw [hA, hB]
    exact (Finset.finite_toSet _).union (Finset.finite_toSet _)
  -- the two distinct levels of the symbol `((a, j), b)` both lie in `A ∪ B`
  have hsrc : coverSrc c ((a, j), b) ∈ A := by
    rw [hAdef]; exact ⟨((a, j), b), hj, rfl⟩
  have htgt : coverTgt c ((a, j), b) ∈ B := by
    rw [hBdef]; exact ⟨((a, j), b), hj, rfl⟩
  have hsub : ({coverSrc c ((a, j), b), coverTgt c ((a, j), b)} : Set ℤ) ⊆ A ∪ B := by
    intro i hi
    rcases hi with h | h
    · rw [h]; exact Or.inl hsrc
    · rw [h]; exact Or.inr htgt
  calc (2 : ℕ) = ({coverSrc c ((a, j), b), coverTgt c ((a, j), b)} : Set ℤ).ncard :=
        (Set.ncard_pair (coverSrc_ne_coverTgt c a hca j b)).symm
    _ ≤ (A ∪ B).ncard := Set.ncard_le_ncard hsub hfin

end Work.OROneRel
