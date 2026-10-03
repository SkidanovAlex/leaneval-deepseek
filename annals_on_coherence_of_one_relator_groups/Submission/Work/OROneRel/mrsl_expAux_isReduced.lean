import Mathlib
import Submission.Work.OROneRel.mrslExp

/-!
# The expansion of a reduced decorated word is reduced

For a decorated word `D : List (({x // x ≠ t} × ℤ) × Bool)` the *expansion* `expAux t a D` puts
back the `t`-frame: the decorated letter `((x, i), b)` contributes the `t`-run
`runLetters t (i - a)` — where `a` is the decoration of the previous letter — followed by the
letter `(x, b)`.

The expansion is reduced as soon as the decorated word is.  Two consecutive letters of `D` with
different decorations are separated by a nonempty `t`-run, and two consecutive letters with the
*same* decoration are forced to be non-cancelling by `IsReduced D`.  This file proves that
(`mrsl_expAux_isReduced`), together with the elementary facts about `t`-runs and about the head of
an expansion that the induction on `D` needs.
-/

namespace Work.OROneRel

universe u

variable {β : Type u}

/-- A `t`-run `runLetters t n` is reduced: all of its letters are equal. -/
private lemma isReduced_runLetters (t : β) (n : ℤ) : FreeGroup.IsReduced (runLetters t n) := by
  rw [runLetters]
  exact List.isChain_replicate_of_rel _ (fun _ => rfl)

/-- The head of a `t`-run. -/
private lemma head?_runLetters (t : β) (n : ℤ) :
    (runLetters t n).head? = if n = 0 then none else some (t, decide (0 < n)) := by
  rw [runLetters, List.head?_replicate]
  by_cases h : n = 0
  · rw [if_pos (Int.natAbs_eq_zero.mpr h), if_pos h]
  · rw [if_neg (by simpa [Int.natAbs_eq_zero] using h), if_neg h]

/-- The last element of a `t`-run. -/
private lemma getLast?_runLetters (t : β) (n : ℤ) :
    (runLetters t n).getLast? = if n = 0 then none else some (t, decide (0 < n)) := by
  rw [runLetters, List.getLast?_replicate]
  by_cases h : n = 0
  · rw [if_pos (Int.natAbs_eq_zero.mpr h), if_pos h]
  · rw [if_neg (by simpa [Int.natAbs_eq_zero] using h), if_neg h]

/-- Every element occurring as the last letter of a `t`-run has first component `t`. -/
private lemma getLast?_runLetters_mem (t : β) (n : ℤ) {y : β × Bool}
    (hy : y ∈ (runLetters t n).getLast?) : y.1 = t := by
  rw [getLast?_runLetters] at hy
  by_cases h : n = 0
  · rw [if_pos h] at hy; exact absurd hy (by simp)
  · rw [if_neg h, Option.mem_some_iff] at hy; subst hy; rfl

/-- The head of the expansion of a nonempty decorated word: it is the first letter of the decorated
word when the leading `t`-run is empty, and the letter `t` otherwise. -/
private lemma head?_expAux_cons (t : β) (a i : ℤ) (c : {x : β // x ≠ t}) (b : Bool)
    (rest : List (({x : β // x ≠ t} × ℤ) × Bool)) :
    (expAux t a (((c,i),b) :: rest)).head?
      = if i - a = 0 then some (c.1, b) else some (t, decide (0 < i - a)) := by
  rw [expAux_cons, List.head?_append, head?_runLetters, List.head?_cons]
  by_cases h : i - a = 0
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- The head of the expansion of the tail of a reduced decorated word does not cancel with the
letter `p` preceding it: either the head is `t`, or it is the next decorated letter of `D` and the
reducedness of `D` applies. -/
private lemma expAux_head_rel (t : β) (p : ({x : β // x ≠ t} × ℤ) × Bool)
    (rest : List (({x : β // x ≠ t} × ℤ) × Bool))
    (hD : FreeGroup.IsReduced (p :: rest)) :
    ∀ y ∈ (expAux t p.1.2 rest).head?, (p.1.1.1 = y.1 → p.2 = y.2) := by
  cases rest with
  | nil =>
    intro y hy
    rw [expAux_nil] at hy
    have h := runLetters_mem (List.mem_of_mem_head? hy)
    rw [h]
    intro hh
    exact absurd hh p.1.1.2
  | cons q rest' =>
    have hrel : p.1 = q.1 → p.2 = q.2 := (FreeGroup.isReduced_cons_cons.mp hD).1
    obtain ⟨⟨c', i'⟩, b'⟩ := q
    intro y hy
    by_cases h : i' - p.1.2 = 0
    · have hnil : runLetters t (i' - p.1.2) = [] := by rw [h, runLetters_zero]
      rw [expAux_cons, hnil, List.nil_append, List.head?_cons] at hy
      have hy' : y = (c'.1, b') := (Option.mem_some_iff.mp hy).symm
      rw [hy']
      intro hp
      have hi : p.1.2 = i' := by omega
      have hc : p.1.1 = c' := Subtype.ext hp
      exact hrel (Prod.ext hc hi)
    · have hne : runLetters t (i' - p.1.2) ≠ [] := by
        rw [List.ne_nil_iff_length_pos, runLetters, List.length_replicate]
        exact Int.natAbs_pos.mpr h
      rw [expAux_cons, List.head?_append_of_ne_nil _ hne, head?_runLetters, if_neg h] at hy
      have hy' : y = (t, decide (0 < i' - p.1.2)) := (Option.mem_some_iff.mp hy).symm
      rw [hy']
      intro hh
      exact absurd hh p.1.1.2

/-- The expansion of a reduced decorated word is reduced. -/
private theorem expAux_isReduced_aux (t : β) :
    ∀ (D : List (({x : β // x ≠ t} × ℤ) × Bool)) (a : ℤ),
      FreeGroup.IsReduced D → FreeGroup.IsReduced (expAux t a D) := by
  intro D
  induction D with
  | nil =>
    intro a _
    rw [expAux_nil]
    exact isReduced_runLetters t (-a)
  | cons p rest ih =>
    intro a hD
    obtain ⟨⟨c, i⟩, b⟩ := p
    rw [expAux_cons]
    have hrest : FreeGroup.IsReduced rest := (List.isChain_cons.mp hD).2
    refine List.IsChain.append (isReduced_runLetters t (i - a)) ?_ ?_
    · refine List.isChain_cons.mpr ⟨?_, ih i hrest⟩
      exact expAux_head_rel t ((c, i), b) rest hD
    · intro x hx y hy
      rw [List.head?_cons] at hy
      have hy' : y = (c.1, b) := (Option.mem_some_iff.mp hy).symm
      rw [hy']
      rw [getLast?_runLetters_mem t (i - a) hx]
      intro hh
      exact absurd hh.symm c.2

theorem mrsl_expAux_isReduced {β : Type u} (t : β) (a : ℤ) {D : List (({x : β // x ≠ t} × ℤ) × Bool)}
    (hD : FreeGroup.IsReduced D) : FreeGroup.IsReduced (Work.OROneRel.expAux t a D) :=
  expAux_isReduced_aux t D a hD

end Work.OROneRel
