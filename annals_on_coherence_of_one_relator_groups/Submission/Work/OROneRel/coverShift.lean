/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The level shift of the decorated walk

`decor c i L` is the walk of the word `L` started at level `i`, so it is the `i`-shift of the walk
`decor c 0 L` started at level `0`: the `k`-th decorated letter has the same label and sign, and its
level is raised by `i`.  This is the combinatorial form of the fact that the `2`-cells of the
`ℤ`-cover of a one-relator presentation are the translates of one another, which is what Linton's
`Z`-domain conditions (2) and (3) (arXiv 2202.11324) quantify over.
-/
import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.GaugeDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The `i`-shift of a decorated letter: the same edge of the cover, read at the level raised by
`i`. -/
def coverShift (i : ℤ) (p : (α × ℤ) × Bool) : (α × ℤ) × Bool := ((p.1.1, p.1.2 + i), p.2)

@[simp] theorem coverShift_fst (i : ℤ) (p : (α × ℤ) × Bool) :
    (coverShift i p).1 = (p.1.1, p.1.2 + i) := rfl

@[simp] theorem coverShift_snd (i : ℤ) (p : (α × ℤ) × Bool) : (coverShift i p).2 = p.2 := rfl

theorem coverShift_zero (p : (α × ℤ) × Bool) : coverShift 0 p = p := by
  obtain ⟨⟨a, j⟩, b⟩ := p
  simp [coverShift]

theorem coverShift_add (i j : ℤ) (p : (α × ℤ) × Bool) :
    coverShift i (coverShift j p) = coverShift (j + i) p := by
  obtain ⟨⟨a, k⟩, b⟩ := p
  simp only [coverShift]
  rw [show k + j + i = k + (j + i) from by ring]

theorem coverShift_injective (i : ℤ) : Function.Injective (coverShift (α := α) i) := by
  rintro ⟨⟨a, j⟩, b⟩ ⟨⟨a', j'⟩, b'⟩ h
  simp only [coverShift, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst h1
  subst h3
  have hj : j = j' := by omega
  subst hj
  rfl

/-- **The decorated walk is the level shift of the walk started at level `j`.** -/
theorem decor_shift_add (c : α → ℤ) (i j : ℤ) (L : List (α × Bool)) :
    decor c (j + i) L = (decor c j L).map (coverShift i) := by
  induction L generalizing j with
  | nil => simp [decor]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [show decor c j ((a, false) :: L) = ((a, j - c a), false) :: decor c (j - c a) L
          from rfl,
        List.map_cons, ← ih (j - c a),
        show decor c (j + i) ((a, false) :: L) = ((a, (j + i) - c a), false) ::
          decor c ((j + i) - c a) L from rfl,
        show (j + i) - c a = (j - c a) + i from by ring]
      rfl
    · rw [show decor c j ((a, true) :: L) = ((a, j), true) :: decor c (j + c a) L from rfl,
        List.map_cons, ← ih (j + c a),
        show decor c (j + i) ((a, true) :: L) = ((a, j + i), true) ::
          decor c ((j + i) + c a) L from rfl,
        show (j + i) + c a = (j + c a) + i from by ring]
      rfl

/-- **The decorated walk is the level shift of the walk at level `0`.** -/
theorem decor_shift (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    decor c i L = (decor c 0 L).map (coverShift i) := by
  have h := decor_shift_add c i 0 L
  simpa using h

/-- The source level of a shifted decorated letter is the shifted source level. -/
theorem coverSrc_shift (c : α → ℤ) (i : ℤ) (p : (α × ℤ) × Bool) :
    coverSrc c (coverShift i p) = coverSrc c p + i := by
  obtain ⟨⟨a, j⟩, b⟩ := p
  cases b <;> simp only [coverShift, coverSrc, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The target level of a shifted decorated letter is the shifted target level. -/
theorem coverTgt_shift (c : α → ℤ) (i : ℤ) (p : (α × ℤ) × Bool) :
    coverTgt c (coverShift i p) = coverTgt c p + i := by
  obtain ⟨⟨a, j⟩, b⟩ := p
  cases b <;> simp only [coverShift, coverTgt, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The letter read at a shifted decorated letter is the same. -/
theorem coverLetter_shift (i : ℤ) (p : (α × ℤ) × Bool) :
    coverLetter (coverShift i p) = coverLetter p := by
  obtain ⟨⟨a, j⟩, b⟩ := p
  cases b <;> simp only [coverShift, coverLetter, Bool.false_eq_true, ↓reduceIte]

end Work.OROneRel
