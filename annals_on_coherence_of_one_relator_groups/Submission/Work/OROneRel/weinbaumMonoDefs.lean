/-
Auxiliary vocabulary for the monochromatic case of Weinbaum's theorem
(`Work.OROneRel.weinbaumAt_of_monochromatic`).

The proof compares the length of a word with the `ℓ¹`-norm of its exponent-sum vector.  For a
relator `r` in which every generator occurs with a single orientation (a *monochromatic* relator),
the two coincide, so that the abelianisation criterion
`Work.OROneRel.expVec_mem_zpowers_of_mem_normalClosure` forces any element of the normal closure of
`r` to be at least as long as `r`.

Everything is phrased with `wordOf` (the reduced word with the *fixed* `Classical.decEq` instance)
so that no statement carries a `DecidableEq α` hypothesis.

The declarations `wordOf` and `mk_wordOf` are *imported* from
`Submission.Work.OROneRel.wordOfDefs`, a leaf module shared with the Magnus-rewriting development.
They were previously duplicated here, verbatim, which made it impossible for any file to import both
this module and `Submission.Work.OROneRel.MagnusGenDefs`; see the "dependency-cone" note in
`NOTES_magnus_step_root_no_eps_zero.md`.
-/
import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.wordOfDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A list of letters is *monochromatic* if no generator occurs in it with both orientations. -/
def MonochromaticList (L : List (α × Bool)) : Prop :=
  ∀ a : α, ¬ ((a, true) ∈ L ∧ (a, false) ∈ L)

/-- `r` is monochromatic iff its reduced word is. -/
theorem monochromaticRelator_iff (r : FreeGroup α) :
    MonochromaticRelator r ↔ MonochromaticList (wordOf r) := by
  constructor <;> intro h a <;> exact h a

/-- The `ℓ¹`-norm of an integer-valued finitely supported function. -/
noncomputable def l1 (f : α →₀ ℤ) : ℕ :=
  f.support.sum fun a => (f a).natAbs

/-- The `ℓ¹`-norm of the exponent-sum vector of `w`. -/
noncomputable def l1Exp (w : FreeGroup α) : ℕ := l1 (expVec w).toAdd

/-- The exponent-sum vector of a word: the sum of `±e_a` over its letters. -/
noncomputable def listExpVec (L : List (α × Bool)) : α →₀ ℤ :=
  (L.map fun p => Finsupp.single p.1 (if p.2 then (1 : ℤ) else -1)).sum

/-- Coordinates of the exponent-sum vector of a word are the signed counts of the letters. -/
theorem listExpVec_apply [DecidableEq α] (a : α) (L : List (α × Bool)) :
    listExpVec L a =
      (L.map fun p => if p.1 = a then (if p.2 then (1 : ℤ) else -1) else 0).sum := by
  induction L with
  | nil => simp [listExpVec]
  | cons p L ih =>
    show (Finsupp.single p.1 (if p.2 then (1 : ℤ) else -1) + listExpVec L) a =
      (List.map (fun p => if p.1 = a then (if p.2 then (1 : ℤ) else -1) else 0) (p :: L)).sum
    rw [Finsupp.add_apply, ih, List.map_cons, List.sum_cons]
    by_cases h : p.1 = a
    · subst h
      simp [Finsupp.single_eq_same]
    · have h' : a ≠ p.1 := fun hh => h hh.symm
      simp [h, Finsupp.single_eq_of_ne h']

/-- The length of `wordOf r` is `relatorNorm r`. -/
theorem relatorNorm_eq_length_wordOf (r : FreeGroup α) :
    relatorNorm r = (wordOf r).length := by
  classical
  simp only [relatorNorm, wordOf, FreeGroup.norm]

/-- A subword of a monochromatic word is monochromatic. -/
theorem monochromatic_of_isSubwordOf {v w : FreeGroup α}
    (hm : MonochromaticRelator w) (h : IsSubwordOf v w) : MonochromaticRelator v := by
  classical
  intro a
  rintro ⟨h1, h2⟩
  obtain ⟨L₁, L₂, hL⟩ := h
  have hmem : ∀ p : α × Bool, p ∈ FreeGroup.toWord v → p ∈ FreeGroup.toWord w := by
    intro p hp
    rw [hL]
    simp only [List.mem_append]
    tauto
  exact hm a ⟨hmem _ h1, hmem _ h2⟩

/-- A nontrivial relator has norm at least one. -/
theorem one_le_relatorNorm_of_ne_one {r : FreeGroup α} (h : r ≠ 1) : 1 ≤ relatorNorm r := by
  classical
  have hnorm : FreeGroup.norm r ≠ 0 := fun h0 => h (FreeGroup.norm_eq_zero.mp h0)
  simp only [relatorNorm]
  omega

end Work.OROneRel
