import Mathlib
import Submission.Work.SG.SGprelude

/-!
# `sgClose_map_fst`: the matrix projection of the affine closure

`sgClose gens k acc` is the (`k`-fold) affine closure of `gens` started from `acc`; it is the
list of affine pairs `(A, a)`, where `A` is a flat `3 × 3` matrix (row major, `List ℤ`) and `a`
a translation (`List ℚ`), built with the multiplication

`s (A, a) * (B, b) = (A * B, a + A b)`   (`sgMulPair`, translations reduced mod `ℤ³`).

`mClose gensM k accM` is the analogous closure on the *matrix* side (`SGprelude`), using
`m9mul` for the flat matrix product and starting from `accM`.

The point of this file is that projecting an affine element onto its matrix commutes with the
closure, at the level of *membership*:

* `sgClose_map_fst`: `l ∈ (sgClose gens k acc).map (·.1) ↔ l ∈ mClose (gens.map (·.1)) k
  (acc.map (·.1))`.

The two closures do **not** commute as `List`-equalities: the deduplication step of `sgClose`
removes duplicate *pairs*, while the one of `mClose` removes duplicate *matrices*, so lists may
differ (e.g. two generators with the same matrix and different translations).  Membership,
however, is all that the one step can change, and that is what is proved here.

The mechanism is a predicate `SameMem L M` ("`L` and `M` have the same elements"), shown to be
preserved by one closure round (`mF`) and hence by all of them (`mClose`), together with the
observation that one round of `sgClose`, projected to the matrix side, has the same elements as
one round of `mClose` applied to the projected accumulator.
-/

namespace Work.SG

/-- `L` and `M` have the same members.  (This is the weakest hypothesis under which a list can
be replaced by another one inside a membership statement.) -/
private def SameMem {α : Type*} (L M : List α) : Prop := ∀ x, x ∈ L ↔ x ∈ M

/-- One round of `sgClose`, projected to the matrices, has the same members as one round of
`mClose` started from the projected accumulator.

Unwinding the definitions, both sides describe, elementwise,
`{a | a ∈ acc} ∪ {A * G | (A, a) ∈ acc, G ∈ gens}` (with `gens` projected to `gens.map (·.1)`),
so the only content is bookkeeping of `List.mem` over `map`, `flatMap`, `++` and `dedup`. -/
private theorem sameMem_step (gens acc : List (List ℤ × List ℚ)) :
    SameMem ((acc ++ acc.flatMap fun a => gens.map fun g => sgMulPair a g).dedup |>.map (·.1))
      (mF (gens.map (·.1)) (acc.map (·.1))) := by
  intro x
  simp only [mF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map, sgMulPair]
  constructor
  · rintro ⟨a, (ha | ⟨a1, ha1, g, hg, rfl⟩), hfst⟩
    · exact Or.inl ⟨a, ha, hfst⟩
    · exact Or.inr ⟨a1.1, ⟨a1, ha1, rfl⟩, g.1, ⟨g, hg, rfl⟩, hfst⟩
  · rintro (⟨a, ha, hfst⟩ | ⟨b, ⟨a1, ha1, he1⟩, g1, ⟨g, hg, he2⟩, hmul⟩)
    · exact ⟨a, Or.inl ha, hfst⟩
    · refine ⟨sgMulPair a1 g, Or.inr ⟨a1, ha1, g, hg, rfl⟩, ?_⟩
      show m9mul a1.1 g.1 = x
      rw [he1, he2]; exact hmul

/-- One closure round on the matrix side preserves the members. -/
private theorem sameMem_mF {gM L M : List (List ℤ)} (h : SameMem L M) :
    SameMem (mF gM L) (mF gM M) := by
  intro x
  simp only [mF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (hx | ⟨a, ha, g, hg, rfl⟩)
    · exact Or.inl ((h x).mp hx)
    · exact Or.inr ⟨a, (h a).mp ha, g, hg, rfl⟩
  · rintro (hx | ⟨a, ha, g, hg, rfl⟩)
    · exact Or.inl ((h x).mpr hx)
    · exact Or.inr ⟨a, (h a).mpr ha, g, hg, rfl⟩

/-- Every closure round on the matrix side preserves the members. -/
private theorem sameMem_mClose {gM : List (List ℤ)} (k : ℕ) {L M : List (List ℤ)}
    (h : SameMem L M) : SameMem (mClose gM k L) (mClose gM k M) := by
  induction k generalizing L M with
  | zero => exact h
  | succ k ih => exact ih (sameMem_mF h)

/-- Membership version of the statement, with `gens` and `acc` explicit so that the induction
can generalise the accumulator. -/
private theorem sgClose_map_fst_aux (gens acc : List (List ℤ × List ℚ)) (k : ℕ) (l : List ℤ) :
    l ∈ (sgClose gens k acc).map (·.1) ↔
      l ∈ mClose (gens.map (·.1)) k (acc.map (·.1)) := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    have hstep : sgClose gens (k+1) acc =
        sgClose gens k ((acc ++ acc.flatMap fun a => gens.map fun g => sgMulPair a g).dedup) := rfl
    have hstep2 : mClose (gens.map (·.1)) (k+1) (acc.map (·.1)) =
        mClose (gens.map (·.1)) k (mF (gens.map (·.1)) (acc.map (·.1))) := rfl
    rw [hstep, ih, hstep2]
    exact sameMem_mClose k (sameMem_step gens acc) l

/-- The image of the affine closure under `(·.1)` is the matrix closure. -/
theorem sgClose_map_fst {gens : List (List ℤ × List ℚ)} {acc : List (List ℤ × List ℚ)} (k : ℕ)
    (l : List ℤ) :
    l ∈ (sgClose gens k acc).map (·.1) ↔ l ∈ mClose (gens.map (·.1)) k (acc.map (·.1)) :=
  sgClose_map_fst_aux gens acc k l

end Work.SG
