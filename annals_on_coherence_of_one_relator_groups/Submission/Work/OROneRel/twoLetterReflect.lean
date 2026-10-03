/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The reflection symmetry of the two-letter Freiheitssatz

The two-letter Freiheitssatz with the weight `-tlW p q` is the reflection of the one with the weight
`tlW p q`: the map `(x, i) ↦ (x, -i)` of the level graph of `tlW p q` onto the level graph of
`-tlW p q` carries the walk of `u` at level `0` to the walk of `u` at level `0`, the window
`[lo, hi]` to `[-hi, -lo]` and the loop classes to the loop classes.

This file records that reduction in the form needed by the target: the conclusion for the weight
`tlWneg p q = -tlW p q` (for the gauge `Wt`) follows from the conclusion for the weight `tlW p q` for
the reflected gauge `fun j => Wt (-j)` (with the reflected window).
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetterWindow_neg

namespace Work.OROneRel

universe u

/-- The reflection carries loop classes to loop classes. -/
theorem coverClassAt_reflect (Wt : ℤ → FreeGroup (Fin 2)) (c : Fin 2 → ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : Fin 2 × ℤ) :
    coverClassAt (fun j => Wt (-j)) (fun a => -c a) e =
      coverClassAt Wt c (e.1, -e.2) := by
  rcases e with ⟨x, i⟩
  simp only [coverClassAt, gaugeMap_of]
  congr 2
  ring_nf

/-- The window reflects. -/
theorem mem_winE_reflect (c : Fin 2 → ℤ) {lo hi : ℤ} {e : Fin 2 × ℤ} :
    e ∈ winE (fun a => -c a) (-hi) (-lo) ↔ (e.1, -e.2) ∈ winE c lo hi := by
  rcases e with ⟨x, i⟩
  simp only [mem_winE]
  constructor <;> intro h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Work.OROneRel
