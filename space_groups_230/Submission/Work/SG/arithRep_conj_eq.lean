import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.arithDefs
import Submission.Work.SG.trPow_card_conj
import Submission.Work.SG.fixPow_conj

/-!
# The 73 arithmetic-class representatives are pairwise non-conjugate in `GL₃(ℤ)`

`arithRep j` is proved (in `Submission.Work.SG.arithDefs`) to be *exactly* the explicit finite
group `finSet j` of integral matrices listed there, and the invariant
`invOf` (cardinality, power sums of traces, and power sums of the numbers of fixed vectors of the
actions on `(ℤ/2)³`, `(ℤ/3)³`, `(ℤ/4)³`) is proved there to separate the 73 classes.  Here we
assemble these two facts with the conjugation invariance of `invOf` — the trace/cardinality part
is `Work.SG.trPow_card_conj` (`Submission/Work/SG/trPow_card_conj.lean`) and the fixed-vector part
is `Work.SG.fixPow_conj` (`Submission/Work/SG/fixPow_conj.lean`).
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped BigOperators

/-- `invOf` is invariant under conjugation by a unimodular integer matrix. -/
theorem invOf_conj {P P' : Finset IMat} {U : IMat} (hU : IsUnit U.det)
    (h : ∀ A, A ∈ P' ↔ ∃ B ∈ P, A = U * B * U⁻¹) : invOf P = invOf P' := by
  obtain ⟨hc, h1⟩ := trPow_card_conj (P := P) (P' := P') hU h 1
  obtain ⟨_, h2⟩ := trPow_card_conj (P := P) (P' := P') hU h 2
  obtain ⟨_, h3⟩ := trPow_card_conj (P := P) (P' := P') hU h 3
  have f1 : fixPow 2 P 1 = fixPow 2 P' 1 := (fixPow_conj (P := P) (P' := P') hU h 2 1).symm
  have f2 : fixPow 2 P 2 = fixPow 2 P' 2 := (fixPow_conj (P := P) (P' := P') hU h 2 2).symm
  have f3 : fixPow 3 P 1 = fixPow 3 P' 1 := (fixPow_conj (P := P) (P' := P') hU h 3 1).symm
  have f4 : fixPow 3 P 2 = fixPow 3 P' 2 := (fixPow_conj (P := P) (P' := P') hU h 3 2).symm
  have f5 : fixPow 4 P 1 = fixPow 4 P' 1 := (fixPow_conj (P := P) (P' := P') hU h 4 1).symm
  have f6 : fixPow 4 P 2 = fixPow 4 P' 2 := (fixPow_conj (P := P) (P' := P') hU h 4 2).symm
  simp only [invOf, hc.symm, h1.symm, h2.symm, h3.symm, f1, f2, f3, f4, f5, f6]

/-- The 73 arithmetic-class representatives are pairwise non-conjugate in `GL₃(ℤ)`. -/
theorem arithRep_conj_eq {j j' : Fin 73} {U : IMat} (hU : IsUnit U.det)
    (h : ∀ A, A ∈ arithRep j' ↔ ∃ B ∈ arithRep j, A = U * B * U⁻¹) : j = j' := by
  have h' : ∀ A, A ∈ finSet j' ↔ ∃ B ∈ finSet j, A = U * B * U⁻¹ := by
    intro A
    simp only [← mem_arithRep j' A, h A, mem_arithRep j]
  exact invOf_injective (invOf_conj hU h')

end Work.SG
