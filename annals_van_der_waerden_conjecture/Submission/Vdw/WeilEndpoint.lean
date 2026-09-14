import Mathlib
import Submission.Vdw.FourierTranslate
import Submission.Vdw.MIndexEndpoint

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The endpoints with the Weil-bound input

`FourierTranslate.mIndexBound_of_weilPolyBound` shows that the single-prime §4
input `MIndexBound n` (the paper's Proposition `ftgen2`) follows from the
*classical Weil bound* for polynomial exponential sums over `F_p`
(`FourierTranslate.WeilPolyBound`).  This module re-states the endpoints of
`MIndexEndpoint` with `WeilPolyBound` as the input, so that the challenge
theorem is seen to depend on the Weil bound rather than on any splitting-type
analysis.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- The §4 index-condition input from the Weil bound for exponential sums. -/
theorem perIrrBound_of_weilPolyBound (n : ℕ) (hn : 3 ≤ n) (h : WeilPolyBound n) :
    ∃ c, 1 ≤ c ∧ PerIrrBound n c :=
  perIrrBound_of_MIndexBound n hn (mIndexBound_of_weilPolyBound n (by omega) h)

/-- **The challenge theorem from the Weil bound.** -/
theorem theorem_1_of_weilPoly (n : ℕ) (hn : 3 ≤ n) (h : WeilPolyBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_MIndex n hn (mIndexBound_of_weilPolyBound n (by omega) h) h2 h3 h4

/-- **The challenge theorem from the Weil bound**, subcase (i) discharged. -/
theorem theorem_1_of_weilPoly_three (n : ℕ) (hn : 3 ≤ n) (h : WeilPolyBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_MIndex_three n hn (mIndexBound_of_weilPolyBound n (by omega) h) h2 h4

/-- **The challenge theorem in prime degree from the Weil bound.** -/
theorem theorem_1_of_weilPoly_one_prime (n : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n)
    (h : WeilPolyBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_MIndex_one_prime n hn hprime (mIndexBound_of_weilPolyBound n (by omega) h) h2

/-- **The challenge theorem in degree 5 from the Weil bound.** -/
theorem theorem_1_of_weilPoly_caseII_five (h : WeilPolyBound 5)
    (hLOT : PerFieldFibreBound 5 (by omega : 1 ≤ 5))
    (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) :=
  theorem_1_of_MIndex_caseII_five (mIndexBound_of_weilPolyBound 5 (by omega) h) hLOT hSC

/-- **The challenge theorem for `n ≥ 6` from the Weil bound.** -/
theorem theorem_1_of_weilPoly_caseII_eps (n : ℕ) (hn : 6 ≤ n) (h : WeilPolyBound n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_MIndex_caseII_eps n hn (mIndexBound_of_weilPolyBound n (by omega) h)
    hLOT hSC hw

/-- **The challenge theorem in degree 4 from the Weil bound.** -/
theorem theorem_1_of_weilPoly_caseII_four (h : WeilPolyBound 4)
    (hLOT : PerFieldFibreBound 4 (by omega : 1 ≤ 4))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1)
    (hw : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ))) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) :=
  theorem_1_of_MIndex_caseII_four (mIndexBound_of_weilPolyBound 4 (by omega) h) hLOT hSC hw

/-- **The challenge theorem in degree 3 from the Weil bound.** -/
theorem theorem_1_of_weilPoly_degree_three (h : WeilPolyBound 3)
    (hLOT : PerFieldFibreBound 3 (by omega : 1 ≤ 3))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_MIndex_degree_three (mIndexBound_of_weilPolyBound 3 (by omega) h) hLOT hSC

end
end Submission.Vdw
