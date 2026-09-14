import Mathlib
import Submission.Vdw.MultiPrimePerIrr
import Submission.Vdw.CaseIISmallDelta

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The endpoints with the single-prime §4 input

The multi-prime §4 counting (`MultiPrimeCount.multiPrime_count_le`, assembled
in `MultiPrimePerIrr`) turns the §4 input of the whole development into the
*single-prime* statement `FourierPrime.MIndexBound` (the paper's Proposition
`ftgen2`).  This module records the resulting endpoints, replacing the
multi-prime `DequiBound` of `FourierDequi`/`CaseIISmallDelta`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw
noncomputable section

/-- The §4 index-condition input from the single-prime Proposition `ftgen2`. -/
theorem perIrrBound_of_MIndexBound (n : ℕ) (hn : 3 ≤ n) (h : MIndexBound n) :
    ∃ c, 1 ≤ c ∧ PerIrrBound n c :=
  perIrrBound_of_perIrrBoundEv n hn (perIrrBoundEv_of_MIndexBound n hn h)

/-- **The challenge theorem from the single-prime §4 input.** -/
theorem theorem_1_of_MIndex (n : ℕ) (hn : 3 ≤ n) (h : MIndexBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h3 : (fun H : ℕ => ((SubcaseI_P3 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound n hn h
  exact theorem_1_of_perIrr n c hn hc1 hb h2 h3 h4

/-- **The challenge theorem from the single-prime §4 input**, with the
subcase-(i) region discharged. -/
theorem theorem_1_of_MIndex_three (n : ℕ) (hn : 3 ≤ n) (h : MIndexBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)))
    (h4 : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound n hn h
  exact theorem_1_of_perIrr_three n c hn hc1 hb h2 h4

/-- **The challenge theorem in prime degree from the single-prime §4 input.** -/
theorem theorem_1_of_MIndex_one_prime (n : ℕ) (hn : 3 ≤ n) (hprime : Nat.Prime n)
    (h : MIndexBound n)
    (h2 : (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound n hn h
  exact theorem_1_of_perIrr_one_prime n c hn hprime hc1 hb h2

/-- **The challenge theorem in degree 5** from the single-prime §4 input,
Lemke Oliver–Thorne's per-field fibre bound and the exact quintic field count. -/
theorem theorem_1_of_MIndex_caseII_five (h : MIndexBound 5)
    (hLOT : PerFieldFibreBound 5 (by omega : 1 ≤ 5))
    (hSC : FieldCountBound 5 (by omega : 1 ≤ 5) 1) :
    (fun H : ℕ => (E 5 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (5 - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound 5 (by omega) h
  exact theorem_1_of_perIrr_one_prime 5 c (by omega) (by norm_num) hc1 hb
    (subcaseI_P2_isBigO_of_quartic_quintic 5 (by omega) (by omega) hLOT hSC c hc1 hb)

/-- **The challenge theorem for `n ≥ 6`** from the single-prime §4 input,
Schmidt + Lemke Oliver–Thorne (Case II) and Widmer's imprimitive bound. -/
theorem theorem_1_of_MIndex_caseII_eps (n : ℕ) (hn : 6 ≤ n) (h : MIndexBound n)
    (hLOT : PerFieldFibreBound n (by omega : 1 ≤ n))
    (hSC : FieldCountBound n (by omega : 1 ≤ n) (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound n (by omega) h
  exact theorem_1_of_perIrr_three n c (by omega) hc1 hb
    (subcaseI_P2_isBigO_of_schmidt_eps n hn hLOT hSC c hc1 hb)
    (ImprimitiveBad_isBigO_of_widmer n (by omega) hw)

/-- **The challenge theorem in degree 4** from the single-prime §4 input,
conditional on an `O(H^3)` bound for the imprimitive slice. -/
theorem theorem_1_of_MIndex_caseII_four (h : MIndexBound 4)
    (hLOT : PerFieldFibreBound 4 (by omega : 1 ≤ 4))
    (hSC : FieldCountBound 4 (by omega : 1 ≤ 4) 1)
    (hw : (fun H : ℕ => ((ImprimitiveBad 4 H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ))) :
    (fun H : ℕ => (E 4 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (4 - 1) : ℝ)) := by
  obtain ⟨c, hc1, hb⟩ := perIrrBound_of_MIndexBound 4 (by omega) h
  refine theorem_1_of_residual 4 (by omega) ?_ ?_ ?_ hw
  · refine SubcaseI_P1resid_isBigO_of_perD 4
      (max (c * smallConst 4 + 1) (smallConst 4 * (2 * smallConst 4 + 1) ^ 4))
      (by omega) ?_ (perDDiscBound_of_perIrrBound 4 c (by omega) hc1 hb)
    exact le_trans (Nat.le_add_left 1 (c * smallConst 4)) (Nat.le_max_left _ _)
  · exact subcaseI_P2_isBigO_of_quartic_quintic 4 (by omega) (by omega) hLOT hSC c hc1 hb
  · exact SubcaseI_P3_isBigO_of_perIrrBound 4 c (by omega) hc1 hb

/-- **The challenge theorem in degree 3** from the single-prime §4 input,
Lemke Oliver–Thorne's per-field fibre bound and the count of cyclic cubic
fields of bounded discriminant. -/
theorem theorem_1_of_MIndex_degree_three (h : MIndexBound 3)
    (hLOT : PerFieldFibreBound 3 (by omega : 1 ≤ 3))
    (hSC : FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2)) :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_MIndex_one_prime 3 (by omega) (by norm_num) h
    (subcaseI_P2_isBigO_three hLOT hSC)

end
end Submission.Vdw
