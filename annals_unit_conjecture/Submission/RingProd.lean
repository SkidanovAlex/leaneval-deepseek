import Submission.RingMain

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-!
# Product collapses: monomial sets times a single section element

Reference: `sum_mul_single_right` gives
`(∑ s∈S, single s 1) * single t 1 = ∑ s∈S, single (s*t) 1`, and
`sum_single_map_eq_sum_single (P) f Q hcover huniq` collapses a sum of images
onto a set; the hypotheses are decidable (`native_decide`).

`HW.A = m 0 0 0 qA`, `HW.B = m 0 0 0 qB`, `HW.A * HW.B = m 0 0 0 qAB`
(verify by `decide` / `native_decide`).
-/

lemma qA_prod :
    (∑ q ∈ Qq, single q (1 : ZMod 2)) * single (m 0 0 0 qA) (1 : ZMod 2)
      = ∑ q ∈ PqA, single q (1 : ZMod 2) := by
  rw [sum_mul_single_right]
  refine sum_single_map_eq_sum_single Qq (fun s => s * m 0 0 0 qA) PqA ?_ ?_
  · intro p hp
    simp [Qq] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp [PqA] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide

lemma rB_prod :
    (∑ q ∈ Qr, single q (1 : ZMod 2)) * single (m 0 0 0 qB) (1 : ZMod 2)
      = ∑ q ∈ PrB, single q (1 : ZMod 2) := by
  rw [sum_mul_single_right]
  refine sum_single_map_eq_sum_single Qr (fun s => s * m 0 0 0 qB) PrB ?_ ?_
  · intro p hp
    simp [Qr] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp [PrB] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> decide

lemma sAB_prod :
    (∑ q ∈ Qs, single q (1 : ZMod 2)) * single (m 0 0 0 qAB) (1 : ZMod 2)
      = ∑ q ∈ PsAB, single q (1 : ZMod 2) := by
  rw [sum_mul_single_right]
  refine sum_single_map_eq_sum_single Qs (fun s => s * m 0 0 0 qAB) PsAB ?_ ?_
  · intro p hp
    simp [Qs] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro q hq
    simp [PsAB] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide

end Submission
