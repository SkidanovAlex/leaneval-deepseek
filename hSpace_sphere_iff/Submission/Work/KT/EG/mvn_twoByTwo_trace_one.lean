import Mathlib
import Submission.Work.KT.Defs

open Matrix

namespace Work.KT.EG

/-- A `2 × 2` complex matrix with trace `1` and vanishing determinant (written multiplicatively as
`P 0 0 * P 1 1 = P 0 1 * P 1 0`) is Murray–von Neumann equivalent to the `1 × 1` identity matrix.
These are exactly the relations satisfied at every point of `S²` by the Hopf projection
(`Work.KT.Fund.hopf_trace_det`), so the claim says that the Hopf bundle at every point is trivial.

`Work.KT.Mat.MvN ⟨2,P⟩ (Work.KT.Mat.one ℂ 1)` unfolds to
`∃ a : Matrix (Fin 1) (Fin 2) ℂ, ∃ b : Matrix (Fin 2) (Fin 1) ℂ, b * a = P ∧ a * b = 1`.

Explicit witnesses (`P * P = P` follows from the hypotheses by
`Work.KT.Fund.twoByTwo_idem_of_trace_det`, but is not needed for either case):

* if `P 0 0 ≠ 0`, take the row `a = !![1, P 0 1 / P 0 0]` and the column `b = !![P 0 0; P 1 0]`:
  `(b * a) 0 0 = P 0 0`, `(b * a) 0 1 = P 0 1`, `(b * a) 1 0 = P 1 0`,
  `(b * a) 1 1 = P 1 0 * (P 0 1 / P 0 0) = P 1 1` (by `hdet` and `P 0 0 ≠ 0`), and
  `a * b = P 0 0 + (P 0 1 / P 0 0) * P 1 0 = P 0 0 + P 1 1 = 1` (by `hdet`, `htr`);
* if `P 0 0 = 0`, take the row `a = !![P 1 0, 1]` and the column `b = !![P 0 1; 1]`:
  `b * a = !![P 0 1 * P 1 0, P 0 1; P 1 0, 1] = P` (as `P 0 1 * P 1 0 = 0` by `hdet` and
  `P 1 1 = 1` by `htr`), and `a * b = P 1 0 * P 0 1 + 1 = 1`. -/
theorem mvn_twoByTwo_trace_one (P : Matrix (Fin 2) (Fin 2) ℂ)
    (htr : P 0 0 + P 1 1 = 1) (hdet : P 0 0 * P 1 1 = P 0 1 * P 1 0) :
    Work.KT.Mat.MvN (⟨2, P⟩ : Work.KT.Mat ℂ) (Work.KT.Mat.one ℂ 1) := by
  by_cases h00 : P 0 0 = 0
  · -- Case `P 0 0 = 0`: the row `![P 1 0, 1]` and the column `![P 0 1; 1]`.
    have h11 : P 1 1 = 1 := by rw [h00, zero_add] at htr; exact htr
    have hz : P 0 1 * P 1 0 = 0 := by rw [h00, zero_mul] at hdet; exact hdet.symm
    have hz' : P 1 0 * P 0 1 = 0 := by rw [mul_comm]; exact hz
    refine ⟨(!![P 1 0, 1] : Matrix (Fin 1) (Fin 2) ℂ),
      (!![P 0 1; 1] : Matrix (Fin 2) (Fin 1) ℂ), ?_, ?_⟩
    · show (!![P 0 1; 1] : Matrix (Fin 2) (Fin 1) ℂ) *
        (!![P 1 0, 1] : Matrix (Fin 1) (Fin 2) ℂ) = P
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, h00, h11, hz]
    · show (!![P 1 0, 1] : Matrix (Fin 1) (Fin 2) ℂ) *
        (!![P 0 1; 1] : Matrix (Fin 2) (Fin 1) ℂ) = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, hz']
  · -- Case `P 0 0 ≠ 0`: the row `![1, P 0 1 / P 0 0]` and the column `![P 0 0; P 1 0]`.
    refine ⟨(!![1, P 0 1 / P 0 0] : Matrix (Fin 1) (Fin 2) ℂ),
      (!![P 0 0; P 1 0] : Matrix (Fin 2) (Fin 1) ℂ), ?_, ?_⟩
    · show (!![P 0 0; P 1 0] : Matrix (Fin 2) (Fin 1) ℂ) *
        (!![1, P 0 1 / P 0 0] : Matrix (Fin 1) (Fin 2) ℂ) = P
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
      · exact mul_div_cancel₀ (P 0 1) h00
      · rw [← mul_div_assoc, mul_comm (P 1 0) (P 0 1), ← hdet]
        exact mul_div_cancel_left₀ (P 1 1) h00
    · show (!![1, P 0 1 / P 0 0] : Matrix (Fin 1) (Fin 2) ℂ) *
        (!![P 0 0; P 1 0] : Matrix (Fin 2) (Fin 1) ℂ) = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
      · rw [div_mul_eq_mul_div, ← hdet]
        rw [mul_div_cancel_left₀ _ h00, htr]

end Work.KT.EG
