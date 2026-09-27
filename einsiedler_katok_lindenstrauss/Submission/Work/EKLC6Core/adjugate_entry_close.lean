import Mathlib

namespace Work.EKLC6Core

set_option maxHeartbeats 1000000 in
/-- If the entries of `A : Matrix (Fin 3) (Fin 3) ℝ` are within `ε` of the identity,
then the entries of the adjugate `A.adjugate` are within `2ε + 2ε²` of the identity.
(This is a quantitative version of `adj(I) = I`, using the explicit cofactor
expansion for 3×3 matrices.) -/
lemma adjugate_entry_close {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ ε) :
    ∀ i j, |A.adjugate i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 * ε + 2 * ε ^ 2 := by
  -- Two-sided bounds on the deviations `A i j - δ_{ij}` of each entry from the identity.
  have h00 := abs_le.mp (by simpa using hA 0 0)
  have h01 := abs_le.mp (by simpa using hA 0 1)
  have h02 := abs_le.mp (by simpa using hA 0 2)
  have h10 := abs_le.mp (by simpa using hA 1 0)
  have h11 := abs_le.mp (by simpa using hA 1 1)
  have h12 := abs_le.mp (by simpa using hA 1 2)
  have h20 := abs_le.mp (by simpa using hA 2 0)
  have h21 := abs_le.mp (by simpa using hA 2 1)
  have h22 := abs_le.mp (by simpa using hA 2 2)
  intro i j
  -- Expand the adjugate into its nine cofactor entries and check each one.
  fin_cases i <;> fin_cases j <;>
    · rw [Matrix.adjugate_fin_three]
      simp
      rw [abs_le]
      constructor <;>
        nlinarith [h00.1, h00.2, h01.1, h01.2, h02.1, h02.2, h10.1, h10.2,
          h11.1, h11.2, h12.1, h12.2, h20.1, h20.2, h21.1, h21.2, h22.1, h22.2]

end Work.EKLC6Core
