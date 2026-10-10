import Submission.Work.MotAS.ASRul.Matrices
import Submission.Work.MotAS.ASData
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS ruling matrix and the AS Klein-matrix contraction (auxiliary file)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace Work.MotAS

open Matrix

/-- **The AS ruling matrix**: the coefficient matrix of the linear-in-`y` system
`kleinMAS a b g y *ᵥ c`, i.e. `AmatAS2 c *ᵥ y = kleinMAS y *ᵥ c`.  It is the AS analogue of the
T-route's `Work.MotK.TwCensus.AmatP`.  (This is the corrected version of
`Work.MotAS.ASRul.AmatAS`: the lower triangle of the latter does not satisfy the contraction
identity.) -/
noncomputable def AmatAS2 {R : Type*} [CommRing R] (a b g : R) (c : Fin 5 → R) :
    Matrix (Fin 5) (Fin 5) R :=
  !![      0, 2 * a * (c 4) - b * (c 4), -a * (c 3) - 2 * b * (c 3), a * (c 2) + 2 * a * (c 4) + 2 * b * (c 2) + b * (c 4), -2 * a * (c 1) - 2 * a * (c 3) + b * (c 1) - b * (c 3);
      -a * (c 4) - 2 * b * (c 4), a * (c 3) + 2 * b * (c 3), -2 * a * (c 2) - a * (c 4) + b * (c 2) + 2 * b * (c 4), -a * (c 3) + 2 * b * (c 3), 2 * a * (c 0) + 2 * a * (c 2) + a * (c 4) - b * (c 0) + b * (c 2) + 2 * b * (c 4);
      -2 * a * (c 3) + b * (c 3), -2 * a * (c 4) - b * (c 4), 2 * a * (c 1) - a * (c 3) - b * (c 1) + 2 * b * (c 3), -a * (c 0) + 2 * a * (c 4) - 2 * b * (c 0) - b * (c 4), -2 * a * (c 1) + a * (c 3) + a * (c 4) * g - b * (c 1) + 2 * b * (c 3) + 2 * b * (c 4) * g;
      2 * a * (c 2) + a * (c 4) - b * (c 2) - 2 * b * (c 4), -a * (c 1) - 2 * b * (c 1), a * (c 0) + a * (c 2) + 2 * a * (c 4) + 2 * b * (c 0) - 2 * b * (c 2) - b * (c 4), a * (c 1) - 2 * a * (c 4) * g - 2 * b * (c 1) + b * (c 4) * g, 2 * a * (c 0) - a * (c 2) - 2 * a * (c 4) + b * (c 0) - 2 * b * (c 2) - b * (c 4);
      a * (c 1) - a * (c 3) + 2 * b * (c 1) + 2 * b * (c 3), -2 * a * (c 0) + 2 * a * (c 2) + b * (c 0) + b * (c 2), a * (c 1) - 2 * a * (c 3) - 2 * b * (c 1) + b * (c 3), -2 * a * (c 0) - 2 * a * (c 2) + 2 * a * (c 3) * g - b * (c 0) + b * (c 2) - b * (c 3) * g, -a * (c 1) - a * (c 2) * g + 2 * a * (c 3) - 2 * b * (c 1) - 2 * b * (c 2) * g + b * (c 3)]

/-- **The AS Klein-matrix contraction**: `kleinMAS a b g y *ᵥ kleinPAS a b g y = 0` in
characteristic `5`. -/
theorem kleinMAS_mulVec_kleinPAS {R : Type*} [CommRing R] (a b g : R) (h5 : (5 : R) = 0)
    (y : Fin 5 → R) :
    Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) (kleinPAS a b g y) = 0 := by
  funext i
  fin_cases i
  · simp [Work.MotAS.ASRul.kleinMAS, Work.MotAS.kleinPAS,
        Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2,
        Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
    linear_combination (norm := refl_ring1 (mod := 5))
  · simp [Work.MotAS.ASRul.kleinMAS, Work.MotAS.kleinPAS,
        Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2,
        Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
    linear_combination (norm := refl_ring1 (mod := 5))
  · simp [Work.MotAS.ASRul.kleinMAS, Work.MotAS.kleinPAS,
        Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2,
        Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
    linear_combination (norm := refl_ring1 (mod := 5))
  · simp [Work.MotAS.ASRul.kleinMAS, Work.MotAS.kleinPAS,
        Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2,
        Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
    linear_combination (norm := refl_ring1 (mod := 5))
  · simp [Work.MotAS.ASRul.kleinMAS, Work.MotAS.kleinPAS,
        Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1, Work.MotAS.kleinPAS2,
        Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
    linear_combination (norm := refl_ring1 (mod := 5))

/-- **The AS ruling system, linear in `y`.** -/
theorem AmatAS2_mulVec {R : Type*} [CommRing R] (a b g : R) (y c : Fin 5 → R) :
    Matrix.mulVec (AmatAS2 a b g c) y = Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) c := by
  funext i
  fin_cases i <;>
  · simp [AmatAS2, Work.MotAS.ASRul.kleinMAS, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five]
    refl_ring1

/-- **The source point of the AS chart lies in the kernel of the AS ruling matrix at its image.**
If `kleinPAS a b g y = c` then `AmatAS2 a b g c *ᵥ y = 0` — the AS analogue of the T-route step
`AmatP c' *ᵥ y = 0` for `c' = kleinTwP y`. -/
theorem AmatAS2_mulVec_of_kleinPAS {R : Type*} [CommRing R] (a b g : R) (h5 : (5 : R) = 0)
    (y : Fin 5 → R) :
    Matrix.mulVec (AmatAS2 a b g (kleinPAS a b g y)) y = 0 := by
  rw [AmatAS2_mulVec]
  exact kleinMAS_mulVec_kleinPAS a b g h5 y

end Work.MotAS
