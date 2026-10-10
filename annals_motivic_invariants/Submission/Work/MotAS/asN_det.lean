import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASEntries

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- `asN w k j = (w + 2k)^j` is the Vandermonde matrix in the five distinct nodes
`w, w+2, w+4, w+6, w+8`; its determinant is the constant
`∏_{i<j} ((w+2j) - (w+2i)) = 2^10 · ∏_{i<j}(j-i) = 2^10 · 288 = 294912`. -/
theorem asN_det {R : Type*} [CommRing R] (w : R) : (Work.MotAS.asN w).det = 294912 := by
  have h : asN w = Matrix.vandermonde (fun k : Fin 5 => w + 2 * (k : ℕ)) := rfl
  rw [h, Matrix.det_vandermonde]
  simp only [Fin.prod_univ_five]
  have h0 : Finset.Ioi (0 : Fin 5) = ({1, 2, 3, 4} : Finset (Fin 5)) := by decide
  have h1 : Finset.Ioi (1 : Fin 5) = ({2, 3, 4} : Finset (Fin 5)) := by decide
  have h2 : Finset.Ioi (2 : Fin 5) = ({3, 4} : Finset (Fin 5)) := by decide
  have h3 : Finset.Ioi (3 : Fin 5) = ({4} : Finset (Fin 5)) := by decide
  have h4 : Finset.Ioi (4 : Fin 5) = (∅ : Finset (Fin 5)) := by decide
  rw [h0, h1, h2, h3, h4]
  norm_num

end Work.MotAS
