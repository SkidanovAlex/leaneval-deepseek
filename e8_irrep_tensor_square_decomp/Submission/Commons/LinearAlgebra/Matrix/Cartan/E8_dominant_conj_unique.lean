import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- Two dominant weights obtained from a common weight by Weyl-group words coincide: the closed
dominant chamber is a fundamental domain for the Weyl group of `E₈`. -/
theorem E8_dominant_conj_unique {d d' η : Fin 8 → ℤ} (hd : ∀ i, 0 ≤ d i) (hd' : ∀ i, 0 ≤ d' i) {L L' : List (Fin 8)} (h : Commons.LinearAlgebra.Matrix.Cartan.wact L η = d) (h' : Commons.LinearAlgebra.Matrix.Cartan.wact L' η = d') : d = d' := by
  have hmem : ∃ M : List (Fin 8), wact M d = d' := by
    refine ⟨L.reverse ++ L', ?_⟩
    rw [wact_append]
    have h1 : wact L.reverse d = η := by rw [← h, wact_reverse]
    rw [h1, h']
  exact E8_dominant_unique hd hd' hmem

end Commons.LinearAlgebra.Matrix.Cartan
