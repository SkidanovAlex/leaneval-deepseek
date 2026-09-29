import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing

namespace Commons.FieldTheory.Differential

/-- If `E` is an intermediate field of a differential field `L` which is closed under the
derivation, and the derivation on `E` restricts to the derivation on `L`, then `E` is a
differential algebra over `F` (where `L` is a differential algebra over `F`). -/
theorem differentialAlgebra_subfield {F L : Type*} [Field F] [Differential F] [Field L]
    [Algebra F L] [Differential L] [DifferentialAlgebra F L] (E : IntermediateField F L)
    (hE : ∀ x ∈ E, Differential.deriv x ∈ E) (dE : Differential E)
    (hdE : ∀ x : E, dE.deriv x = ⟨Differential.deriv (x : L), hE (x : L) x.2⟩) :
    letI := dE; DifferentialAlgebra F E := by
  refine ⟨fun a => ?_⟩
  apply Subtype.ext
  rw [hdE]
  simp only [IntermediateField.coe_algebraMap_apply]
  exact deriv_algebraMap a

end Commons.FieldTheory.Differential