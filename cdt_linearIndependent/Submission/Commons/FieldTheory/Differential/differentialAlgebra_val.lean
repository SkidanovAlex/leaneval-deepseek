import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing

namespace Commons.FieldTheory.Differential

/-- If `E : IntermediateField F L` is stable under the derivation of `L`
(`hE`) and carries the restricted derivation `dE` (`hdE`), then `E ⊆ L` is a
differential algebra: the derivation of `E` commutes with the inclusion
`E → L`, because on `E` the derivation of `L` restricts to `dE`. -/
theorem differentialAlgebra_val {F L : Type*} [Field F] [Differential F] [Field L]
    [Algebra F L] [Differential L] (E : IntermediateField F L)
    (hE : ∀ x ∈ E, Differential.deriv x ∈ E) (dE : Differential E)
    (hdE : ∀ x : E, dE.deriv x = ⟨Differential.deriv (x : L), hE (x : L) x.2⟩) :
    letI := dE; DifferentialAlgebra E L := by
  refine ⟨fun a => ?_⟩
  show Differential.deriv (algebraMap E L a) = algebraMap E L (dE.deriv a)
  rw [hdE a]
  show Differential.deriv (algebraMap E L a)
    = algebraMap E L ⟨Differential.deriv (a : L), hE (a : L) a.2⟩
  rfl

end Commons.FieldTheory.Differential