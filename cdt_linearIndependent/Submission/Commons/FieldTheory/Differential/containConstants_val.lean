import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing

namespace Commons.FieldTheory.Differential

theorem containConstants_val {F L : Type*} [Field F] [Field L] [Algebra F L] [Differential L]
    [Differential.ContainConstants F L] (E : IntermediateField F L) :
    Differential.ContainConstants E L := by
  refine ⟨fun {x} hx => ?_⟩
  obtain ⟨f, hf⟩ := mem_range_of_deriv_eq_zero F hx
  exact ⟨algebraMap F E f, by rw [← IsScalarTower.algebraMap_apply F E L, hf]⟩

end Commons.FieldTheory.Differential