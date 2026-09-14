import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.IntermediateField

theorem finrank_intermediateField_mul {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (E : IntermediateField K L) :
    Module.finrank K ↥E * Module.finrank ↥E L = Module.finrank K L := by
  exact Module.finrank_mul_finrank K (↥E) L

end Commons.FieldTheory.IntermediateField