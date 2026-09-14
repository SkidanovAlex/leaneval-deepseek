import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

theorem card_algHom_eq_finrank {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [Algebra.IsSeparable ℚ K] :
    Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := by
  exact AlgHom.card ℚ K ℂ

end Commons.NumberTheory.NumberField