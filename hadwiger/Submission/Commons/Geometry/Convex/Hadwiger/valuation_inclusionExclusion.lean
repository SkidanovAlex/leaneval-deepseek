import Mathlib.Analysis.Convex.Body
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Geometry.Convex.Hadwiger

/-- Inclusion–exclusion for a quadruple-additive valuation: from the additivity law
`φ A + φ B = φ C + φ D` (when `A = C ∪ D` and `B = C ∩ D`) solve for `φ A`. -/
theorem valuation_inclusionExclusion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    {A B C D : ConvexBody V}
    (hU : (A : Set V) = (C : Set V) ∪ (D : Set V))
    (hI : (B : Set V) = (C : Set V) ∩ (D : Set V)) :
    φ A = φ C + φ D - φ B := by
  have h := hadd A B C D hU hI
  linarith

end Commons.Geometry.Convex.Hadwiger