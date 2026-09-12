import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_inclusionExclusion

namespace Commons.Geometry.Convex.Hadwiger

/-- A simple valuation (one vanishing on every convex body with empty interior)
satisfies ordinary binary inclusion–exclusion: since `B = C ∩ D` has empty
interior, `φ B = 0` and the additivity law `φ A + φ B = φ C + φ D` collapses to
`φ A = φ C + φ D`. -/
theorem simple_valuation_binary_union
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (φ : ConvexBody V → ℝ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → φ K = 0)
    {A B C D : ConvexBody V}
    (hU : (A : Set V) = (C : Set V) ∪ (D : Set V))
    (hI : (B : Set V) = (C : Set V) ∩ (D : Set V))
    (hB : interior (B : Set V) = ∅) :
    φ A = φ C + φ D := by
  have hB0 : φ B = 0 := hsimple B hB
  have hie : φ A = φ C + φ D - φ B := valuation_inclusionExclusion (V := V) φ hadd hU hI
  linarith

end Commons.Geometry.Convex.Hadwiger
