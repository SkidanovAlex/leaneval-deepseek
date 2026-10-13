import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- The `N` attached to a product of two unit-valued elements: `(N₁ + 1) * (N₂ + 1) = N + 1`
with `N = N₁ * N₂ + N₁ + N₂`. -/
private lemma unitVal_mul_cast {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (N₁ N₂ : ℕ) :
    ((N₁ * N₂ + N₁ + N₂ : ℕ) : M) + 1 = ((N₁ : M) + 1) * ((N₂ : M) + 1) := by
  push_cast
  ring

/-- `IsUnitVal` is multiplicative: the product of two elements in the Archimedean class of `1`
(equivalently, of value `0` in the natural valuation) is again in that class.

Indeed `1/(N₁+1) ≤ |x| ≤ N₁+1` and `1/(N₂+1) ≤ |y| ≤ N₂+1` give
`1/(N+1) ≤ |x·y| ≤ N+1` with `N = N₁N₂ + N₁ + N₂`. -/
theorem unitVal_mul {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x y : M}
    (hx : WilkiesDesign.CG.IsUnitVal x) (hy : WilkiesDesign.CG.IsUnitVal y) :
    WilkiesDesign.CG.IsUnitVal (x * y) := by
  obtain ⟨N₁, h1lo, h1hi⟩ := hx
  obtain ⟨N₂, h2lo, h2hi⟩ := hy
  have hA : (0 : M) ≤ (N₁ : M) + 1 := by positivity
  have hB : (0 : M) ≤ (N₂ : M) + 1 := by positivity
  refine ⟨N₁ * N₂ + N₁ + N₂, ?_, ?_⟩
  · rw [abs_mul, unitVal_mul_cast, mul_inv]
    exact mul_le_mul h1lo h2lo (inv_nonneg.mpr hB) (abs_nonneg x)
  · rw [abs_mul, unitVal_mul_cast]
    exact mul_le_mul h1hi h2hi (abs_nonneg y) hA

end Work.WilC4
