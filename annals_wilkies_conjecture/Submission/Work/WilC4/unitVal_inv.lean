import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- `IsUnitVal` is closed under inversion: if `(N+1)⁻¹ ≤ |x| ≤ N+1` then
`(N+1)⁻¹ ≤ |x⁻¹| ≤ N+1`, by antitonicity of inversion on the positive reals. -/
theorem unitVal_inv {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x : M} (hx : WilkiesDesign.CG.IsUnitVal x) : WilkiesDesign.CG.IsUnitVal x⁻¹ := by
  obtain ⟨N, h1, h2⟩ := hx
  have hxpos : 0 < |x| := lt_of_lt_of_le (by positivity) h1
  refine ⟨N, ?_, ?_⟩
  · rw [abs_inv]
    exact (inv_le_inv₀ (by positivity) hxpos).mpr h2
  · rw [abs_inv]
    exact inv_le_of_inv_le₀ (by positivity) h1

end Work.WilC4
