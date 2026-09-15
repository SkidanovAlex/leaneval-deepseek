import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open Function Set MeasureTheory
open scoped Pointwise

namespace Commons.Analysis.Convolution

/-- **Compact support of a mollification.**  If `ρ` and `u` both have compact support then so does
`z ↦ ∫ y, ρ y • u (z - y)`. -/
theorem hasCompactSupport_integral_smul_sub {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : (Fin d → ℂ) → ℝ} {u : (Fin d → ℂ) → E}
    (hsρ : HasCompactSupport ρ) (hsu : HasCompactSupport u) :
    HasCompactSupport (fun z => ∫ y, ρ y • u (z - y)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
  -- The convolution `z ↦ ∫ y, ρ y • u (z - y)` vanishes off `tsupport ρ + tsupport u`.
  have hKρ : IsCompact (tsupport ρ) := hsρ
  have hKu : IsCompact (tsupport u) := hsu
  have hK : IsCompact (tsupport ρ + tsupport u) := hKρ.add hKu
  have hzero : ∀ z ∉ tsupport ρ + tsupport u,
      (∫ y, ρ y • u (z - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) = 0 := by
    intro z hz
    -- The integrand is identically zero: either `ρ y = 0`, or `z - y ∉ tsupport u`.
    have hpt : (fun y : Fin d → ℂ => ρ y • u (z - y)) = fun _ => (0 : E) := by
      funext y
      by_cases hρ : ρ y = 0
      · simp [hρ]
      · have hy : y ∈ tsupport ρ := subset_tsupport ρ (mem_support.2 hρ)
        have hu : u (z - y) = 0 := by
          by_contra hcu
          have hyu : z - y ∈ tsupport u := subset_tsupport u (mem_support.2 hcu)
          exact hz (by
            have h1 : y + (z - y) = z := by abel
            rw [← h1]
            exact add_mem_add hy hyu)
        simp [hu]
    rw [hpt]
    simp
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  rw [tsupport]
  exact closure_minimal (fun z hz => by
    by_contra h
    exact hz (hzero z h)) hK.isClosed

end Commons.Analysis.Convolution