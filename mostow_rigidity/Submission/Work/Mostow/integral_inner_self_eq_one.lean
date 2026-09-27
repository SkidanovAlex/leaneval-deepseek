import Mathlib

namespace Work.Mostow

open MeasureTheory

/-- If a probability measure `ν` on `EuclideanSpace ℝ (Fin n)` is supported on the unit
sphere (i.e. `ν (sphere 0 1)ᶜ = 0`), then the second moment `∫ ξ, ⟪ξ,ξ⟫ ∂ν` equals `1`. -/
theorem integral_inner_self_eq_one {n : ℕ} (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    [MeasureTheory.IsProbabilityMeasure ν]
    (hsupp : ν (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)ᶜ = 0) :
    ∫ ξ, inner ℝ ξ ξ ∂ν = 1 := by
  -- `ν` lives on the unit sphere
  have hmem : ∀ᵐ ξ ∂ν, ξ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  -- hence the integrand is a.e. equal to the constant `1`
  have hval : ∀ᵐ ξ ∂ν, inner ℝ ξ ξ = (1 : ℝ) := by
    filter_upwards [hmem] with ξ hξ
    rw [Metric.mem_sphere, dist_eq_norm] at hξ
    have h1 : ‖ξ‖ = 1 := by simpa using hξ
    rw [real_inner_self_eq_norm_sq, h1]
    norm_num
  calc (∫ ξ, inner ℝ ξ ξ ∂ν) = ∫ _ξ, (1 : ℝ) ∂ν := integral_congr_ae hval
    _ = 1 := by simp

end Work.Mostow
