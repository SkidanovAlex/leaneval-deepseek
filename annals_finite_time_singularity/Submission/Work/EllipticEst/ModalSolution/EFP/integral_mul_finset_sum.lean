import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.EFP

theorem integral_mul_finset_sum (s : Finset ℕ) (c : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hint : ∀ m ∈ s, MeasureTheory.IntegrableOn
      (fun θ => f θ * e m θ * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ * (∑ m ∈ s, c m * e m θ) * Real.cos θ)
      = ∑ m ∈ s, c m * (∫ θ in Work.Spaces.Iθ, f θ * e m θ * Real.cos θ) := by
  -- pointwise, the integrand is the finite sum of the individual integrands
  have hpt : ∀ θ, f θ * (∑ m ∈ s, c m * e m θ) * Real.cos θ
      = ∑ m ∈ s, c m * (f θ * e m θ * Real.cos θ) := by
    intro θ
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  simp only [hpt]
  -- linearity of the Bochner integral over a finite sum, then pull out the scalars
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl (fun m _ => by rw [MeasureTheory.integral_const_mul])
  · intro m hm
    exact (hint m hm).const_mul (c m)

end Work.EllipticEst.ModalSolution.EFP
