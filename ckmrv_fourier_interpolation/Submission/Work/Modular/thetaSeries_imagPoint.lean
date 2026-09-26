import Mathlib
import Submission.Work.Modular.ThetaImagAxis

namespace Work.Modular

open Work.Modular
open scoped Real MatrixGroups
open UpperHalfPlane

/-- On the imaginary axis `τ = i t` with `t > 0`, the theta series of a lattice `L ⊆ ℝⁿ`
coincides with the Gaussian sum: `Θ_L (i t) = ∑_{x ∈ L} exp (-π t ‖x‖²)`. -/
theorem thetaSeries_imagPoint {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (ht : 0 < t) : thetaSeries L (imagPoint t) = gaussSum L t := by
  simp only [thetaSeries, gaussSum]
  apply tsum_congr
  intro x
  simp only [thetaTerm]
  congr 1
  rw [coe_imagPoint ht]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end Work.Modular
