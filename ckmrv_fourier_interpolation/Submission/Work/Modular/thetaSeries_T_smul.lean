import Mathlib
import Submission.Work.Modular.Lattice

namespace Work.Modular

open Work.Modular
open scoped Real MatrixGroups
open UpperHalfPlane

/-- The theta series of an even lattice is invariant under `τ ↦ τ + 1`: since `‖x‖² = 2k` for
every lattice vector, the summand picks up the factor `exp (π i ‖x‖²) = exp (2 π i k) = 1`. -/
theorem thetaSeries_T_smul {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] (heven : IsEvenSubmodule L) (τ : ℍ) :
    thetaSeries L (ModularGroup.T • τ) = thetaSeries L τ := by
  rw [thetaSeries]
  refine tsum_congr (fun x => ?_)
  simp only [thetaTerm]
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  obtain ⟨k, hk⟩ := heven (x : EuclideanSpace ℝ (Fin n)) x.2
  have hper :
      Complex.exp (π * Complex.I * ((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [hk]
    push_cast
    rw [show π * Complex.I * (2 * (k : ℂ)) = (k : ℂ) * (2 * π * Complex.I) by ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  rw [hT,
    show π * Complex.I * ((τ : ℂ) + 1) * ((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) : ℂ)
        = π * Complex.I * (τ : ℂ) * ((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) : ℂ)
          + π * Complex.I * ((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ) : ℂ) by ring]
  rw [Complex.exp_add, hper, mul_one]

end Work.Modular
