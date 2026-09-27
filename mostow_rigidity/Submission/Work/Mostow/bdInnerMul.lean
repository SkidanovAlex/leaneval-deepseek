import Mathlib
import Submission.Work.Mostow.busemannCocycle
import Submission.Work.Mostow.LambdaMat_theta_eq_exp_smul

/-!
# The boundary action scales the spherical inner product by the Busemann cocycle

For `ξ, η ∈ Sph n` and `g : PO n 1`, the null lifts `θ ξ = (ξ,1)`, `θ η = (η,1)` satisfy
`mform (θ ξ) (θ η) = inner ℝ ξ η - 1`, and `mat (rep g) *ᵥ θ ξ = bdt g ξ • θ (bd g ξ)`.
Since `mat (rep g)` preserves the Minkowski form `mform`, and `exp (bCocy g ξ) = tsign (rep g) * (bdt g ξ)⁻¹`,
the two scaling factors combine into the claimed identity.

This is the conformal (cross-ratio) factor of the boundary action: the quantity `1 - ⟪ξ,η⟫`
is scaled by `exp (bCocy g ξ + bCocy g η)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory _root_.Matrix

theorem bdInnerMul (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) (g : LeanEval.Geometry.MostowRigidity.PO n 1) {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) : 1 - inner ℝ (Submission.Mostow.bd g ξ) (Submission.Mostow.bd g η) = (1 - inner ℝ ξ η) * Real.exp (Work.Mostow.bCocy g ξ + Work.Mostow.bCocy g η) := by
  have hbξ : bdt g ξ ≠ 0 := bdt_ne_zero g ξ hξ
  have hbη : bdt g η ≠ 0 := bdt_ne_zero g η hη
  -- the lifted null vector of `bd g ξ` is the rescaling of `mat (rep g) *ᵥ θ ξ`
  have hsmξ : Submission.Mostow.mat (Submission.Mostow.rep g) *ᵥ theta ξ
      = bdt g ξ • theta (bd g ξ) :=
    smul_theta_of_time_ne_zero _ hbξ
  have hsmη : Submission.Mostow.mat (Submission.Mostow.rep g) *ᵥ theta η
      = bdt g η • theta (bd g η) :=
    smul_theta_of_time_ne_zero _ hbη
  -- invariance of `mform` under `mat (rep g)`
  have hmain : mform (bdt g ξ • theta (bd g ξ)) (bdt g η • theta (bd g η))
      = mform (theta ξ) (theta η) := by
    rw [← hsmξ, ← hsmη]
    exact mform_mat_mulVec (Submission.Mostow.rep g) _ _
  rw [mform_smul_left, mform_smul_right] at hmain
  have h1 : mform (theta ξ) (theta η) = inner ℝ ξ η - 1 := by
    rw [mform_eq]; simp
  have h2 : mform (theta (bd g ξ)) (theta (bd g η)) = inner ℝ (bd g ξ) (bd g η) - 1 := by
    rw [mform_eq]; simp
  rw [h1, h2] at hmain
  -- `exp` of the sum of cocycles is the inverse of the product of the time coordinates
  have hexp : Real.exp (bCocy g ξ + bCocy g η) = (bdt g ξ * bdt g η)⁻¹ := by
    rw [Real.exp_add, exp_bCocy_eq n hA g ξ hξ, exp_bCocy_eq n hA g η hη, mul_inv]
    ring_nf
    rw [pow_two, tsign_sq, one_mul]
  have hz : bdt g ξ * bdt g η ≠ 0 := mul_ne_zero hbξ hbη
  have hkey : (1 - inner ℝ (bd g ξ) (bd g η)) * (bdt g ξ * bdt g η) = 1 - inner ℝ ξ η := by
    have := hmain
    ring_nf at this ⊢
    linarith
  rw [hexp]
  calc 1 - inner ℝ (bd g ξ) (bd g η)
      = (1 - inner ℝ (bd g ξ) (bd g η))
          * ((bdt g ξ * bdt g η) * (bdt g ξ * bdt g η)⁻¹) := by
        rw [mul_inv_cancel₀ hz, mul_one]
    _ = ((1 - inner ℝ (bd g ξ) (bd g η)) * (bdt g ξ * bdt g η))
          * (bdt g ξ * bdt g η)⁻¹ := by ring
    _ = (1 - inner ℝ ξ η) * (bdt g ξ * bdt g η)⁻¹ := by rw [hkey]

end Work.Mostow
