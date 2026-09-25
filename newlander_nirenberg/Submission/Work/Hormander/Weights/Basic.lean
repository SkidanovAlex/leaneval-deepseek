/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# First API for the weighted `∂̄`-operators on `ℂⁿ`

Elementary properties of the operators `dbarCoord`, `dCoord` of
`Work.Hormander.Weights.Defs`: linearity, the Leibniz rule, the values on the
coordinate functions, and the compatibility with `Submission.dbar` for the
standard structure.
-/
import Submission.Work.Hormander.Weights.Defs

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### Compatibility with `Submission.dbar` -/

/-- `dbarCoord` is the `j`-th component of the standard `∂̄`-operator, i.e. of the
operator `Submission.dbar J u` of `Submission.Work.Core.Defs` for the standard
structure `Submission.Jstd` (on `Cn n = Submission.F n`, where `Jstd` lives). -/
theorem dbarCoord_eq_stdFormula (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord n j u z = (1 / 2 : ℂ) *
      (fderiv ℝ u z (evec n j)
        + Complex.I * fderiv ℝ u z ((Submission.Jstd n) z (evec n j))) := by
  simp [dbarCoord, ivec, Submission.Jstd]

/-- The same, for `dCoord`: `∂_j u = (1/2)(du(e_j) - i·du(i e_j))`. -/
theorem dCoord_eq_stdFormula (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dCoord n j u z = (1 / 2 : ℂ) *
      (fderiv ℝ u z (evec n j)
        - Complex.I * fderiv ℝ u z ((Submission.Jstd n) z (evec n j))) := by
  simp [dCoord, ivec, Submission.Jstd]

/-! ### Linearity -/

theorem dbarCoord_add (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord n j (u + v) z = dbarCoord n j u z + dbarCoord n j v z := by
  simp only [dbarCoord, fderiv_add hu hv, add_apply]
  ring

theorem dbarCoord_neg (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord n j (-u) z = -dbarCoord n j u z := by
  simp only [dbarCoord, fderiv_neg, neg_apply]
  ring

theorem dbarCoord_sub (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord n j (u - v) z = dbarCoord n j u z - dbarCoord n j v z := by
  simp only [dbarCoord, fderiv_sub hu hv, sub_apply]
  ring

theorem dbarCoord_const (j : Fin n) (c : ℂ) (z : Cn n) :
    dbarCoord n j (fun _ => c) z = 0 := by
  simp [dbarCoord]

theorem dCoord_add (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord n j (u + v) z = dCoord n j u z + dCoord n j v z := by
  simp only [dCoord, fderiv_add hu hv, add_apply]
  ring

/-! ### The Leibniz rule -/

theorem dbarCoord_mul (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord n j (fun w => u w * v w) z
      = dbarCoord n j u z * v z + u z * dbarCoord n j v z := by
  have h : fderiv ℝ (fun w => u w * v w) z
      = u z • fderiv ℝ v z + v z • fderiv ℝ u z := fderiv_mul hu hv
  simp only [dbarCoord, h, add_apply, smul_apply,
    smul_eq_mul]
  ring

theorem dCoord_mul (j : Fin n) (u v : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dCoord n j (fun w => u w * v w) z
      = dCoord n j u z * v z + u z * dCoord n j v z := by
  have h : fderiv ℝ (fun w => u w * v w) z
      = u z • fderiv ℝ v z + v z • fderiv ℝ u z := fderiv_mul hu hv
  simp only [dCoord, h, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-! ### The coordinate functions -/

theorem coord_evec (j k : Fin n) : coord n j (evec n k) = if j = k then 1 else 0 := by
  rw [coord_apply, evec_ofLp, Pi.single_apply]

theorem coord_ivec (j k : Fin n) : coord n j (ivec n k) = if j = k then Complex.I else 0 := by
  rw [coord_apply, ivec_ofLp, Pi.single_apply]

/-- The coordinate functions are `∂̄`-closed. -/
theorem dbarCoord_coord (j k : Fin n) (z : Cn n) :
    dbarCoord n k (fun w => coord n j w) z = 0 := by
  have hfd : fderiv ℝ (fun w : Cn n => (coord n j) w) z = (coord n j).restrictScalars ℝ :=
    ContinuousLinearMap.fderiv ((coord n j).restrictScalars ℝ)
  rw [dbarCoord, hfd]
  change (1 / 2 : ℂ) * (coord n j (evec n k) + Complex.I * coord n j (ivec n k)) = 0
  rw [coord_evec, coord_ivec]
  by_cases hjk : j = k <;> simp [hjk]

/-- The `∂`-derivative of the coordinate functions. -/
theorem dCoord_coord (j k : Fin n) (z : Cn n) :
    dCoord n k (fun w => coord n j w) z = if j = k then 1 else 0 := by
  have hfd : fderiv ℝ (fun w : Cn n => (coord n j) w) z = (coord n j).restrictScalars ℝ :=
    ContinuousLinearMap.fderiv ((coord n j).restrictScalars ℝ)
  rw [dCoord, hfd]
  change (1 / 2 : ℂ) * (coord n j (evec n k) - Complex.I * coord n j (ivec n k))
    = if j = k then 1 else 0
  rw [coord_evec, coord_ivec]
  by_cases hjk : j = k <;> simp [hjk] <;> norm_num

end Work.Hormander.Weights
