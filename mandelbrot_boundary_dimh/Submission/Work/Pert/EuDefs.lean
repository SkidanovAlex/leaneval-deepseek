import Mathlib
import Submission.Work.Pert.CoordDefs

/-!
# PERT · `Work.Pert.EuDefs`

Shared notation for the deviation `E_u = τ₀ ∘ τ_f - id` of the composite chart, used by
`Work.Pert.EuDevBounds` (Shishikura (4.2.5)) and its bricks.

* `euS α = s = 2πiα` — the exponent parameter of `τ_f`;
* `euPsi α = ψ = (e^s - 1)/s` — so that `σ u₀ = -s ψ` under `1 - σ u₀ = e^s`;
* `euT α η = t = -s·iη = 2παη` — the exponent of the two centres `±iη`.
-/

namespace Work.Pert

open Complex

noncomputable section

/-- `s = 2πiα`, the exponent parameter of `τ_f = tauC σ α`. -/
def euS (α : ℂ) : ℂ := 2 * Real.pi * Complex.I * α

/-- `ψ = (e^s - 1)/s`.  Under the normalisation `1 - σ u₀ = e^s` one has `σ u₀ = -s ψ`. -/
def euPsi (α : ℂ) : ℂ := (Complex.exp (euS α) - 1) / euS α

/-- `t = -s·iη = 2παη`, the exponent of the centres `±iη`. -/
def euT (α : ℂ) (η : ℝ) : ℂ := 2 * Real.pi * α * (η : ℂ)

theorem euS_ne_zero {α : ℂ} (hα : α ≠ 0) : euS α ≠ 0 := by
  rw [euS]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hα

theorem norm_euS (α : ℂ) : ‖euS α‖ = 2 * Real.pi * ‖α‖ := by
  rw [euS, norm_mul, norm_mul, norm_mul]
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2c, hp, hI, mul_one]

theorem norm_euT (α : ℂ) (η : ℝ) : ‖euT α η‖ = 2 * Real.pi * ‖α‖ * |η| := by
  rw [euT, norm_mul, norm_mul, norm_mul]
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hη : ‖(η : ℂ)‖ = |η| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h2c, hp, hη]

/-- `euT α η = -s·(iη)`. -/
theorem euT_eq_neg_mul {α : ℂ} {η : ℝ} : euT α η = -(euS α) * (Complex.I * (η : ℂ)) := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [euS, euT]
  linear_combination (2 * ↑Real.pi * α * ↑η) * h

/-- `s = i·t/η`. -/
theorem euS_eq_I_mul_euT_div {α : ℂ} {η : ℝ} (hη : (η : ℂ) ≠ 0) :
    euS α = Complex.I * euT α η / (η : ℂ) := by
  rw [euS, euT]
  field_simp

end

end Work.Pert
