import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.SymAPI
import Submission.Work.OneBodyKin.famSym_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.OneBodyKin.Phi` — the residual as one explicit real-valued function

`SymBoundOne C` (the scale-free pointwise symbol bound) is *equivalent* to the single inequality

    `∀ ρ : ℝ³, 0 ≤ Phi C ρ`,

with `Phi C ρ = ‖ρ‖² − famSym 1 (fsKinCoeff C) ρ` (so the equivalence is `linarith`).  Expanded,
`Phi` is

    `‖ρ‖² − symA(ρ) + 2(2π)⁻³ boxHat(ρ) symD(ρ) − symA(0) boxHat(ρ)²`

(`Phi_eq_expand`), and using the exact relation `symD 1 F 0 = (2π)³ symA 1 F 0`
(`symD_zero_eq_symA_zero`, the algebra behind `famSym_zero`) it also reads

    `‖ρ‖² − symA(ρ) + 2(2π)⁻³ boxHat(ρ)(symD(ρ) − symD(0)) + symA(0)(2boxHat(ρ) − boxHat(ρ)²)`

(`PhiAlt`, the form in which the mechanism of `README.md` §5 is visible).  Since `Phi C 0 = 0`
(`Phi_zero`), `SymBoundOne C` is a *second-order* statement about a function vanishing at the
origin.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **The residual as an explicit function**: `Phi C ρ = ‖ρ‖² − famSym 1 (fsKinCoeff C) ρ`, i.e.
`SymBoundOne C` is exactly `0 ≤ Phi C` pointwise. -/
noncomputable def Phi (C : ℝ) (ρ : ℝ³) : ℝ :=
  ‖ρ‖ ^ 2 - famSym 1 (fsKinCoeff C) ρ

/-- The exact consistency relation behind `famSym_zero`: `symD 1 F 0 = (2π)³ symA 1 F 0`. -/
theorem symD_zero_eq_symA_zero (F : ℝ → ℝ) :
    symD 1 F 0 = (2 * Real.pi) ^ 3 * symA 1 F 0 := by
  rw [symD_zero]
  simp only [one_smul]
  have h : symA 1 F 0 = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * (profHat p) ^ 2 := by
    unfold symA
    simp
  rw [h, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ^ 3 ≠ 0), one_mul]

/-- **The residual, checkably**: `SymBoundOne C` is exactly the pointwise positivity of the
explicit function `Phi C`. -/
theorem SymBoundOne_iff_Phi (C : ℝ) : SymBoundOne C ↔ ∀ ρ : ℝ³, 0 ≤ Phi C ρ := by
  constructor
  · intro h ρ; unfold Phi; linarith [h ρ]
  · intro h ρ; have := h ρ; unfold Phi at this; linarith

/-- `Phi` vanishes at the origin for every cut-off: the residual is an *equality* at `ρ = 0`. -/
theorem Phi_zero (C : ℝ) : Phi C 0 = 0 := by
  unfold Phi
  rw [famSym_zero (by norm_num : (0 : ℝ) < 1)]
  simp

/-- The expanded form of `Phi` used by the estimates. -/
theorem Phi_eq_expand (C : ℝ) (ρ : ℝ³) :
    Phi C ρ = ‖ρ‖ ^ 2 - symA 1 (fsKinCoeff C) ρ
      + 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 ρ * symD 1 (fsKinCoeff C) ρ
      - symA 1 (fsKinCoeff C) 0 * (boxHat 1 ρ) ^ 2 := by
  unfold Phi famSym symC
  norm_num
  ring

/-- **The analysis-friendly form of `Phi`** (`PhiAlt`): using `symD 1 F 0 = (2π)³ symA 1 F 0`,

    `Phi C ρ = ‖ρ‖² − symA(ρ) + 2(2π)⁻³ boxHat(ρ)(symD(ρ) − symD(0))
                  + symA(0)·(2 boxHat(ρ) − boxHat(ρ)²)`.

This is the form in which the mechanism of the residual is visible: the *gain* `‖ρ‖² − symA(ρ)`
of the cut-off, the *change* `symD(ρ) − symD(0)` of the cross term, and the box profile
correction `2boxHat − boxHat² = 1 − (1 − boxHat)² ≤ 1`. -/
theorem PhiAlt (C : ℝ) (ρ : ℝ³) :
    Phi C ρ = ‖ρ‖ ^ 2 - symA 1 (fsKinCoeff C) ρ
      + 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat 1 ρ * (symD 1 (fsKinCoeff C) ρ - symD 1 (fsKinCoeff C) 0)
      + symA 1 (fsKinCoeff C) 0 * (2 * boxHat 1 ρ - (boxHat 1 ρ) ^ 2) := by
  rw [Phi_eq_expand, symD_zero_eq_symA_zero]
  ring_nf
  rw [show (Real.pi : ℝ) ^ 3 * (Real.pi)⁻¹ ^ 3 = 1 from by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]]
  ring

end Work.OneBodyKin
