import Mathlib

/-!
# Vocabulary for the even Taylor splitting `Work.RPB.B3.evenTaylorSplit`

A smooth `F : (ℝ × ℝ) × ℝ → E` which is even in the last variable can be written as a polynomial
`∑_{j<k} r^{2j} • a_j(p)` in the even powers of `r` plus `r^{2k} • R`.  The coefficients and the
remainder are produced by the *Hadamard quotient*

`stepOp h (p,r) = ∫_0^1 ∂_r h (p, r u) du`,

which for smooth `h` equals `(h (p, r) - h (p, 0)) / r`, and by the *even quotient*
`evenStep h = stepOp (stepOp (h - h(·,0)))`, which for even `h` satisfies
`h (p,r) - h (p,0) = r^2 • evenStep h (p,r)`.

This file only contains the definitions, the predicate `Per` of `2π`-periodicity in the middle
variable, and the two elementary facts `pdR_eq_deriv` (the partial derivative in the last variable
is the one-variable derivative of the slice) and `stepOp_zero`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B3.EvenTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The direction `(0,1)` (derivative in the last variable) of `(ℝ × ℝ) × ℝ`. -/
def ee : (ℝ × ℝ) × ℝ := (0, 1)

/-- The partial derivative of `h` in the last variable, as a function of the point. -/
noncomputable def pdR (h : (ℝ × ℝ) × ℝ → E) : (ℝ × ℝ) × ℝ → E :=
  fun z => (fderiv ℝ h z) ee

/-- `2π`-periodicity in the middle variable. -/
def Per {F : Type*} (h : (ℝ × ℝ) × ℝ → F) : Prop :=
  ∀ τ t r, h ((τ, t + 2 * Real.pi), r) = h ((τ, t), r)

/-- `stepOp h (p,r) = ∫_0^1 ∂_r h (p, r u) du`.  For smooth `h` this is the Hadamard quotient
`(h (p, r) - h (p, 0)) / r` (with value `∂_r h (p, 0)` at `r = 0`). -/
noncomputable def stepOp (h : (ℝ × ℝ) × ℝ → E) : (ℝ × ℝ) × ℝ → E :=
  fun z => ∫ u in (0:ℝ)..1, pdR h (z.1, z.2 * u)

/-- `h ↦ h - h(·, 0)`. -/
def Hsub (h : (ℝ × ℝ) × ℝ → E) : (ℝ × ℝ) × ℝ → E :=
  fun z => h z - h (z.1, 0)

/-- The even quotient: divides `h(·,r) - h(·,0)` by `r²`. -/
noncomputable def evenStep (h : (ℝ × ℝ) × ℝ → E) : (ℝ × ℝ) × ℝ → E :=
  stepOp (stepOp (Hsub h))

/-- The `n`-fold even quotient. -/
noncomputable def chi (f : (ℝ × ℝ) × ℝ → E) (n : ℕ) : (ℝ × ℝ) × ℝ → E :=
  evenStep^[n] f

omit [CompleteSpace E] in
/-- The partial derivative in the last variable is the derivative of the one-variable slice. -/
theorem pdR_eq_deriv (h : (ℝ × ℝ) × ℝ → E) (p : ℝ × ℝ) (r : ℝ)
    (hd : DifferentiableAt ℝ h (p, r)) :
    pdR h (p, r) = deriv (fun s : ℝ => h (p, s)) r := by
  have h1 : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) r :=
    hasFDerivAt_prodMk_right p r
  have h2 : HasFDerivAt (fun s : ℝ => h (p, s))
      ((fderiv ℝ h (p, r)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) r :=
    hd.hasFDerivAt.comp r h1
  rw [pdR, h2.hasDerivAt.deriv]
  simp [ee, ContinuousLinearMap.inr_apply]

/-- The value of `stepOp` at `r = 0`. -/
theorem stepOp_zero (h : (ℝ × ℝ) × ℝ → E) (p : ℝ × ℝ) :
    stepOp h (p, 0) = pdR h (p, 0) := by
  rw [stepOp]
  rw [show (fun u : ℝ => pdR h (p, 0 * u)) = (fun _ => pdR h (p, 0)) from by
    funext u; rw [zero_mul]]
  rw [intervalIntegral.integral_const]
  simp

end Work.RPB.B3.EvenTaylor
