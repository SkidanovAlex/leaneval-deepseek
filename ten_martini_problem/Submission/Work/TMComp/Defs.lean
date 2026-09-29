/-
# Shared vocabulary for component C1 (`P_OpBasics`)

The operators of the almost Mathieu family are bounded operators on `ℓ²(ℤ)` with the
shift-plus-diagonal coordinate formula

`(H u) n = u (n+1) + u (n-1) + c n * u n`.

This file introduces the coordinate predicate `IsJacobiOp` independently of the frozen
`IsAlmostMathieuOperator` (which is the special choice `c n = 2 λ cos (2π (θ + n α))`), so
that the operator-theoretic lemmas needed for C1 can be stated and proved in full
generality.  This file contains nothing but definitions and immediate theorems; the
component lemmas live in sibling modules.
-/
import Mathlib
import ChallengeDeps

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

/-- The coordinate formula of a shift-plus-diagonal ("Jacobi") operator on `ℓ²(ℤ)` with
coefficient sequence `c`: `(H u) n = u (n+1) + u (n-1) + c n * u n`. -/
def IsJacobiOp (c : ℤ → ℂ) (H : EllTwo →L[ℂ] EllTwo) : Prop :=
  ∀ (u : EllTwo) (n : ℤ), H u n = u (n + 1) + u (n - 1) + c n * u n

/-- The almost Mathieu potential `2 λ cos (2π (θ + n α))`, as a function of `n : ℤ`. -/
def amoCoeff (α lam θ : ℝ) : ℤ → ℂ :=
  fun n => ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ)

/-- The challenge's `IsAlmostMathieuOperator` is the Jacobi formula with potential
`amoCoeff α lam θ`. -/
theorem isAMO_iff_isJacobiOp (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) :
    IsAlmostMathieuOperator α lam θ H ↔ IsJacobiOp (amoCoeff α lam θ) H := by
  simp only [IsAlmostMathieuOperator, IsJacobiOp, amoCoeff]
  refine forall_congr' fun u => forall_congr' fun n => ?_
  rw [show ((2 : ℂ) * (lam : ℂ) * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℂ))
      = ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ) from by
        push_cast; ring]

end Work.TMComp
