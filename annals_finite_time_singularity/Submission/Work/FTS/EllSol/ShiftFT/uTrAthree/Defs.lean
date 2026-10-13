/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Auxiliary definitions for `Work.FTS.EllSol.ShiftFT.uTr_Athree`

The target `Work.FTS.EllSol.ShiftFT.uTr_Athree` compares the second angular slot
`∫∫ (∂_θ² u)² σ_η` of the truncated data `uTr N b u` with that of `u`.

The truncation is `uTr N b u = phiTr N · Gc N b u` with

`Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`,

so the second `θ`-derivative of `uTr` is

`∂_θ²(uTr) t θ = phiTr N t · ( chi N t · ∂_θ²u t θ + tailE N b (∂_θ²u) t θ )`

where `tailE` is the *tail integral* defined below: it is the moving integral of the
`θ`-differentiated integrand, and it is the only piece of the estimate that is not
pointwise trivial.  Its analysis is the content of the pointwise-in-`θ` bound
`Work.FTS.EllSol.ShiftFT.uTrAthree.tail_oneD`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

open MeasureTheory Set
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-- The tail integral of the `θθ`-derivative of `Gc N b u`: the second `θ`-derivative of
`Gc N b u` equals `chi N t · ∂_θ²u t θ + tailE N b (∂_θ²u) t θ`. -/
def tailE (N b : ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ) : ℝ :=
  Real.exp (b * t) * ∫ s in t..(2 * N),
    Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ

/-- The one-variable version of `tailE`, used for the pointwise-in-`θ` bound: for a fixed
angle `θ` the function `s ↦ f s θ` is an arbitrary real function `g`. -/
def tailE1 (N b : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (b * t) * ∫ s in t..(2 * N),
    Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * g s

/-- `tailE` applied to a `θ`-independent function is `tailE1` (definitional). -/
theorem tailE_const_apply (N b : ℝ) (g : ℝ → ℝ) (t θ : ℝ) :
    tailE N b (fun s _ => g s) t θ = tailE1 N b g t := rfl

end

end Work.FTS.EllSol.ShiftFT.uTrAthree
