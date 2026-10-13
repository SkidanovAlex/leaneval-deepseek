/-
# `Work.FTS.Physical.Clock.A_le_exp_mul` — exponential decay of the amplitude

The amplitude `A` of the dynamic rescaling solves `A' = -(1+μ)A` with `1 + μ ≥ 1/2`.  Since `A > 0`
in fake time, the function `x ↦ A x · e^{x/2}` has derivative
`e^{x/2} · A x · (1/2 - (1 + μ x)) ≤ 0`, so it is antitone on `[0,∞)`; this gives

  `A s ≤ A τ · e^{-(s-τ)/2}`  for `0 ≤ τ ≤ s`  (`PhysClock.A_le_exp_mul`),

the exponential decay that makes `T = ∫₀^∞ A` finite (the blow-up happens in finite time).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set

namespace Work.FTS.Physical.Clock

theorem A_le_exp_mul (C : Work.FTS.Physical.PhysClock) {τ s : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) : C.A s ≤ C.A τ * Real.exp (-(s - τ) / 2) := by
  -- `x ↦ A x * exp (x/2)` is antitone on `[0,∞)`: its derivative is
  -- `exp (x/2) * A x * (1/2 - (1 + μ x)) ≤ 0`, since `A x > 0` and `1 + μ x ≥ 1/2`.
  have hcont : ContinuousOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Set.Ici (0:ℝ)) := by
    exact C.hAcont.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
  have hderiv : ∀ x ∈ interior (Set.Ici (0:ℝ)),
      HasDerivWithinAt (fun x : ℝ => C.A x * Real.exp (x / 2))
        ((-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2)))
        (interior (Set.Ici (0:ℝ))) x := by
    intro x hx
    have hx' : (0:ℝ) < x := by simpa [interior_Ici] using hx
    have h1 : HasDerivAt (fun x : ℝ => C.A x) (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx'.le
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (x / 2) * (1/2)) x :=
      ((hasDerivAt_id x).div_const 2).exp
    exact (h1.mul h2).hasDerivWithinAt
  have hnonpos : ∀ x ∈ interior (Set.Ici (0:ℝ)),
      (-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2)) ≤ 0 := by
    intro x hx
    have hx' : (0:ℝ) < x := by simpa [interior_Ici] using hx
    have hA : 0 < C.A x := C.hApos x hx'.le
    have hE : 0 < Real.exp (x / 2) := Real.exp_pos _
    have hmu : (1:ℝ)/2 ≤ 1 + C.mu x := by
      have := C.hmu_lo x hx'.le
      linarith
    have heq : (-(1 + C.mu x) * C.A x) * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1/2))
        = Real.exp (x / 2) * C.A x * ((1:ℝ)/2 - (1 + C.mu x)) := by ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hE.le hA.le) (by linarith)
  have hanti : AntitoneOn (fun x : ℝ => C.A x * Real.exp (x / 2)) (Set.Ici (0:ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcont hderiv hnonpos
  have h1 : C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) :=
    hanti hτ (le_trans hτ hτs) hτs
  -- multiply the target inequality by `exp (s/2) > 0` to reduce it to `h1`
  have hpos : 0 < Real.exp (s / 2) := Real.exp_pos _
  have key : C.A s * Real.exp (s / 2) ≤ (C.A τ * Real.exp (-(s - τ) / 2)) * Real.exp (s / 2) := by
    calc C.A s * Real.exp (s / 2) ≤ C.A τ * Real.exp (τ / 2) := h1
      _ = (C.A τ * Real.exp (-(s - τ) / 2)) * Real.exp (s / 2) := by
            rw [mul_assoc, ← Real.exp_add]; congr 1; ring_nf
  exact (mul_le_mul_iff_left₀ hpos).mp key

end Work.FTS.Physical.Clock
