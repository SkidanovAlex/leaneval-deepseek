/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/LimGdot.lean` — the fake-time derivative of a limit package

`EpsLimPkg` (`Submission/Work/FTS/StrongEps/EpsLimit.lean`) carries the limiting equation only in
the *within*`[0,T]` form (`eqT`).  This module draws the two consequences that the `dbd` clause of
the design's E5 (`HkNorm α 3 (∂_τ g) ≤ Cd`) consumes:

* `EpsLimPkg.gdot_eq` — at an **interior** fake time `τ ∈ (0,T)` the within-derivative is an
  honest derivative, so `gdot g τ = rhsFun α Φs E g τ` on the open quadrant;
* `EpsLimPkg.gdot_eq_eqOn` — the same as an `EqOn` statement on the open quadrant.

Once the identification of the limit equation is available, these turn the `dbd` clause into a
level-three estimate for the *limiting* right-hand side `rhsFun`, which is what the frozen
level-three package (`Work.FTS.StrongPersist.L3Data`, `lin` + `nonlin`) prices.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.Gdot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false

/-- **The limiting equation as an identity for `gdot`.**  At an interior fake time the derivative
of the package's `eqT` clause is honest, so `deriv` sees it. -/
theorem EpsLimPkg.gdot_eq {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    gdot g τ z θ = rhsFun α Φs E g τ z θ := by
  rw [gdot]
  exact (h.eqT τ hτ.1.le hτ.2.le z θ ⟨hz, hθ⟩).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2) |>.deriv

/-- The same, as an `EqOn` statement on the open quadrant. -/
theorem EpsLimPkg.gdot_eq_eqOn {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    Set.EqOn (Function.uncurry (gdot g τ)) (Function.uncurry (rhsFun α Φs E g τ))
      Work.FTS.EllipticEst.Q0 :=
  fun p hp => h.gdot_eq hτ hp.1 hp.2

/-- The `init`-clause of the package, read at the fake time `0`. -/
theorem EpsLimPkg.gdot_at_zero {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) : slice g 0 = g₀ :=
  funext fun z => funext fun θ => h.init z θ

end Work.FTS.StrongEps
