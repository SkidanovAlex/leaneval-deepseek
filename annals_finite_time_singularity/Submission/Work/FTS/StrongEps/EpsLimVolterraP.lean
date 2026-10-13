/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLimVolterraP.lean` — E5-4(ii) for the `P₀`-corrected scheme

`EpsLimVolterra` (`EpsLimVolterra.lean`) is the Volterra half of E5-4: if the `ε`-solutions of the
scheme have right-hand sides that are continuous in `s` on `[0,T]`, converge pointwise at *every*
`p ∈ Q0` and every `s ∈ Icc 0 T` to the limiting right-hand side `rhsFun α Φs E g s p`, are
uniformly bounded in `(n,s)` at each `p`, and the family values converge at every `(p,τ)`, then the
limit family satisfies the limiting equation `eqT` (a `HasDerivWithinAt` within `Icc 0 T`).

This module is the `P₀`-analogue: the only change is `IsEpsSol → IsEpsSolP` and
`epsRHS → epsRHSP`.  The statement is *scheme-independent otherwise* — the limiting right-hand side
`rhsFun` is the same function — so the proof is the verbatim application of
`hasDerivWithinAt_of_tendsto`, exactly as in the un-projected sibling.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.hasDerivWithinAt_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E5-4(ii) for the `P₀`-scheme**: the limit of a convergent sequence of `P₀`-scheme solutions
satisfies the limiting equation, provided the right-hand sides converge pointwise, are continuous
in the fake time and uniformly bounded at each point of the quadrant, and the family values
converge at every fake time. -/
theorem EpsLimVolterraP {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {g : Fam}
    (hT : 0 < T)
    (hsol : ∀ n : ℕ, IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2) (Set.Icc (0 : ℝ) T))
    (hlim : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2) Filter.atTop
        (nhds (rhsFun α Φs E g s p.1 p.2)))
    (hbdd : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, ∀ n : ℕ,
      ∀ s ∈ Set.Icc (0 : ℝ) T, |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C)
    (hconv0 : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n : ℕ => G n p.1 p.2 τ) Filter.atTop (nhds (g p.1 p.2 τ)))
    (hcontR : ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E g s p.1 p.2) (Set.Icc (0 : ℝ) T)) :
    ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 → ∀ τ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => g p.1 p.2 s) (rhsFun α Φs E g τ p.1 p.2)
        (Set.Icc (0 : ℝ) T) τ := by
  intro p hp τ hτ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  exact Work.FTS.StrongEps.hasDerivWithinAt_of_tendsto (T := T) hT.le
    (g := fun n s => G n p.1 p.2 s)
    (G := fun s => g p.1 p.2 s)
    (D := fun s => rhsFun α Φs E g s p.1 p.2)
    (dk := fun n s => epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
    (fun n s hs => (hsol n).2 p.1 p.2 s hz hθ hs)
    (fun n => hcont n p hp)
    (hbdd p hp)
    (hcontR p hp)
    (fun s hs => hconv0 p hp s hs)
    (fun s hs => hlim p hp s hs) τ hτ

end Work.FTS.StrongEps
