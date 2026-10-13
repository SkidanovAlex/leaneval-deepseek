/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkIntegrand_perz_RHS.lean` — the per-`z` energy bound of the
# scheme's right-hand side, from its trace data

`Work.FTS.EpsEngine.HkIntegrand_perz_le_of_traces` (proved) gives the per-`z` bound

    ∫_θ HkIntegrand α 4 f z θ ≤ C (1 + w z ^ 2) (1 + Xn6 α f)^2      (z ∈ Iz)

for every profile `f` that is `SmoothOpen`, `HkMem α 6` and satisfies `BdryTraces α 6`.  This module
instantiates it along a family of scheme right-hand-sides `H s = epsRHSP α ρ ε Φs E g s`, so that
the per-`z` energy input of `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz` is discharged for the
right-hand side as soon as its **trace (flatness) data** and its uniform `ℋ⁶`-size are available.

The trace data `BdryTraces α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)` is the one genuinely missing input on the
route (interface item `(H4-perz)` of `NOTES_perz_intervalIntegral.md` §3); it is the same class
clause that the class-`C` propagation of the local step needs, so nothing new is required.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.HkIntegrand_perz_le_of_traces
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` energy bound of the projected scheme's right-hand side.** -/
theorem HkIntegrand_perz_RHS {α Ce T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T) (hCe : 0 ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (htr : ∀ s ∈ Set.Icc 0 T, Work.FTS.Nonlin.BdryTraces α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hbd6 : ∀ s ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc 0 T,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_perz_le_of_traces
  refine ⟨C, hCpos, ?_⟩
  intro z hz s hs
  refine le_trans (hC α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) hα (hreg s hs) (hmem s hs) (htr s hs) z hz) ?_
  have h1 : (1 : ℝ) ≤ 1 + Ce := by linarith
  have h2 : (1 : ℝ) + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ 1 + Ce := by
    linarith [hbd6 s hs]
  have h3 : (0 : ℝ) ≤ 1 + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) := by
    have := Work.Spaces.HkNorm_nonneg α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)
    rw [Work.FTS.StrongGlobal.Xn6]
    linarith
  have h4 : (0 : ℝ) ≤ 1 + Ce := by linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2)
    (mul_nonneg hCpos.le (by positivity))

end Work.FTS.EpsEngine
