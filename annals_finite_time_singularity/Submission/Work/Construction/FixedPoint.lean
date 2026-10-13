/-
# The CONSTRUCTION area: the "fake time" fixed-point argument (tex 1549-1578)

This module formalises the last step of §Modulation: the existence of a stationary solution `g`
of `\eqref{gEquationFinal}` of size `O(α²)`, obtained as the `τ → ∞` limit of the solution family
of the *fake-time* equation

  `∂_τ g + 𝓛_Γ^T(g) = -μ̄(τ)(Γ/c)2z²/(1+z)³ + N₀ + N + N_*`,  `g(z,θ,0) = 0`,
  `μ̄(τ) = L₁₂(N₀)(0,τ) + L₁₂(N)(0,τ)`

(tex 1559), where `IsTimeGSol` is the equation, `gdot g τ = ∂_τg(·,·,τ)` its time derivative and
`gAt g τ = g(·,·,τ)` the family.

## What is proved here and what is a named input

* `uniform_bound_of_energy`: from the a-priori differential inequality of tex 1569-1570,
  the `ℋ⁴`-norm of `g(·,·,τ)` is uniformly bounded by the level `y1` at which the cubic
  right hand side becomes negative — the paper's `|g|_{ℋ⁴} ≤ Cα²`.  This is an immediate
  corollary of the scalar comparison lemma `le_of_deriv_le_of_cubic`.
* `timeDeriv_decay`: from the differential inequality of tex 1575-1577 for
  `τ ↦ |∂_τg(·,·,τ)|_{ℋ³}`, that norm decays exponentially (`Cα² exp(-c*τ)`) by the scalar
  comparison lemma `gronwall_exp_bound`.
* `stationary_exists`: the existence theorem.  Its hypotheses are (i) the fake-time equation
  (`IsTimeGSol`), (ii) the two scalar inequalities above (whose *derivation* from the
  a-priori estimate is the content of `Apriori.lean`, applied at each τ), and (iii) the
  **compactness input**, stated as a closed general proposition about an arbitrary family
  `(g(·,·,τ))` satisfying the two uniform bounds: it has an `ℋ³`-limit `ginf` whose lift
  `F_* + ginf` solves the stationary equation.  That input is the paper's "compactness method"
  (tex 1578: "It now follows that `g` has a (unique) limit as `τ → ∞`; now it is easy to see
  that `\eqref{gEquationFinal}` has a unique `ℋ⁴` solution in `B_{Cα²}(0)`"): it is the only
  genuinely functional-analytic step of this chapter, and it is isolated here as a named
  input (see `NOTES.md`).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.Equation
import Submission.Work.Construction.Terms
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.Apriori
import Submission.Work.Construction.gronwall_exp_bound
import Submission.Work.Construction.le_of_deriv_le_of_cubic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- The family `τ ↦ g(·,·,τ)` of the fake-time flow, as a function of `(z,θ)`. -/
def gAt (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ => g z θ τ

/-- The scalar function whose differential inequality the a-priori estimate produces:
`τ ↦ |g(·,·,τ)|_{ℋ⁴}` (tex 1569-1570). -/
def gNorm (α : ℝ) (g : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ := fun τ => H4N α (gAt g τ)

/-- The differential inequality of tex 1569-1570 for the `ℋ⁴`-norm along the fake-time flow. -/
def EnergyIneq (α c C : ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ τ, 0 < τ → deriv (gNorm α g) τ ≤ -2 * c * gNorm α g τ
    + C * (α ^ 2 + Real.sqrt α * gNorm α g τ + α ^ (-(3 / 2 : ℝ)) * gNorm α g τ ^ 2
      + α ^ (-(5 / 2 : ℝ)) * gNorm α g τ ^ 3)

/-- The differential inequality of tex 1575-1577 for the `ℋ³`-norm of `∂_τg`
(keeping the modulation constants free: the coefficient is a *parameter* `c`). -/
def TimeDerivIneq (c : ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ τ, 0 < τ → deriv (fun s => Work.Spaces.HkNorm 0 3 (gdot g s)) τ
    ≤ -c * Work.Spaces.HkNorm 0 3 (gdot g τ)

/-- **The uniform bound `|g(·,·,τ)|_{ℋ⁴} ≤ y1`** (tex 1569-1572): if the `ℋ⁴`-norm of the
fake-time family satisfies the a-priori differential inequality and starts at `0`, and if the
cubic right hand side is negative at the level `y1` ("`α` sufficiently small"), then the norm
never exceeds `y1`; in the application `y1 = C₀α²` (the paper's `Cα²`). -/
theorem uniform_bound_of_energy {α c C y1 : ℝ} (hα : 0 < α) (hc : 0 < c) (hC : 0 < C)
    (hy1 : 0 < y1)
    (hF : -2 * c * y1 + C * (α ^ 2 + Real.sqrt α * y1 + α ^ (-(3 / 2 : ℝ)) * y1 ^ 2
        + α ^ (-(5 / 2 : ℝ)) * y1 ^ 3) < 0)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (gNorm α g) (Set.Ici 0))
    (hdiff : ∀ τ, 0 < τ → HasDerivAt (gNorm α g) (deriv (gNorm α g) τ) τ)
    (h0 : gNorm α g 0 ≤ 0)
    (henergy : EnergyIneq α c C g) :
    ∀ τ, 0 ≤ τ → gNorm α g τ ≤ y1 :=
  le_of_deriv_le_of_cubic hα hc hC hy1 hF hcont hdiff h0 henergy

/-- **The exponential decay of `∂_τg`** (tex 1577): the `ℋ³`-norm of `∂_τg` decays like
`K exp(-cτ)`, where `K` is its value at `τ = 0`. -/
theorem timeDeriv_decay {c K : ℝ} (hc : 0 < c) {g : ℝ → ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun τ => Work.Spaces.HkNorm 0 3 (gdot g τ)) (Set.Ici 0))
    (hdiff : ∀ τ, 0 < τ → HasDerivAt (fun s => Work.Spaces.HkNorm 0 3 (gdot g s))
      (deriv (fun s => Work.Spaces.HkNorm 0 3 (gdot g s)) τ) τ)
    (h0 : Work.Spaces.HkNorm 0 3 (gdot g 0) ≤ K)
    (hline : TimeDerivIneq c g) :
    ∀ τ, 0 ≤ τ → Work.Spaces.HkNorm 0 3 (gdot g τ) ≤ K * Real.exp (-(c * τ)) :=
  gronwall_exp_bound hc hcont hdiff hline h0

/-- **The compactness input** (tex 1578, "the compactness method"): for any fake-time family
`satisfying the two uniform bounds of the a-priori estimate — `|g(·,·,τ)|_{ℋ⁴} ≤ y1` and
`|∂_τg(·,·,τ)|_{ℋ³} ≤ K exp(-cτ)` — the family converges in `ℋ³` to a limit `ginf`, and the
lift `F_* + ginf` solves the stationary `g`-equation `\eqref{gEquationFinal}` with a stream
function `Phiinf`; moreover the limit obeys the same `ℋ⁴` bound.

This is the *only* genuinely functional-analytic step of this chapter (Riesz--Fischer /
completeness of the `ℋ³`-space together with the continuity of `N₀, N, N_*` in the limit).
It is stated here as a closed general proposition — the residual of this file — and is
recorded in `NOTES.md`. -/
def CompactnessInput (α μ lam y1 K c : ℝ) : Prop :=
  ∀ (Φ : ℝ → ℝ → ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ),
    IsTimeGSol α μ lam Φ g →
    (∀ τ, 0 ≤ τ → gNorm α g τ ≤ y1) →
    (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm 0 3 (gdot g τ) ≤ K * Real.exp (-(c * τ))) →
    ∃ (ginf Phiinf : ℝ → ℝ → ℝ),
      IsGSol α μ lam (fun z θ => Fstar α z θ + ginf z θ) ginf Phiinf ∧
        H4N α ginf ≤ y1 ∧
        Tendsto (fun τ => Work.Spaces.HkNorm 0 3 (fun z θ => g z θ τ - ginf z θ)) atTop (𝓝 0)

/-- **Existence of the stationary modulation** (tex 1578, conclusion of §Modulation): if the
fake-time equation holds, the a-priori bounds hold along the flow (with the level `y1` at which
the cubic right hand side is negative) and the compactness input is available, then
`\eqref{gEquationFinal}` has a solution `ginf` with `|ginf|_{ℋ⁴} ≤ y1`, and the fake-time family
converges to it in `ℋ³`.

The conclusion `IsGSol α μ lam (F_* + ginf) ginf Phiinf` is exactly the statement that the modulated
self-similar profile `F_* + ginf` solves the stationary equations (tex 1369 and (PolarBSLFinal)):
`Apriori.apriori_corollary` then supplies `|ginf|_{ℋ⁴} ≤ 2Cα²` when `y1 ≤ α^{7/4}`, which is the
input of the Stability layer. -/
theorem stationary_exists {α μ lam y1 K c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hcomp : CompactnessInput α μ lam y1 K c)
    {Φ : ℝ → ℝ → ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hsol : IsTimeGSol α μ lam Φ g)
    (hbound : ∀ τ, 0 ≤ τ → gNorm α g τ ≤ y1)
    (hdecay : ∀ τ, 0 ≤ τ → Work.Spaces.HkNorm 0 3 (gdot g τ) ≤ K * Real.exp (-(c * τ))) :
    ∃ (ginf Phiinf : ℝ → ℝ → ℝ),
      IsGSol α μ lam (fun z θ => Fstar α z θ + ginf z θ) ginf Phiinf ∧ H4N α ginf ≤ y1 := by
  obtain ⟨ginf, Phiinf, hgsol, hbdd, _⟩ := hcomp Φ g hsol hbound hdecay
  exact ⟨ginf, Phiinf, hgsol, hbdd⟩

end Work.Construction
