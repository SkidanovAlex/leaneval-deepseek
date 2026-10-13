/-
# `Work.ConstructionInstance.ModulatedData` — the **modulated-box interface**

This module isolates the *analytic core* of the construction instantiation: the fields that the
`St0`–`St3` dynamic-modulation bootstrap delivers about the self-similar vorticity `ω` and the
modulation `λ̄`, **after** the two steps that turn a *profile* into a *box*:

* `hBdd` — `λ̄(t)·‖ω(y,t)‖ ≤ M`: the `L^∞` box in the **self-similar** variable.  It is *not*
  uniform in `t`: the honest vorticity blows up like `1/λ̄(t)` (`Boxes.lam_mul_norm_le_of_ansatz`),
  which is why the delivered `Work.SolutionDelivery.ConstructedSolution` field `hBdd`
  (time-independent on the two-sided window) is *refutable* — `Obstruction.lean`;
* `hBddDt` — `λ̄(t)²·‖∂ₜω(y,t)‖ ≤ M₁`: the same box for the time derivative, with the honest
  weight `λ̄²` produced by differentiating the ansatz
  (`lam_sq_timeDeriv_le_Ioo` / `lam_sq_timeDeriv_le`);
* `hansatz` — `∃ x, c₀α ≤ λ̄(t)‖ω(x,t)‖`: the `St5` lower bound, i.e. `‖ω(·,t)‖_∞ ≳ 1/λ̄(t)` — the
  *other half* of the blow-up, and the reason a time-independent box cannot coexist with `St5`.

## Why this is the right interface

`not_lam_pos_extWindow` proves that the two-dimensional family

>`λ̄ > 0` on the extended window`, `λ̄(t) ≤ 2(T-t)` on `[0,T)`, `λ̄` differentiable at `T`

is empty; consistently, **every** field below is stated on the half-open window
`Ioo (-2) T = extWindow T ∩ (-∞,T)`, i.e. on the times *before* the maximal time, where the
self-similar description is meaningful.  `Modulated.inhabited` exhibits an explicit inhabitant
(`λ̄(t) = (T-t)/2`, `ω` the exact self-similar field of the perturbation `g = 0`), so the interface
is not vacuously satisfiable-shaped.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-- **The modulated-box interface**: the `St0`–`St3` output about `(λ̄, ω)`, on the times before
the maximal time `T`, in the *self-similar* weighting.

* `hlam`/`hlam_le`/`hlam_low` — `0 < λ̄(t)`, `λ̄(t) ≤ 2(T-t)` and `(T-t)/2 ≤ λ̄(t)` for `t < T`
  (`St0`'s `κ ≤ 2` and its matching lower bound; the lower bound is what makes the weighted box
  equivalent to a *strip* bound, `strip_bdd_of_repaired`);
* `hlamd` — the rate bound `|λ̄'| ≤ 1/2` (the design's normalisation of `κ`);
* `hBdd`, `hBddDt` — the two self-similar boxes;
* `hansatz` — the `St5` lower bound.

Every field is a statement about the *physical* vorticity `ω : ℝ³ × ℝ → ℝ³` and the scalar `λ̄`;
nothing here refers to the profile `F = F_* + g`. -/
structure ModulatedData (α : NNReal) where
  /-- the blow-up time -/
  T : ℝ
  /-- `T > 0` -/
  hT : 0 < T
  /-- the self-similar `L^∞` constant -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the self-similar `L^∞` constant of `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the `St5` constant -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- the modulation `λ̄` -/
  lam : ℝ → ℝ
  /-- the physical vorticity -/
  ω : R3 → ℝ → R3
  /-- `λ̄ > 0` before the maximal time -/
  hlam : ∀ t ∈ preWindow T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` (`St0`, `κ ≤ 2`) -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- `(T-t)/2 ≤ λ̄(t)` (the matching lower bound of the design) -/
  hlam_low : ∀ t ∈ Set.Ico 0 T, (T - t) / 2 ≤ lam t
  /-- the rate bound `|λ̄'| ≤ 1/2` -/
  hlamd : ∀ t ∈ preWindow T, |deriv lam t| ≤ 1 / 2
  /-- **the `L^∞` box in the self-similar variable** -/
  hBdd : ∀ t ∈ preWindow T, ∀ y : R3, lam t * ‖ω y t‖ ≤ M
  /-- **the box for `∂ₜω`**, with the honest `λ̄²` weight -/
  hBddDt : ∀ t ∈ preWindow T, ∀ y : R3,
    (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁
  /-- **`St5`**: somewhere the vorticity is as large as `c₀α/λ̄(t)` -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖

end Work.ConstructionInstance
