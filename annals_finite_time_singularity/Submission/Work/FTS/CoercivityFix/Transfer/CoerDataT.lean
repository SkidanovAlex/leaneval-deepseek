/-
# `Transfer/CoerDataT.lean` — the level package of the transfer induction

`Assembly.CoerData2 α n IP cc CC` packages the coercivity of the **clean** operator
`𝓛̂ = 𝓛 − Transport` (`coer` on `RegQ α (n+1)`) plus its Cauchy–Schwarz bound (`cs` on
`RegQ α n`).  This module defines the companion package for the paper's operator.

`CoerDataT α n IP cc CC` carries the *same* `cs` clause and, in place of `coer`, the
coercivity of `𝓛_Γ^T`:

  `cc · |f|²_{ℋⁿ} ≤ IP (𝓛_Γ^T f) f`   for `f ∈ CoerAdm α`.

The base case `n = 1` is the paper's Corollary `FirstDerivativeCoercivity` in the interior
class — `Coer1T.coer1_LGammaT` — and the induction from `n` to `n+1` is
`Transfer.stepT` (a modification of `Assembly.coer_clause_succ` in which the `D_θ`-slot and the
`D_z`-slot are each split off through the **clean** coercivity of `CoerData2` and the two
explicit defects `E1`, `E2` of `Transfer/Profiles.lean`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q
import Submission.Work.FTS.CoercivityFix.Coer1T.coer1_LGammaT

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false

/-- **The level-`n` data of the transfer induction**: the Cauchy–Schwarz bound of `IP` at
level `n` (on `RegQ α n`), together with the coercivity of the paper's operator `𝓛_Γ^T`
at level `n` on the thin class `CoerAdm`. -/
structure CoerDataT (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) (cc CC : ℝ) : Prop where
  /-- the coercivity constant is positive -/
  hcc : 0 < cc
  /-- the Cauchy–Schwarz constant is positive -/
  hCC : 0 < CC
  /-- Cauchy–Schwarz against the honest `ℋⁿ`-norm, on the level-`n` class -/
  cs : ∀ f g : Fn, RegQ α n f → RegQ α n g →
    |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g
  /-- coercivity of `𝓛_Γ^T` at level `n`, on the one-condition class `CoerAdm` -/
  coer : ∀ f : Fn, CoerAdm α f →
    cc * Work.Spaces.HkSq α n f ≤ IP (Work.Coercivity.LGammaT α f) f

/-- **The base case of the transfer induction** (`n = 1`): the paper's Corollary
`FirstDerivativeCoercivity` in the interior class, `Coer1T.coer1_LGammaT`, together with the
level-`1` Cauchy–Schwarz bound `Assembly.H1IP_cs_Q`.  The coercivity constant is `1`, as in
`Coer1T.ledger`. -/
theorem coerDataT_one :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      CoerDataT α 1 (Work.Coercivity.H1IP α) 1 CC := by
  obtain ⟨C, hC, hcs⟩ := Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q
  refine ⟨C, hC, fun α hα => ?_⟩
  exact
    { hcc := one_pos
      hCC := hC
      cs := fun f g hf hg => hcs α hα.1 f g hf hg
      coer := fun f hf => by
        simpa using Work.FTS.CoercivityFix.Coer1T.coer1_LGammaT α hα.1 hα.2 hf }

end Work.FTS.CoercivityFix.Transfer
