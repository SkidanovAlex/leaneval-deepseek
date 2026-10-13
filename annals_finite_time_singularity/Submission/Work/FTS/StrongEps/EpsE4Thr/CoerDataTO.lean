/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/CoerDataTO.lean` — the base of the *transfer* induction on
the open class

`CoercivityFix/Transfer/CoerDataT.lean` defines the data of the transfer induction
(`CoerDataT`: Cauchy–Schwarz at level `n` on `RegQ`, coercivity of `𝓛_Γ^T` at level `n` on
`CoerAdm`) and its base case `coerDataT_one`, which uses the paper's Corollary
`FirstDerivativeCoercivity` (`Coer1T.coer1_LGammaT`) together with `Assembly.H1IP_cs_Q`.

This file ports the base to the open class `CoerDataTO` (defined in `StepDataO.lean`):

* the Cauchy–Schwarz half comes from `Transfer.H1IP_cs_of_mem`, which needs only
  `HkMem α 1 f` and `HkMem α 1 g` — so the bound holds *verbatim* on `RegQo α 1` (the `RegQ`-stated
  `Assembly.H1IP_cs_Q` is not needed at all);
* the coercivity half is the open-class level-one `FirstDerivativeCoercivity`,
  `Coer1Open.coer1_LGammaT_O` (proved this session), with the integrability bundle `IntPkgO α f`
  obtained from `IntPkg_O` and `regQo_mono`.

This is the base of the final route to the level-four `coer` clause of the `IP4` interface: the
route runs `Transfer/L4Main.transfer_level4`, whose level-`1` transfer data is exactly this base.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1Open
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkg_O
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-one Cauchy–Schwarz bound of `H1IP` on the open class.**  The frozen
`Assembly.H1IP_cs_Q` is stated on `RegQ α 1`; the sharp form
`Transfer.H1IP_cs_of_mem` needs only `HkMem α 1`, which `RegQo` supplies. -/
theorem H1IP_cs_Q_O : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → ∀ f g : Fn,
    RegQo α 1 f → RegQo α 1 g →
      |Work.Coercivity.H1IP α f g|
        ≤ C * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g :=
  ⟨10 ^ 22, by norm_num, fun α hα f g hf hg =>
    Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα f g hf.2.1 hg.2.1⟩

/-- **The base of the transfer induction on the open class**: the level-one `CoerDataTO` for
`H1IP`, with coercivity constant `1` (as in `Coer1T.ledger`) and the Cauchy–Schwarz constant
`10²²`. -/
theorem coerDataT_one_O :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      CoerDataTO α 1 (Work.Coercivity.H1IP α) 1 CC := by
  obtain ⟨C, hC, hcs⟩ := H1IP_cs_Q_O
  refine ⟨C, hC, fun α hα => ?_⟩
  refine
    { hcc := one_pos
      hCC := hC
      cs := fun f g hf hg => hcs α hα.1 f g hf hg
      coer := fun f hf => ?_ }
  have hreg : RegQo α 2 f := regQo_mono (by norm_num) hf.1
  have h := coer1_LGammaT_O hα.1 hα.2 hf (IntPkg_O hα.1 hreg)
  simpa using h

end Work.FTS.StrongEps.EpsE4Thr
