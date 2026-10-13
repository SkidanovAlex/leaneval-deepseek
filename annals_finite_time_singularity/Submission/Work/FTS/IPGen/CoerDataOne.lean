/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/CoerDataOne.lean` — the level-1 clean data of `H1IP`, discharged

`Work.FTS.CoercivityFix.Assembly.CoerData2 α n IP cc CC` is the level-`n` package of the
corrected induction: Cauchy–Schwarz against the honest `ℋ^n`-norm on `RegQ α n`, and coercivity
of the clean operator `Lhat` at level `n` on `RegQ α (n+1)`.

The headline `CoercivityFix.Transfer.headline_of_errors` takes
`hCD₁ : ∀ α ∈ (0, 1/10^14], CoerData2 α 1 (H1IP α) 2 CC₁` as one of its five open obligation
families (the audit `FTS_INTEGRATION_AUDIT.md` §2 lists it as open).  It is in fact *already*
available: the two clauses are the proved lemmas

* `CoercivityFix.Assembly.H1IP_cs_Q` — `|H1IP α f g| ≤ 10^22 · |f|_{ℋ¹}·|g|_{ℋ¹}` on
  `RegQ α 1`, for every `α > 0` (this is the `cs` clause with `CC₁ = 10^22`);
* `CoercivityFix.Coer1.coer1_Lhat` — `2·|f|²_{ℋ¹} ≤ H1IP α (Lhat f) f` on `RegQ α 2`, for
  `α ∈ (0, 1/4]` (this is the `coer` clause with `cc = 2`).

Hence `hCD₁` holds with `CC₁ = 10^22`; the only range restriction is `α ≤ 1/4`, which contains
the interval `(0, 1/10^14]` used by the headline.

This removes one of the five obligation families of `headline_IP4_of_errors` / of
`CoercivityFix.Transfer.headline_of_errors`; the remaining four (`hE1`, `hE2`, `hok₁`, `hok₂`,
`hok₃`) involve the transfer defects `E1`, `E2` and belong to the `CoercivityFix` layer.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q
import Submission.Work.FTS.CoercivityFix.Coer1.coer1_Lhat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-1 clean data of `H1IP`**, i.e. the headline's `hCD₁` obligation:
`CoerData2 α 1 (H1IP α) 2 CC₁` for every `α ∈ (0, 1/10^14]`, with the explicit constant
`CC₁ = 10^22` (the Cauchy–Schwarz constant of `H1IP_cs_Q`) and coercivity constant `2`
(`coer1_Lhat`). -/
theorem coerData2_one_H1IP :
    ∃ CC₁ : ℝ, 0 < CC₁ ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      Work.FTS.CoercivityFix.Assembly.CoerData2 α 1 (Work.Coercivity.H1IP α) 2 CC₁ := by
  obtain ⟨C, hC, hcs⟩ := Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q
  refine ⟨C, hC, ?_⟩
  intro α hα
  refine { hcc := by norm_num, hCC := hC, cs := ?_, coer := ?_ }
  · intro f g hf hg
    exact hcs α hα.1 f g hf hg
  · intro f hf
    exact Work.FTS.CoercivityFix.Coer1.coer1_Lhat α hα.1
      (le_trans hα.2 (by norm_num : (1 : ℝ) / 10 ^ 14 ≤ 1 / 4)) hf

end Work.FTS.IPGen
