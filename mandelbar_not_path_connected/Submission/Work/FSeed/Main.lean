/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# `Work.FSeed.exists_rootParabolic`: a root-parabolic seed parameter exists

This is the target of the FSeed area (`NOTES_LEAD_mandelbar_EL_F_contracts.md` §9.5): a parameter
`c` of the tricorn at which the structure `Work.EL.RootParabolic` (declared in
`Submission/Work/ELTop/Defs.lean`, consumed by the EL areas and by the ELRig chain) is inhabited —
`T_c` has a *simple* parabolic cycle of exact period `5` carrying the two root rays `371/1023` and
`404/1023`, to which the critical orbit converges, with the wake condition.

## What is proved, and what is assumed

* **Step 1 (unconditional).** `Work.FSeed.exists_paramRay_limit` and
  `Work.FSeed.exists_paramRay_limit_α₁_paramRay` (`ParamRayLimit.lean`): the parameter ray at
  angle `θ` has a limit point `c ∈ Mb` which is not on the ray.
* **Step 2 (an input, shared with the Top glue).** `Work.FSeed.RepellingRayParamStable`
  (Goldberg–Milnor Lemma B.1; its dynamical form `RepellingRayStable`, false at parameters of
  `∂M*` and unused, was deleted), the reduction
  `Work.FSeed.not_isRepelling_of_mem_closure_paramRay`, the `hθ` clause
  `Work.FSeed.not_mem_closure_paramRay_paramAngle`, and the conclusion of Milnor 18.10 in the form
  `Work.FSeed.ParabolicLandingAtParamRay` (`Inputs.lean`).
* **Step 3 (proved from the input bundle).** `Work.FSeed.odd_period_five`,
  `Work.FSeed.per_half`, `Work.FSeed.mult_five`, `Work.FSeed.coLands_α₂`, `Work.FSeed.not_cusp`,
  `Work.FSeed.portrait_exact`, `Work.FSeed.rootParabolic_of_input`: the classical input bundle
  `Work.FSeed.RootParabolicInput` classifies the parabolic cycle — the odd period is exactly `5`,
  the second root ray co-lands, the period is exact, and the structure `Work.EL.RootParabolic` is
  produced.  (`Classify.lean`.)  The non-cusp condition `not_cusp` is *not* derived: it is the
  field `RootParabolicInput.simple`, a cited per-parameter classical fact
  (`NOTES_LEAD_mandelbar_seedsimple.md` §4.2); the ray-theoretic statement that would discharge it
  is `Work.FSeedSimple.CuspFixedRay`.  The portrait clause `portrait` is stated modulo `1`
  (`Int.fract`), which is the repair of the vacuity bug of `NOTES_LEAD_mandelbar_seedsimple.md` §1.
* **The numerical portrait** consumed by step 3 and by the EL areas: `Portrait/*.lean` (all
  proved, unconditional).

The single hypothesis `Work.FSeed.FSeedInput` collects the classical data of the root of the
non-real period-`5` hyperbolic component; see `Submission/Work/FSeed/Inputs.lean` for the exact
provenance of each field.

## Main results

* `Work.FSeed.exists_rootParabolic` — the target, conditional on `Work.FSeed.FSeedInput`.
* `Work.FSeed.exists_rootParabolic_at` — the same, with the parameter pinned to a limit point of
  the parameter ray `R(α₁)` and to the mandelbar.
* `Work.FSeed.exists_paramRay_limit`, `exists_paramRay_limit_α₁_paramRay` — step 1.
* `Work.FSeed.rootParabolic_of_input` — the classification (step 3), producing
  `Work.EL.RootParabolic`.
-/
import Submission.Work.FSeed.Defs
import Submission.Work.FSeed.RootParabolic
import Submission.Work.FSeed.Inputs
import Submission.Work.FSeed.Classify
import Submission.Work.FSeed.ParamRayLimit
import Submission.Work.FSeed.API.mem_Mandelbar
import Submission.Work.FSeed.API.mem_Mandelbar_input

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The FSeed deliverable.**  If the classical input bundle `Work.FSeed.FSeedInput` of the
root-parabolic parameter of the non-real period-`5` component holds, then there is a parameter `c`
carrying the structure `Work.EL.RootParabolic`: a simple parabolic period-`5` cycle with the root
rays `α₁`, `α₂`, an attracting critical orbit and the wake condition. -/
theorem exists_rootParabolic (h : FSeedInput) :
    ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c) := by
  obtain ⟨c, hne⟩ := h
  exact ⟨c, rootParabolic_of_input hne.some⟩

/-- **The target with the parameter pinned down.**  The seed parameter produced by the
classification is a parameter of the mandelbar which is a limit point of the parameter ray
`R(α₁)` and not on it — i.e. the parameter `c₁` of steps 1–2 of the route. -/
theorem exists_rootParabolic_at (h : FSeedInput) :
    ∃ c : ℂ, c ∈ Mandelbar ∧ c ∈ closure (Work.ParamRays.paramRay α₁) ∧
      c ∉ Work.ParamRays.paramRay α₁ ∧ Nonempty (Work.EL.RootParabolic c) := by
  obtain ⟨c, hne⟩ := h
  have hseed := hne.some
  refine ⟨c, ?_, hseed.mem_closure_paramRay, hseed.notMem_paramRay,
    rootParabolic_of_input hseed⟩
  exact Work.FSeed.API.mem_Mandelbar_input hseed

/-- The same statement with the classical input supplied as a named parameter and structure rather
than an existential. -/
theorem exists_rootParabolic_of (c : ℂ) (h : RootParabolicInput c) :
    ∃ c' : ℂ, Nonempty (Work.EL.RootParabolic c') :=
  ⟨c, rootParabolic_of_input h⟩

end Work.FSeed

end
