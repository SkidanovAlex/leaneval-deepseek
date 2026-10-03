import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Measurability

/-!
# Port helper (Lean v4.35 / Mathlib 5e0c4e5)

Since Mathlib's change making `eLpNorm f p μ = ∞` for non-`AEStronglyMeasurable` `f`, several
`eLpNorm` lemmas (`eLpNorm_mono`, `eLpNorm_eq_lintegral_rpow_enorm_toReal`, ...) take a measurability
hypothesis.  `pw_aesm` discharges it in the situations that occur in this development.
-/

open Lean Elab Tactic Meta in
/-- Add `AEStronglyMeasurable` facts derived from the `MemLp` / `AEMeasurable` / `Measurable` /
`StronglyMeasurable` hypotheses in the local context. -/
elab "pw_aesm_ctx" : tactic => withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some c := ty.getAppFn.constName? | continue
    let lem? : Option Name :=
      if c == ``MeasureTheory.MemLp then some ``MeasureTheory.MemLp.aestronglyMeasurable
      else if c == ``AEMeasurable then some ``AEMeasurable.aestronglyMeasurable
      else if c == ``Measurable then some ``Measurable.aestronglyMeasurable
      else if c == ``MeasureTheory.StronglyMeasurable then
        some ``MeasureTheory.StronglyMeasurable.aestronglyMeasurable
      else none
    let some lem := lem? | continue
    let h ← Term.exprToSyntax ldecl.toExpr
    try evalTactic (← `(tactic| have := $(mkIdent lem) $h)) catch _ => pure ()

/-- Discharge an `AEStronglyMeasurable f μ` side condition. -/
macro "pw_aesm" : tactic => `(tactic| first
  | exact MeasureTheory.AEStronglyMeasurable.of_discrete
  | assumption
  | exact (MeasureTheory.SimpleFunc.stronglyMeasurable _).aestronglyMeasurable
  | fun_prop
  | (apply AEMeasurable.aestronglyMeasurable; first | assumption | fun_prop)
  | (apply MeasureTheory.StronglyMeasurable.aestronglyMeasurable; first | assumption | fun_prop)
  | (apply Measurable.aestronglyMeasurable; first | assumption | fun_prop)
  | (pw_aesm_ctx; fun_prop)
  | measurability)
