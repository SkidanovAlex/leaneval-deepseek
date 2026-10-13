/-
# N4 — the common context of the per-piece rows (design §3.4) — **REPAIRED**

The 26 rows of the design's table are inequalities for the concrete functions of `Defs.lean`,
under the *same* list of hypotheses.  `RowCtx` collects that list once, so that every row (or
group of rows) can be stated briefly.

This file replaces the earlier `RowCtx`, which was built on the unsatisfiable `N4RegQ` (see the
module docstring of `Interface.lean`).  The new context is

* the norm-level interface `N4Norm Ci α₂` (whose fields are true statements about the paper's
  function spaces);
* the `IP`-level interface `N4Extra IP α₂ Ct`;
* the two elliptic packages `StarPkg α Cs Φs` (N3) and `EllPkgG α Ce g Φg` (N1);
* the Galerkin class `GalClass α g` of the perturbation and the ranges `0 < α`, `α ≤ 1`,
  `α ≤ α₂`.

`RegQ α 4 g` (needed by `N4Extra`'s clauses) is *derived* from `GalClass α g` by
`galClass_regQ4` below, using the proved `Work.FTS.GalerkinFix.RegQ.regQ_mono`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `GalClass α g` gives `RegQ α 4 g` (`regQ_mono`). -/
theorem galClass_regQ4 {α : ℝ} {g : Fn} (h : GalClass α g) : RegQ α 4 g :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono h.reg (by norm_num)

/-- **The context of the per-piece estimates.**  `IP` is the concrete `ℋ⁴`-inner product with
its transport interface `N4Extra`, `N4Norm` carries the norm-level facts, `α ∈ (0, min α₂ 1]`
is the small parameter, and `g`, `Φs`, `Φg` are the perturbation and the two stream functions
of `StarPkg`/`EllPkgG`. -/
structure RowCtx (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop where
  hCi : 0 < Ci
  hN : N4Norm Ci α₂
  hE : N4Extra IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hg : GalClass α g
  hs : StarPkg α Cs Φs
  hell : EllPkgG α Ce g Φg

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn}

/-- The pieces of the context, extracted once. -/
theorem RowCtx.reg4 (h : RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : RegQ α 4 g :=
  galClass_regQ4 h.hg

theorem RowCtx.hαIoc (h : RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩

theorem RowCtx.hregQ (h : RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg) : 0 < α₂ := h.hN.pos.2

end Work.FTS.Nonlin
