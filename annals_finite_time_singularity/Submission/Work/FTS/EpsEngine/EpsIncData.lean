/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/EpsIncData.lean` — the metric data of one Picard increment

`classC_step_of_flat` / `classC_step_of_profRHS_flat` (`EpsEngine/ClassCStep*.lean`) need three
metric-data clauses of the increment `epsInc α ρ ε Φs E g₀ n τ = ∫_0^τ Feps (slice (epsIter g₀ n) s) ds`:
`SmoothOpen`, `ℋ⁴`-honesty and `EpsMem`.  All three are *transfers* of the corresponding data of the
**slice** `slice (epsIter g₀ (n+1)) τ` and of the **datum** `g₀`, through the definitional identity

    slice (epsIter g₀ (n+1)) τ = g₀ + epsInc n τ          (`slice_epsIter_succ_eq`, by `rfl`) .

The engine supplies the slice data at the `(n+1)`-st level (its `SmoothOpen` clause
`SmoothOpenIterProd.smoothOpen_iter_succ_XBall_prefix`, the `ℋ⁴`-clause `H4Feps.HkMem_iter_feps`,
and the `EpsMem`/`EpsSq` clause `HkeepMetric`), so these three lemmas are the whole of item (3) of
`Eps4Thr/NOTES_EpsE4Thr_session23.md` §4.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EllipticEst.HkMem_sub_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The increment is the slice minus the datum** (pointwise rearrangement of
`slice_epsIter_succ_eq`). -/
theorem epsInc_eq_sub (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (n : ℕ) (τ : ℝ) :
    epsInc α ρ ε Φs E g₀ n τ
      = fun z θ => slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ z θ - g₀ z θ := by
  funext z θ
  have h := congrFun (congrFun (slice_epsIter_succ_eq α ρ ε Φs E g₀ n τ) z) θ
  rw [h]
  ring

/-- **The increment is smooth on the open quadrant** as soon as the `(n+1)`-st slice and the datum
are. -/
theorem smoothOpen_epsInc {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {τ : ℝ}
    (hslice : Work.FTS.EllipticEst.SmoothOpen (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hg₀ : Work.FTS.EllipticEst.SmoothOpen g₀) :
    Work.FTS.EllipticEst.SmoothOpen (epsInc α ρ ε Φs E g₀ n τ) := by
  rw [epsInc_eq_sub]
  exact hslice.sub hg₀

/-- **The increment is `ℋ⁴`-honest** as soon as the `(n+1)`-st slice and the datum are. -/
theorem hkMem_epsInc {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {τ : ℝ}
    (hslice : Work.FTS.EllipticEst.SmoothOpen (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hg₀ : Work.FTS.EllipticEst.SmoothOpen g₀)
    (hmemSlice : Work.Spaces.HkMem α 4 (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hmemg₀ : Work.Spaces.HkMem α 4 g₀) :
    Work.Spaces.HkMem α 4 (epsInc α ρ ε Φs E g₀ n τ) := by
  rw [epsInc_eq_sub]
  exact Work.FTS.EllipticEst.HkMem_sub_open hslice hg₀ hmemSlice hmemg₀

/-- **The increment is `EpsMem`-honest** as soon as the `(n+1)`-st slice and the datum are
(`AK` is the boundedness clause `EpsMem_sub` consumes). -/
theorem epsMem_epsInc {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {n : ℕ} {τ : ℝ}
    (hakSlice : Work.FTS.StrongEps.EpsSqTools.AK α (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hakg₀ : Work.FTS.StrongEps.EpsSqTools.AK α g₀)
    (hmemSlice : Work.FTS.StrongEps.EpsMem α (slice (epsIter α ρ ε Φs E g₀ (n + 1)) τ))
    (hmemg₀ : Work.FTS.StrongEps.EpsMem α g₀) :
    Work.FTS.StrongEps.EpsMem α (epsInc α ρ ε Φs E g₀ n τ) := by
  rw [epsInc_eq_sub]
  exact Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hakSlice hakg₀ hmemSlice hmemg₀

end Work.FTS.EpsEngine
