/-
# `Submission/Work/FTS/NonlinRows/` — the primed (open-quadrant) §8 rows

**Deliverable.**  Inhabit `Work.FTS.OpenPkg.N4Rows' IP α₂ Ci Ct Ce Cs` from
`Work.FTS.OpenPkg.N4Norm' Ci α₂` and `Work.FTS.OpenPkg.N4Extra' IP α₂ Ct`: the three row groups
`Work.FTS.Nonlinear.Pieces.N0Rows` (rows 1--7), `.NRows` (rows 8--26) and `.AuxRows`
(`rak`, `rl0`--`rl2`) in the **open-quadrant** vocabulary `StarPkgo`/`EllPkgGo`, together with
the three exact splits and the `ℋ⁴`-honesty table `Work.FTS.OpenPkg.PiecesHk`.

The consumer is `Work.FTS.OpenPkg.pairing_bound_open` (`hRows : N4Rows' …`).

See `NOTES_Rows.md` for the status, the per-row routes and the obstructions.

This module only fixes the *context abbreviation* `Ctx` used by the per-row statements of this
directory (so that each row can be delegated as a short statement) and re-exports the vocabulary.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The context of one §8 row**: the two primed interfaces fixed, and the six hypotheses on the
data (`0 < α ≤ min 1 α₂`, the Galerkin class of the perturbation `g`, and the two open-quadrant
elliptic packages of `Φs` and `Φg`).

This is the hypothesis list of `Work.FTS.OpenPkg.N4Rows'`'s three fields. -/
def Ctx (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop :=
  0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ Work.FTS.Nonlin.GalClass α g ∧
    Work.FTS.VocabO.StarPkgo α Cs Φs ∧ Work.FTS.VocabO.EllPkgGo α Ce g Φg

theorem Ctx.hα {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    0 < α := h.1

theorem Ctx.hα1 {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    α ≤ 1 := h.2.1

theorem Ctx.hαα₂ {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    α ≤ α₂ := h.2.2.1

theorem Ctx.hg {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    Work.FTS.Nonlin.GalClass α g := h.2.2.2.1

theorem Ctx.hs {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    Work.FTS.VocabO.StarPkgo α Cs Φs := h.2.2.2.2.1

theorem Ctx.hell {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h : Ctx α₂ Ci Ct Ce Cs α g Φs Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce g Φg := h.2.2.2.2.2

theorem Ctx.mk' {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn} (h1 : 0 < α) (h2 : α ≤ 1) (h3 : α ≤ α₂)
    (h4 : Work.FTS.Nonlin.GalClass α g) (h5 : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (h6 : Work.FTS.VocabO.EllPkgGo α Ce g Φg) : Ctx α₂ Ci Ct Ce Cs α g Φs Φg :=
  ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The three exact splits** of `N₀`, `N` and `N_*` (the `splits` field of
`Work.FTS.OpenPkg.N4Rows'`).  This is `Work.FTS.Nonlinear.Pieces.splits_of_diff` packaged with
the open-quadrant packages; the identity is claimed only on the open quadrant `Qd`, which is why
`SmoothOpen` suffices. -/
def SplitsData (α : ℝ) (g Φs Φg : Fn) : Prop :=
  (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ
          + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ
          + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ
          + Work.FTS.Nonlin.N06F α g z θ)) ∧
  (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
          + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
        + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
          + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
        + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
          + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
        + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
          + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
        + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
          + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ)) ∧
  (∀ μ : ℝ, μ ≠ -1 → ∀ z θ : ℝ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
      = Work.FTS.Nonlin.NstarLam μ g z θ)

end Work.FTS.NonlinRows
