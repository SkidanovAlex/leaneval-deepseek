/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/OpenLinear.lean` — the coercivity half of `hneg` in the
*open* class

`BarrierLinear.IP_dynLin_le` proves the dissipation inequality

  `IP α (dynLin α g τ) (slice g τ) ≤ - cc * HkSq α 4 (slice g τ)`

(the linear part of the level-four barrier's `hneg`) from the frozen `UnifIP` and the frozen class
`CoerAdm`, plus the extra hypothesis `RegQ α 4 (𝓛_Γ^T x)`.  Both `RegQ`-hypotheses carry
`LocData.SmoothQuad`, which — as `EpsE4Thr/CoerAdmSlice.lean` records — is *not* available along
the route.

This file is the open-class version: the same inequality, with `UnifIPO` and `RegQo`/`CoerAdmO`
in place of `UnifIP` and `RegQ`/`CoerAdm`.  The only hypothesis that remains is the honest
open-class regularity of the operator's output,

  `RegQo α 4 (𝓛_Γ^T x)`,

i.e. `SmoothOpen`, `HkMem α 4` and `BdryTraces α 4` of `𝓛_Γ^T x` (the first two are available in
the tree — `EpsZero.ClassCHk.LGammaTMem` for the honesty and `dynLin`'s explicit formula for the
smoothness; the traces are the open-class residue).

Everything here is `sorry`-free.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The linear part of the scheme is minus the frozen operator**: `dynLin α g τ` is the pointwise
negative of `𝓛_Γ^T α (slice g τ)` (definitional, after unfolding `dynLin`). -/
theorem dynLin_eq_neg_LGammaT (α : ℝ) (g : Fam) (τ : ℝ) :
    Work.FTS.Galerkin.dynLin α g τ
      = fun z θ => - Work.Coercivity.LGammaT α (slice g τ) z θ := by
  funext z θ
  simp only [Work.FTS.Galerkin.dynLin]

/-- **The coercivity half of `hneg`, in the open class.**  Identical to `IP_dynLin_le` with
`UnifIPO`/`RegQo` in place of `UnifIP`/`RegQ`; the hypothesis `RegQo α 4 (𝓛_Γ^T x)` is the
open-class regularity of the operator's output (interface item (V′)). -/
theorem IP_dynLin_le_open {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {g : Fam} {τ : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hcoer : CoerAdmO α (slice g τ))
    (hregL : RegQo α 4 (Work.Coercivity.LGammaT α (slice g τ))) :
    IP α (Work.FTS.Galerkin.dynLin α g τ) (slice g τ)
      ≤ - cc * Work.Spaces.HkSq α 4 (slice g τ) := by
  have hregx : RegQo α 4 (slice g τ) := hcoer.regQoFour
  have hsmul := hIP.smul_fst α hα (-1) (Work.Coercivity.LGammaT α (slice g τ)) (slice g τ)
    hregL hregx
  have hfun : (fun z θ => (-1 : ℝ) * Work.Coercivity.LGammaT α (slice g τ) z θ)
      = Work.FTS.Galerkin.dynLin α g τ := by
    rw [dynLin_eq_neg_LGammaT]
    funext z θ
    ring
  rw [hfun] at hsmul
  have hcoer' := hIP.coer α hα (slice g τ) hcoer
  rw [hsmul]
  linarith

end Work.FTS.StrongEps.EpsE4Thr
