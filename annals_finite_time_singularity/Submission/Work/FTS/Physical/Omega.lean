/-
# `Work.FTS.Physical.Omega` — the physical vorticity read through the extended inverse clock

The physical vorticity of node N8's reconstruction is node N7's field `physVort α A B g` evaluated
at the *physical* time through the extended inverse clock `Work.FTS.Physical.clockInv`:

  `physOmega α A B g C x t = physVort α A B g x (clockInv C t)`.

This module is deliberately small: it holds the definition together with the `ℝ≥0`/`ℝ` bridge used to
pass between the exponent of the reconstruction (`α : ℝ≥0`) and the real-valued `RegPkg` parameter,
so that the firing theorem (`Physical/RegPkgFire.lean`) and the meridian reduction
(`Physical/Meridian.lean`) can share it without a circular import.
-/
import Mathlib.Basic.ENNReal.Basic
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.clockInv
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical

open PhysClock

/-- The `ℝ≥0` element `⟨(α : ℝ), h⟩` with `α : ℝ≥0` is `α` itself.  Used to pass between the
`ℝ≥0` exponent of the reconstruction and the real-valued `RegPkg` parameter. -/
theorem nnreal_mk_coe_eq (α : ℝ≥0) {h : 0 ≤ (α : ℝ)} : (⟨(α : ℝ), h⟩ : ℝ≥0) = α :=
  Subtype.ext rfl

/-- **The physical vorticity of a `RegPkg` profile, read through the extended inverse clock.**
This is node N7's field `physVort α A B g` at the physical time `t`: the fake-time variable is
`τ = clockInv C t`. -/
noncomputable def physOmega (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (C : PhysClock) :
    R3 → ℝ → R3 :=
  fun x t => Work.FTS.Regularity.physVort α A B g x (clockInv C t)

theorem physOmega_apply (α : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) (C : PhysClock)
    (x : R3) (t : ℝ) : physOmega α A B g C x t = Work.FTS.Regularity.physVort α A B g x (clockInv C t) :=
  rfl

end Work.FTS.Physical
