import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsRLX/Defs.lean` — the interface of the `EpsRHSPLipXProof` development

* `Wp ρ ε u = Pz (Jeps ρ ε u)`: the projected-mollified profile at which the scheme's elliptic
  layer is evaluated.
* `ProfileData α C₀ B ε ρ u`: the bundle of hypotheses the target
  (`Work.FTS.StrongEps.EpsRHSPLipXProof`) assumes on a single admissible datum `u`.

Everything else (the product tools, the term-by-term bounds, the assembly) lives in the sibling
modules of this directory.
-/

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The projected-mollified profile `W_u = Pz (J_ε u)` at which the whole right-hand side of the
projected scheme is evaluated. -/
noncomputable def Wp (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (u : Fn) : Fn :=
  Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)

/-- The modulation block `-μ̄·AK + N_*` of the scheme's right-hand side at a single profile `W`
(all modulation constants evaluated at `W`, `Φ = Φs + E W`). -/
noncomputable def muBlock (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W : Fn) : Fn := fun z θ =>
  -(Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
      (Work.Construction.N α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + E W z θ))) * Work.Construction.AK α z θ
  + Work.Construction.Nstar
      (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
        (Work.Construction.N α (Work.Construction.Ftot α W)
          (fun z θ => Φs z θ + E W z θ)) W)
      (Work.Construction.lamfun
        (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
          (Work.Construction.N α (Work.Construction.Ftot α W)
            (fun z θ => Φs z θ + E W z θ)) W))
      W z θ

/-- **The datum of one admissible profile** of the projected `ε`-scheme: exactly the hypotheses
the target assumes at a single `(τ, u)`. -/
structure ProfileData (α C₀ B ε : ℝ) (ρ : ℝ × ℝ → ℝ) (u : Fn) : Prop where
  /-- open-quadrant smoothness of the datum -/
  smo : Work.FTS.EllipticEst.SmoothOpen u
  /-- honest `ℋ⁶`-membership -/
  hkmem : Work.Spaces.HkMem α 6 u
  /-- the `ℋ⁶`-size bound -/
  hknorm : Work.Spaces.HkNorm α 6 u ≤ B
  /-- the projected-mollified profile is of class `C` -/
  cls : Work.FTS.ClassC.ClassC α (Wp ρ ε u)
  /-- the small-ball bound on the projected-mollified profile -/
  xn : Work.FTS.Nonlin.Xn α (Wp ρ ε u) ≤ C₀ * α ^ 2

end Work.FTS.StrongEps.EpsRLX
