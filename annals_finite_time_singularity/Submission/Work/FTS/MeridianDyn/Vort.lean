/-
# `Work.FTS.MeridianDyn.Vort` — the meridian equation implies the `ℝ³` vorticity equation

Deliverable item 5 of the design's §3 list: the transport of the meridian (scalar) equation back to
the `ℝ³` vorticity equation on the open set `Uax` (the complement of the axis and of the equatorial
plane, where the meridian coordinates are regular) and on the time window `(0,T)`.

The reader should note the division of labour: the *pointwise* computation (the two directional
derivatives of the swirl field against the stream-function velocity, and the reading of the curl
equation at a point of `Uax`) is delivered by the sibling area `Work.FTS.FireFix`
(`Work.FTS.FireFix.vorticityEquationOn_of_meridianEqOn`, which consumes
`Work.FTS.MeridianDyn.MeridianEqOn`); the statement below records it in the vocabulary of this area
and in the (slightly stronger) hypothesis shape produced by the reconstruction, so that a caller
who has the meridian equation only in the form used here needs no detour.

`VorticityEquationAt` / `VorticityEquationOn` are the `t`-sliced forms of
`Work.LWP.VorticityEquation`; the equivalence with the unsliced predicate is
`Work.FTS.MeridianDyn.vorticityEquation_iff_forall_at`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.FireFix.VortEqLocal
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-- **The meridian equation gives the `ℝ³` vorticity equation on `Uax`.**  From the meridian
scalar equation on the window `(0,T)` and the differentiability of the meridian pair off the axis,
the stream-function velocity and the swirl vorticity satisfy the `ℝ³` vorticity equation at every
`x ∈ Uax` and every `t ∈ (0,T)`.

The hypotheses are the form in which the reconstruction supplies them (`hW`, `hΨ` for all `t` off
the axis); the conclusion is the pointwise equation on `Uax`, i.e. the exact content of the
`VorticityEquation` clause of `Work.FTS.Physical.BlowupAt` on the window. -/
theorem vorticityEquationOn_of_meridianOn {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hΨ : ∀ t r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2 t) (r, z))
    (hme : MeridianEqOn W ψ T) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      timeDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + directionalDeriv
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
            (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x) x t
        = directionalDeriv (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t :=
  Work.FTS.FireFix.vorticityEquationOn_of_meridianEqOn hme
    (fun t ht r z hr _ => hW t r z hr)
    (fun t ht r z hr _ => hΨ t r z hr)

end Work.FTS.MeridianDyn
