import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.standardCurve_one_one_simple

/-!
# The geometric core of the innermost-disc datum on the standard torus

`exists_innermostDisc_standardCurve` (the file `exists_innermostDisc_standardCurve.lean` in this
directory) asks for an `InnermostDisc standard S` whose boundary curve is the standard `(1,1)`-curve
`α`.  Apart from the two *proved* facts that `α` is simple (`standardCurve_one_one_simple`) and
essential (`standardCurve_essential`), the whole content is geometric, and it is isolated here:

  there is an injective continuous `e : 𝔻 → ℝ³` with `e|∂𝔻 = α`, together with **one**
  inessential simple closed curve `κ` of the standard torus whose range lies in `e(𝔻)` and which
  covers `e '' (open 𝔻) ∩ Σ`.

`DatumsCore` is exactly that statement.  Given it, the datum is assembled in
`exists_innermostDisc_standardCurve` by taking `S := Set.univ`, `ι := PUnit`, `curves := κ`,
and using the two proved facts above.

The shape of a witness (see `NOTES_design_session2.md`, same directory):

* `e '' (open 𝔻) ∩ Σ` is a union of two arcs, both running between `α(0)` and `α(π)` "parallel"
  to the anti-diagonal `t ↦ torusMap (t) (-t)` (so that the union of the two image arcs is a
  null-homotopic simple closed curve `κ`);
* the third region bounded by the two arcs and the arc `{α θ | θ ∈ [0,π]}` lies in the exterior
  of the torus, the others in the solid torus, so that the region homology conditions
  (`class (0,-1)`, `(0,0)`, `(1,0)`) are met;
* the map `e` is written in tube coordinates as `Ψ(Θ, ρ, Φ)` with `Θ` the azimuth, `ρ` the tube
  radius and `Φ` the tube angle; the interior intersection is exactly `{ρ = 1}` in the open disc.
  The `(π,-π)`-type difference of the arcs requires the tube angle's lift to pick up an extra
  `2π` along the arcs, which happens precisely when the image of the disc crosses the *core
  circle* `{R = 2, z = 0}` of the solid torus (where the tube angle is undefined), i.e. `ρ` must
  vanish somewhere inside the disc.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

/-- **The geometric core of the datum.**  An embedded (injective continuous) disc `e` spanning the
standard `(1,1)`-curve on the standard torus, together with a single inessential simple closed
curve `κ` of the torus whose range lies in the image of `e` and covers the intersection of the
*open* disc image with the torus. -/
def DatumCore : Prop :=
  ∃ e : C(Metric.closedBall (0 : ℂ) 1, R3),
    Function.Injective e ∧
    (∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) =
      (Work.CoreTopology.standardCurve 1 1).γ θ) ∧
    ∃ κ : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard,
      Work.CoreTopology.IsSimple Work.CoreTopology.standard κ ∧
      ¬ Work.CoreTopology.IsEssential Work.CoreTopology.standard κ ∧
      Set.range κ.γ ⊆ Set.range e ∧
      (∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 →
        e z ∈ Work.CoreTopology.standard.carrier → e z ∈ Set.range κ.γ)

end

end Work.Drive.EpsForm
