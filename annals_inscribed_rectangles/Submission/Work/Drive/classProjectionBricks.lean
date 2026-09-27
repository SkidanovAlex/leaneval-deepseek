import Mathlib
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.mfderiv_cls_surjective
import Submission.Work.Drive.clampedSweep

/-!
# Two reusable facts about the class projection `cls : CappingSpace → ℝP³`

The `hn2`/`hdense` lanes' class-level arguments push a spanning of two derivatives in the
`4`-dimensional capping space forward to the `3`-dimensional class tangent space, through the chain
rule for the class projection.  This file names the two facts those arguments reuse:

* `Work.Drive.contMDiff_shadow` — the shadow `p ↦ shadow c hc p` is `C^∞` on the capping space (so the
  chain rule applies to `shadow c hc ∘ V` for a smooth `V`);
* `Work.Drive.mfderiv_planeClassMap_eq_comp` — the chart-free chain rule for a plane's class map:
  `mfderiv (planeClassMap Q) y = (mfderiv cls (Q y)).comp (mfderiv Q y)`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartCP :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-- **The shadow is smooth.** -/
theorem contMDiff_shadow (c : ℝ) (hc : 0 < c) :
    ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop (fun p : Work.Drive.CappingSpace =>
      Work.Drive.shadow c hc p) :=
  fun p => contMDiffAt_shadow' c hc p

/-- **The class map of a plane presentation is the class projection after the presentation**, so its
manifold derivative is the composite of the two differentials (chart-free chain rule). -/
theorem mfderiv_planeClassMap_eq_comp
    (Q : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop Q) (y : EuclideanSpace ℝ (Fin 2)) :
    mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap Q) y
      = ((mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (Q y)).comp
          (mfderiv (𝓡 2) (𝓡 4) Q y)) := by
  have h1 : MDifferentiableAt (𝓡 4) (𝓡 3) Work.Drive.cls (Q y) :=
    (contMDiffAt_cls' (Q y)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt (𝓡 2) (𝓡 4) Q y :=
    hQ.contMDiffAt.mdifferentiableAt (by simp)
  have hfun : (Work.Drive.planeClassMap Q) = Work.Drive.cls ∘ Q := rfl
  rw [hfun]
  exact mfderiv_comp y h1 h2

end

end Work.Drive
