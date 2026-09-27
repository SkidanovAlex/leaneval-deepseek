import Mathlib
import Submission.Work.Drive.cutClassImage
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.sideOf_localconst_of_dichotomy
import Submission.Work.Drive.classImageGraphData

/-!
# The side function of the rotation family from profile data (linearity-free)

This file wires the *set-form* rigidity of `Submission/Work/Drive/cutClassImage.lean` to the route's
concrete side function `Work.Drive.sideOf` (the cut of the chart by the clamped sweep of the rotated
plane), and then wires the resulting bridge into the (linearity-free) local-constancy brick
`Work.Drive.sideOf_localconst_of_dichotomy`, whose structural hypotheses are discharged by
`Work.Drive.classImageGraphData`.

The point is that the *linear-plane* description of the chart's class image is never used: the class set
is the class image of the *swept* plane, connected for free.  What is left as an explicit hypothesis is
(★) the bridge (`sideOf … u = 1 ↔` the chart's profile below the swept plane's on that class image) and
the profile data that produces it.

## Contents

* `Work.Drive.sideOf_eq_one_iff_profile_of_classImage` — the bridge (★) for `sideOf` from the profile
  data of the chart and of the rotated plane;
* `Work.Drive.sideOf_eventually_eq_of_profileBridge` — **the local constancy (`hn4`) of the route's side
  function** on the non-collision set, from (★) and the non-vanishing of the profile difference at the
  base angle.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The bridge (★) for the route's side function, from profile data.**  If the chart's profile `FQ`
and the swept plane's profile `G` are continuous and have the prescribed values (`hFQval`, `hGval`), the
truncation bounds `hcne`/`hlev` hold, the two profiles differ on the swept plane's class image (`hne`,
the disjointness) and that class-cut is non-empty (`hccne`), then the side value is the profile
comparison:

> `sideOf Q c ψ u = 1 ↔ FQ < G` on `classImage (rotPresentation Q u)`.

This is `Work.Drive.diskCut_ne_empty_iff_profile_set` instantiated at the sweep `rotPresentation Q u`
with the class set `L := classImage (rotPresentation Q u)` — no linear plane appears. -/
theorem sideOf_eq_one_iff_profile_of_classImage (Q : ℂ → CappingSpace) (hQ : Continuous Q)
    (c : UnitAddCircle → ℝ) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcontψ : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (u : UnitAddCircle) (hc : 0 < c u)
    (FQ G : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQc : Continuous FQ) (hGc : Continuous G)
    (hFQval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      FQ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hGval : ∀ y ∈ Submission.Drive.unitBox 1,
      G ((cappingSpaceHomeoProj (rotPresentation Q u y)).2) = levelOf (rotPresentation Q u y))
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c u ≤ levelOf (Q z))
    (hlev : ∀ y ∈ Submission.Drive.unitBox 1, c u ≤ levelOf (rotPresentation Q u y))
    (hne : ∀ q ∈ classImage (rotPresentation Q u), FQ q ≠ G q)
    (hccne : classCutSet Q (classImage (rotPresentation Q u)) ≠ ∅) :
    sideOf Q c ψ u = 1 ↔
      ∀ q ∈ classImage (rotPresentation Q u), FQ q < G q := by
  have hP : Continuous (rotPresentation Q u) := continuous_rotPresentation Q hQ u
  have hbridge := diskCut_ne_empty_iff_profile_set Q (c u) hc ψ hψ0 hψ1 hψ01
    hcontψ (rotPresentation Q u) hlev (classImage (rotPresentation Q u))
    (fun y hy => ⟨y, hy, rfl⟩) (classImage (rotPresentation Q u))
    (fun x hx => hx.2) FQ G
    (fun x hx => hFQval (cplxOf x) hx.1)
    (fun x _ y hy hcls => le_of_eq (by rw [hcls, hGval y hy]))
    (fun x hx => by
      obtain ⟨y, hy, hcls⟩ := hx.2
      exact ⟨y, hy, hcls.symm, by rw [← hcls, hGval y hy]⟩)
    (fun x hx => hcne (cplxOf x) hx.1)
    (isPreconnected_classImage_of_continuous _ hP)
    ((hFQc.sub hGc).continuousOn) hccne (fun q hq => (hne q hq).symm)
  rw [sideOf_eq_one_iff]
  exact hbridge

/-- **The local constancy (`hn4`) of the route's side function, from the bridge (★).**  With (★) for
every angle and the non-vanishing of the profile difference at the base angle `u₀`, the side function is
locally constant at `u₀`.  The structural hypotheses of
`Work.Drive.sideOf_localconst_of_dichotomy` are discharged by `Work.Drive.classImageGraphData`
(closed graph, pointwise preconnectedness, pointwise non-emptiness); the class set is the class image of
the rotated plane, which is preconnected for free. -/
theorem sideOf_eventually_eq_of_profileBridge (Q : ℂ → CappingSpace) (hQ : Continuous Q)
    (c : UnitAddCircle → ℝ) (ψ : ℝ → ℝ)
    (FQ : Projectivization ℝ (Eucl 3) → ℝ) (G : UnitAddCircle → Projectivization ℝ (Eucl 3) → ℝ)
    (hGc : Continuous (Function.uncurry fun u q => FQ q - G u q))
    (u₀ : UnitAddCircle)
    (hne₀ : ∀ q ∈ classImage (rotPresentation Q u₀), FQ q - G u₀ q ≠ 0)
    (hval : ∀ u : UnitAddCircle, sideOf Q c ψ u = 1 ↔
      ∀ q ∈ classImage (rotPresentation Q u), FQ q - G u q < 0) :
    ∀ᶠ u in 𝓝 u₀, sideOf Q c ψ u = sideOf Q c ψ u₀ := by
  obtain ⟨hclosed, hpre, hne⟩ := classImageGraphData Q hQ
  exact sideOf_localconst_of_dichotomy (fun u => sideOf Q c ψ u)
    (fun u => classImage (rotPresentation Q u)) (fun u q => FQ q - G u q) u₀
    hclosed hGc hpre hne hne₀ hval

end

end Work.Drive
