import Mathlib
import Submission.Work.Drive.classTripleAssembly
import Submission.Work.Drive.exists_nonvanishing_lift_projCharted

/-!
# `L5` in the design's exact form: the lifts are derived, not assumed

`Work.Drive.exists_small_classTripleRegular` (`Submission/Work/Drive/classTripleAssembly.lean`)
produces, for every `ε > 0`, a small per-chain perturbation `A` of the classes of three plane
presentations with `ClassTripleRegular (linCapping (A k) ∘ P k)` — but it takes as hypotheses, besides
the smoothness/seam/immersion data of the `P k`, a **non-vanishing smooth lift `V k` of the class map
of each `P k`** (with its class identity on the unit box).

The design never supplies those lifts: it only supplies the presentations.  This file removes the
hypotheses `V`, `hVne`, `hVsmooth`, `hVcls` by deriving them from the smoothness `hP` alone, through

* `Work.Drive.contMDiffAt_cls_of_contMDiff` — the *global* smoothness form of the workspace's
  `mdifferentiableAt_cls_of_contMDiff`: the class map `y ↦ (cappingSpaceHomeoProj (P y)).2` is `C^∞`
  where `P` is (`ℝ² → CappingSpace` → `ℝP³`);
* `Work.Drive.contMDiffOn_cls_of_contMDiff_box` — the box form, which is exactly the hypothesis of
  `Work.Drive.exists_nonvanishing_lift_projCharted` with `[a,b] × [c,d] = [0,1]²`;
* `Work.Drive.exists_lift_cls_of_contMDiff` — hence a globally `C^∞`, nowhere vanishing lift `V` of the
  class map agreeing with it on the unit box (`Projectivization.mk ℝ (V y) _ = planeClassMap P y`);
* **`Work.Drive.exists_small_classTripleRegular'`** — the same conclusion as
  `exists_small_classTripleRegular`, with the four lift hypotheses gone.

The same lift-existence statement is what the *ends* lane needs (`Work.Drive.IsClassLift` of the chart's
class maps), so this file is the single place where "the class map of a smooth presentation has a
smooth non-vanishing lift on the box" is produced.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.style.haveILetI false

/-! ## 1. The class map is `C^∞` where the presentation is -/

/-- **The class map of a smooth plane presentation is `C^∞`.**  This is the `ContMDiffAt` form of
`Work.Drive.mdifferentiableAt_cls_of_contMDiff` (`Submission/Work/Drive/hcLinCappingManifold.lean`):
the class `y ↦ (cappingSpaceHomeoProj (P y)).2 ∈ ℝP³` is a component of the presentation read in the
transparent model `(0,∞) × ℝP³`, so its smoothness is componentwise smoothness
(`Work.Drive.contMDiffAt_halfLineProjective_iff`). -/
theorem contMDiffAt_cls_of_contMDiff {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) Ctop P) (y : EuclideanSpace ℝ (Fin 2)) :
    ContMDiffAt (𝓡 2) (𝓡 3) Ctop
      (fun y' => (cappingSpaceHomeoProj (P y')).2) y := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hG : ContMDiffAt (𝓡 2) (𝓡 4) Work.Drive.Ctop
      (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
      (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := Work.Drive.Ctop)
      Work.Drive.cappingSpaceHomeoProj.symm P Set.univ y
    exact hiff.mp (hP.contMDiffAt)
  exact ((Work.Drive.contMDiffAt_halfLineProjective_iff
    (fun w => Work.Drive.cappingSpaceHomeoProj (P w)) y).mp hG).2

/-- **The class map of a smooth plane presentation is `C^∞` on the unit box**, in exactly the form
consumed by `Work.Drive.exists_nonvanishing_lift_projCharted`. -/
theorem contMDiffOn_cls_of_contMDiff_box {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) Ctop P) :
    letI := Work.Drive.projCharted 3
    ContMDiffOn (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' => (cappingSpaceHomeoProj (P y')).2)
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc (0 : ℝ) 1 ∧ q 1 ∈ Set.Icc (0 : ℝ) 1} := by
  intro y hy
  exact (contMDiffAt_cls_of_contMDiff hP y).contMDiffWithinAt

/-! ## 2. The smooth non-vanishing lift on the box -/

/-- **A globally `C^∞`, nowhere vanishing lift of the class map of a smooth presentation, agreeing with
it on the unit box.**  The box is convex hence contractible, so the pulled-back tautological bundle is
trivial; the production of the global lift is
`Work.Drive.exists_nonvanishing_lift_projCharted` and the only input here is the box smoothness of the
class map. -/
theorem exists_lift_cls_of_contMDiff {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hP : ContMDiff (𝓡 2) (𝓡 4) Ctop P) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ y ∈ Submission.Drive.unitBox 1,
        Projectivization.mk ℝ (V y) (hV y) = planeClassMap P y := by
  obtain ⟨V, hV, hsm, hcls⟩ := Work.Drive.exists_nonvanishing_lift_projCharted 0 1 0 1
    (by norm_num) (by norm_num) (contMDiffOn_cls_of_contMDiff_box hP)
  exact ⟨V, hV, hsm, fun y hy => hcls y (by simpa using hy 0) (by simpa using hy 1)⟩

/-! ## 3. `L5` without the lift hypotheses -/

/-- **`L5` in the design's exact form.**  Given only the smoothness, the seam invariance and the
unperturbed immersion of the three plane presentations, there are arbitrarily small per-chain
perturbations `A k` of their projective classes with `ClassTripleRegular (linCapping (A k) ∘ P k)`.

This is `Work.Drive.exists_small_classTripleRegular` with its four lift hypotheses discharged by
`Work.Drive.exists_lift_cls_of_contMDiff`, so that the statement mentions the presentations alone. -/
theorem exists_small_classTripleRegular'
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (hci : ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2), (∀ k, openSquare (y k)) → ∀ k,
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (P k)) (mk2 (y k 0) (y k 1))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3,
      (∀ k, ‖(A k : Eucl 3 →L[ℝ] Eucl 3) - 1‖ < ε) ∧
      ClassTripleRegular (fun k => linCapping (A k) ∘ P k) := by
  choose V hVne hVsmooth hVcls using fun k => exists_lift_cls_of_contMDiff (hP k)
  exact exists_small_classTripleRegular P hP hPseam hci V hVne hVsmooth hVcls ε hε

end

end Work.Drive
