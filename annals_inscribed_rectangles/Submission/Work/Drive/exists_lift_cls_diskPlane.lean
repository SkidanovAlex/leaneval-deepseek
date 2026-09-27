import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.exists_nonvanishing_lift_projCharted

/-!
# A smooth nonvanishing lift of the class map of a disk-presented plane

`Work.Drive.diskPlane Q : ℝ² → CappingSpace` is the folded square presentation of a plane
`Q : ℂ → CappingSpace` (`Submission/Work/Drive/planeChain.lean`), and
`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`
(`Submission/Work/Drive/exists_cappingModel_projectivization.lean`) reads off its "class": the second
coordinate `(cappingSpaceHomeoProj (diskPlane Q x)).2 ∈ ℝP³` is the projective class of the plane at
the point `x` of the parameter square.

This file shows that this class map, restricted to any closed box `[a,b] × [c,d]` with `a < b`,
`c < d`, is `C^∞` and therefore -- by `Work.Drive.exists_nonvanishing_lift_projCharted`
(`Submission/Work/Drive/exists_nonvanishing_lift_projCharted.lean`) -- admits a *global* `C^∞`,
nowhere vanishing vector-valued lift `V : ℝ² → ℝ⁴` whose projective class agrees with it on the box.

The smoothness reduces, through the transport lemmas of
`Submission/Work/Drive/chartedStructure_contMDiffWithinAt.lean` (the structure `cappingCharted` on
`CappingSpace` is `halfLineProjectiveCharted` pushed forward along `cappingSpaceHomeoProj.symm`) and
`Work.Drive.contMDiffAt_halfLineProjective_iff` (smoothness into `(0,∞) × ℝP³` is smoothness of the
two components), to the smoothness `Work.Drive.contMDiff_diskPlane` of the disk presentation itself.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

set_option linter.style.haveILetI false

/-- The class map of a disk-presented plane has a globally smooth, nowhere vanishing lift on any box. -/
theorem exists_lift_cls_diskPlane
    (Q : ℂ → CappingSpace)
    (hQ : letI := cappingCharted
      ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ x, V x ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        Projectivization.mk ℝ (V x) (hV x) = (cappingSpaceHomeoProj (diskPlane Q x)).2 := by
  -- the transparent smooth structure of the capping space, and smoothness of the disk presentation
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  haveI : IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) CappingSpace := isManifold_cappingCharted
  have hQ' : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q := hQ
  have hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diskPlane Q) :=
    contMDiff_diskPlane hQ'
  -- the transparent projective structure on `ℝP³`, through which the class map is read
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  haveI : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3)) :=
    isManifold_projCharted 3
  -- the class map is globally `C^∞`
  have hcls : ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (diskPlane Q x)).2) := by
    intro x
    -- `cappingCharted` is `halfLineProjectiveCharted` transported along `cappingSpaceHomeoProj.symm`
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3)) := halfLineProjectiveCharted
    have hG : ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => cappingSpaceHomeoProj (diskPlane Q w)) x := by
      have hiff := chartedStructure_contMDiffWithinAt
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
        (M := Set.Ioi (0:ℝ) × Projectivization ℝ (Eucl 3))
        (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        cappingSpaceHomeoProj.symm (diskPlane Q) Set.univ x
      exact hiff.mp (hP.contMDiffAt)
    -- smoothness into `(0,∞) × ℝP³` is smoothness of the second component
    exact ((contMDiffAt_halfLineProjective_iff
      (fun w => cappingSpaceHomeoProj (diskPlane Q w)) x).mp hG).2
  -- the nonvanishing lift of a smooth class map on a box
  obtain ⟨V, hV, hVdiff, hVcls⟩ :=
    exists_nonvanishing_lift_projCharted a b c d hab hcd
      (h := fun x : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (diskPlane Q x)).2)
      hcls.contMDiffOn
  exact ⟨V, hV, hVdiff, hVcls⟩

end Work.Drive
