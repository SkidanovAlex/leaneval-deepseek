import Mathlib
import Submission.Work.Drive.ProjectiveDefs
import Submission.Work.Drive.exists_lift_cls_diskPlane
import Submission.Work.Drive.cutTransport
import Submission.Work.Drive.hcCartesian
import Submission.Work.Drive.SmoothArc.arcSystem_setup

/-!
# The cut of a disk-presented plane by a projective plane is the zero set of a lifted functional

The transport of `(SURF)` (`Submission/Work/Drive/cutTransportLevelSet.lean`) consumes, for each sweep
`V`, a `C^∞` *profile* `h` on the plane's parameter disk with

> `diskCut Q V = Work.Drive.SmoothArc.Zset h`

(plus the regularity and transversality clauses).  This file supplies the *algebraic half* of the
construction of that profile, in the form in which the design's geometry produces it: a plane of
`ℝ × ℝP³` is the projective plane `projLine (ker φ)` of a *non-zero functional* `φ` on `ℝ⁴`, and the
chart `Q` of the plane comes with a non-vanishing *lift* `V` of its class map
(`Work.Drive.exists_lift_cls_diskPlane`).  Then

> `class (Q x) ∈ projLine (ker φ)  ↔  φ (V x) = 0`,

so the profile is the *linear* function `x ↦ φ (V x)` of the lift — no distance function, no
partition of unity, and its smoothness and its derivative are those of the lift.

## What is proved here

| name | content |
| --- | --- |
| `Work.Drive.mem_projLine_ker_iff` | the dictionary: the class of a vector lies in the projective plane of `φ` iff `φ` kills it |
| `Work.Drive.projLine_inf_eq` | the projective plane of `φ ⊓ ψ` is the intersection of the two projective planes (so a *cut* of two planes is the projectivisation of the intersection of their kernels, i.e. a projective **line**) |
| `Work.Drive.contDiff_comp_lift` | `φ ∘ V` is `C^∞` when `V` is |
| `Work.Drive.fderiv_comp_lift`, `Work.Drive.fderiv_comp_lift_ne_zero` | its derivative is `φ ∘ dV`, non-zero as soon as `dV x` is not contained in `ker φ` |
| **`Work.Drive.exists_classCutProfile`** | **the packaged half**: for a smooth non-vanishing lift `V` of the class map of a disk presentation `Q` and a non-zero `φ`, the function `x ↦ φ (V x)` has zero set exactly the class-cut `{x | class (Q x) ∈ projLine (ker φ)}` |

The remaining half of the design's obligation (`diskCut Q V = Zset h`) is the *radius* bookkeeping of
the concrete chart — that the sweep `V` covers, at each class, exactly the radii realised in the disk
model — which is the design's own choice of the profile `bandTau`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Set

variable {n : ℕ}

/-- **The dictionary between a projective hyperplane and a functional.**  The class of a non-zero
vector `v` of `ℝ^{n+1}` lies in the projective hyperplane `projLine (ker φ)` if and only if `φ` kills
`v`.  (For `n = 3` this is the plane-cut `projLine (ker φ) ⊆ ℝP³`, for `n = 2` a projective line in
`ℝP²`.) -/
theorem mem_projLine_ker_iff (φ : Eucl n →L[ℝ] ℝ) {v : Eucl n} (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ projLine (LinearMap.ker (φ : Eucl n →ₗ[ℝ] ℝ)) ↔ φ v = 0 := by
  constructor
  · rintro ⟨w, hw0, hwU, hwP⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ v w hv hw0).mp hwP
    have hw0' : φ w = 0 := LinearMap.mem_ker.mp hwU
    rw [← ha]
    simp [hw0']
  · intro hv0
    exact ⟨v, hv, hv0, rfl⟩

/-- **The projective hyperplane of an intersection is the intersection of the projective hyperplanes.**
In particular the cut of two projective planes is projective again: `projLine (ker φ ⊓ ker ψ)` is a
projective *line* of `ℝP³`, the projectivisation of the `2`-dimensional `ker φ ⊓ ker ψ`. -/
theorem projLine_inf_eq {V : Type*} [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V) :
    projLine (U ⊓ W) = projLine U ∩ projLine W := by
  ext p
  constructor
  · rintro ⟨v, hv, hvU, rfl⟩
    exact ⟨⟨v, hv, hvU.1, rfl⟩, ⟨v, hv, hvU.2, rfl⟩⟩
  · rintro ⟨⟨v, hv, hvU, hpv⟩, ⟨w, hw, hwW, hpw⟩⟩
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ v w hv hw).mp (hpv.symm ▸ hpw)
    refine ⟨v, hv, ⟨hvU, ?_⟩, hpv⟩
    rw [← ha]
    exact W.smul_mem a hwW

/-- The composition of a continuous linear functional with a smooth map is smooth. -/
theorem contDiff_comp_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → Eucl n} (φ : Eucl n →L[ℝ] ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => φ (V x) :=
  φ.contDiff.comp hV

/-- The derivative of `x ↦ φ (V x)` is `φ ∘ dV x`. -/
theorem fderiv_comp_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Eucl n →L[ℝ] ℝ) {V : E → Eucl n} {x : E} (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => φ (V y)) x = φ.comp (fderiv ℝ V x) :=
  (φ.hasFDerivAt.comp x hV.hasFDerivAt).fderiv

/-- **The regularity of the profile.**  The derivative of `x ↦ φ (V x)` does not vanish at `x` as soon
as the image of `dV x` is not contained in `ker φ` — this is the immersion condition of the design's
lift, and it is what feeds the `hreg` hypothesis of the cut-transport chapter. -/
theorem fderiv_comp_lift_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Eucl n →L[ℝ] ℝ) {V : E → Eucl n} {x : E} (hV : DifferentiableAt ℝ V x)
    (h : ∃ w : E, φ (fderiv ℝ V x w) ≠ 0) :
    fderiv ℝ (fun y => φ (V y)) x ≠ 0 := by
  obtain ⟨w, hw⟩ := h
  intro hzero
  have h2 : (fderiv ℝ (fun y => φ (V y)) x) w = φ (fderiv ℝ V x w) := by
    rw [fderiv_comp_lift φ hV]
    rfl
  exact hw (by rw [← h2, hzero]; rfl)

/-- **The class-cut of a disk presentation is the zero set of a lifted functional.**  If `V` is a
non-vanishing lift of the class map of a plane presentation `Q` (as produced by
`Work.Drive.exists_lift_cls_diskPlane` from the smoothness of `Q`) and `φ` is a non-zero functional,
then reading the plane `projLine (ker φ)` in the chart gives exactly the zero set of `φ ∘ V`:
`x ↦ φ (V x)` is the *profile* of the cut by that plane. -/
theorem exists_classCutProfile {X : Type*}
    (Q : X → CappingSpace) (cls : X → Projectivization ℝ (Eucl 3))
    (hcls : ∀ x, cls x = (cappingSpaceHomeoProj (Q x)).2)
    (V : X → Eucl 3) (hVne : ∀ x, V x ≠ 0)
    (hlift : ∀ x, Projectivization.mk ℝ (V x) (hVne x) = cls x)
    (φ : Eucl 3 →L[ℝ] ℝ) :
    ∀ x, φ (V x) = 0 ↔ cls x ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) := by
  intro x
  rw [← hlift x]
  exact (mem_projLine_ker_iff φ (hVne x)).symm

/-- **The cut profile of a disk-presented plane, from the smoothness of the presentation.**  Combining
`Work.Drive.exists_lift_cls_diskPlane` (a smooth non-vanishing lift `V` of the class map of a disk
presentation, on any parameter box) with the dictionary above: the function `h := φ ∘ V` is a `C^∞`
profile on the box whose zero set is exactly the class-cut by the plane `projLine (ker φ)`, and whose
derivative is non-zero wherever the lift's differential is not contained in `ker φ` (the `hreg`
hypothesis of the cut-transport chapter). -/
theorem exists_cutProfile_of_diskPlane (Q : ℂ → CappingSpace)
    (hQ : letI := cappingCharted
      ContMDiff (modelWithCornersSelf ℝ ℂ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (φ : Eucl 3 →L[ℝ] ℝ) (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ x, V x ≠ 0) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        Projectivization.mk ℝ (V x) (hV x) = (cappingSpaceHomeoProj (diskPlane Q x)).2) ∧
      (∀ x, h x = φ (V x)) ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        (h x = 0 ↔ (cappingSpaceHomeoProj (diskPlane Q x)).2
          ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))) ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        (∃ w : EuclideanSpace ℝ (Fin 2), φ (fderiv ℝ V x w) ≠ 0) →
        fderiv ℝ h x ≠ 0) := by
  obtain ⟨V, hV, hVsm, hVlift⟩ := exists_lift_cls_diskPlane Q hQ a b c d hab hcd
  refine ⟨V, hV, fun x => φ (V x), hVsm, contDiff_comp_lift φ hVsm, hVlift, fun x => rfl, ?_, ?_⟩
  · intro x hx hx'
    show φ (V x) = 0 ↔ (cappingSpaceHomeoProj (diskPlane Q x)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
    rw [← hVlift x hx hx']
    exact (mem_projLine_ker_iff φ (hV x)).symm
  · intro x hx hx' hker
    exact fderiv_comp_lift_ne_zero φ ((hVsm.differentiable (by simp)) x) hker

/-- **The cut of a disk-presented plane by a sweep lies in the class-cut of a plane.**  The transport's
`diskCut Q V` is the set of disk parameters whose plane point lies in the *image of the sweep*, and a
sweep of a plane presentation `P` has at every parameter the class of `P` there
(`Work.Drive.cls_clampedSweep`).  Hence, whenever the class-image of the sweep's box lies in a
projective plane `projLine (ker φ)`, the cut lies in the corresponding class-cut:

> `diskCut Q V ⊆ {x | class (Q x) ∈ projLine (ker φ)}`.

This is the *inclusion* half of the design's `hVcut : diskCut Q V = SmoothArc.Zset h`, with
`h := φ ∘ V` the lifted-functional profile of `exists_cutProfile_of_diskPlane`.  The reverse inclusion
is the *radius* bookkeeping of the concrete chart (that the sweep reaches every class of the plane at
the radius realised in the disk model), which is the design's own choice of the profile `bandTau`. -/
theorem diskCut_subset_classCut {Q : ℂ → CappingSpace}
    {V : EuclideanSpace ℝ (Fin 3) → CappingSpace} {φ : Eucl 3 →L[ℝ] ℝ}
    (hV : ∀ x ∈ Submission.Drive.unitBox 2,
      (cappingSpaceHomeoProj (V x)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    diskCut Q V ⊆ {x | (cappingSpaceHomeoProj (Q (cplxOf x))).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))} := by
  rintro x ⟨-, y, hy, hxy⟩
  show (cappingSpaceHomeoProj (Q (cplxOf x))).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
  rw [← hxy]
  exact hV y hy

/-- **The seam symmetry of the class cut.**  On the boundary circle the disk presentation satisfies
`Q (-z) = Q z` (`IsPlaneChart`'s seam clause), hence the two lifts have the same projective class and
the profile `φ ∘ V` vanishes at `z` if and only if it vanishes at `-z`.  This is the bookkeeping that
makes the two endpoints of a cut an *antipodal pair* of the core — the `hpair` hypothesis of the
cut-transport chapter. -/
theorem zset_comp_lift_neg_iff {Q : ℂ → CappingSpace} (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {V : ℂ → Eucl 3} (hV : ∀ z, V z ≠ 0)
    (hlift : ∀ z, Projectivization.mk ℝ (V z) (hV z) = (cappingSpaceHomeoProj (Q z)).2)
    (φ : Eucl 3 →L[ℝ] ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    φ (V (-z)) = 0 ↔ φ (V z) = 0 := by
  have hseam : Projectivization.mk ℝ (V (-z)) (hV (-z)) = Projectivization.mk ℝ (V z) (hV z) := by
    rw [hlift (-z), hlift z, hQseam z hz]
  rw [← mem_projLine_ker_iff φ (hV (-z)), ← mem_projLine_ker_iff φ (hV z), hseam]

/-- **The cut is contained in the profile's zero set** — the proved half of the design's
`hVcut : diskCut Q V = SmoothArc.Zset h` (the other half is the level bookkeeping).  With the profile
`h := φ ∘ V'` built from the *lift* `V'` of the chart's class map (`exists_cutProfile_of_diskPlane`)
and the class-image of the sweep lying in the plane `projLine (ker φ)`, every point of the cut is a
zero of the profile inside the disk. -/
theorem diskCut_subset_zset_classProfile {Q : ℂ → CappingSpace}
    {V : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {V' : EuclideanSpace ℝ (Fin 2) → Eucl 3} (hV' : ∀ x, V' x ≠ 0)
    (hlift : ∀ x, Projectivization.mk ℝ (V' x) (hV' x)
      = (cappingSpaceHomeoProj (Q (cplxOf x))).2)
    {φ : Eucl 3 →L[ℝ] ℝ}
    (hsweep : ∀ x ∈ Submission.Drive.unitBox 2,
      (cappingSpaceHomeoProj (V x)).2 ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    diskCut Q V ⊆ SmoothArc.Zset (fun x : EuclideanSpace ℝ (Fin 2) => φ (V' x)) := by
  intro x hx
  have hcls := diskCut_subset_classCut hsweep hx
  have hzero : φ (V' x) = 0 :=
    (mem_projLine_ker_iff φ (hV' x)).mp (by rw [hlift x]; exact hcls)
  refine ⟨?_, hzero⟩
  rw [← norm_cplxOf x]
  exact hx.1

end Work.Drive
