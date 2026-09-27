import Mathlib
import Submission.Work.Drive.diskPlane_mfderiv
import Submission.Work.Drive.contMDiffAt_projRot
import Submission.Work.Drive.sideValue

/-!
# The rotation transport of the immersion condition `hc`

The counting route (`Submission/Work/Drive/CHAIN_LEVEL_PLAN.md`, `Submission/Work/Drive/sideValue.lean`)
sweeps, for a triple `u 0, u 1, u 2` of angles, the three chains

`clampedSweep (c k) ψ (P k)`,  `P k = Work.Drive.rotPresentation Q (u k)`,

i.e. the plane of the *base chart* `Q` rotated by the angle `u k`.  The engine
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion` requires, at every triple
point, the **immersion condition** `hc`: the derivative of the projective class of `P k` is injective
(`Work.Drive.planeClassDeriv_injective_iff`), and the **general-position condition** `hV`.

This file supplies `hc` for the rotated presentations from `hc` of the base chart.  The point is that
the rotation of the capping space acts on the projective class *only*:

`cappingSpaceHomeoProj (rotCapping t p) = ((cappingSpaceHomeoProj p).1, projRot t ((cappingSpaceHomeoProj p).2))`

(`Work.Drive.cappingSpaceHomeoProj_rotCapping`), so the class map of the rotated plane is the class map
of the base plane composed with `Work.Drive.projRot t` (the projectivisation of the diagonal rotation
`diagRot t` of `ℂ² = ℝ⁴`), and the derivative is a *composite of two injective linear maps*.

The rotation of `ℝP³`

* is an action (`Work.Drive.projRot_add_apply`, `Work.Drive.projRot_zero_apply`, proved here),
* is differentiable in the point (`Work.Drive.mdifferentiableAt_projRot_aux`, the one-variable slice
  of the joint smoothness `Work.Drive.contMDiffAt_projRot`; the only real work is the instance
  plumbing for the product manifold `ℝ × ℝP³`, see the `letI` block),

whence `Work.Drive.injective_mfderiv_projRot` (its derivative is injective, because evaluating the
`mfderiv` of the identity `projRot (-t) ∘ projRot t` through the chain rule gives a left inverse).

The main statements are

* `Work.Drive.injective_mfderiv_cls_rotPresentation_real` for a real rotation parameter `(t : ℝ)`, and
* `Work.Drive.injective_mfderiv_cls_rotPresentation` for an arbitrary `w : UnitAddCircle` (a coset of
  `ℝ` and hence of the form `(t : UnitAddCircle)`),

both of the form: `hc` for the base chart `Q` implies `hc` for `rotPresentation Q w`; the assembled
form `Work.Drive.injective_mfderiv_cls_rotPresentation_of_diskImmersion` takes the two hypotheses in
the form in which the route has them (`Work.Drive.injective_mfderiv_cls_diskPlane_of_openSquare` of the
*disk* presentation of the plane, at an interior point of the parameter square).

Two further transports of the same kind, which the other clauses of `Work.Drive.Meet3Hyp` and the
general-position condition need:

* `Work.Drive.seam_rotPresentation` — the `seam` clause for the rotated presentations;
* `Work.Drive.range_mfderiv_cls_rotPresentation_real` — the **range** (hence the tangent plane) of the
  rotated presentation is the image of the base tangent plane under `d (projRot t)`, i.e. the `hV`
  companion of the immersion transfer.

Nothing here needs the general-position condition `hV` itself, which is a genuinely different (and
rotation-invariant only jointly) statement about the three ranges — see
`Submission/Work/Drive/HC_AND_FACE_STATUS.md` and `Submission/Work/Drive/HC_ROTATION_STATUS.md`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization

attribute [local instance] Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 1. The rotation of `ℝP³` is an action -/

theorem projRot_add_apply (s t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
    projRot (s + t) p = projRot s (projRot t p) := by
  have hL : projRot (s + t) p
      = Projectivization.mk ℝ (diagRot (s + t) p.rep)
          (diagRot_ne_zero (s + t) (Projectivization.rep_nonzero p)) := rfl
  have hR : projRot s (projRot t p)
      = Projectivization.mk ℝ (diagRot s (diagRot t p.rep))
          (diagRot_ne_zero s (diagRot_ne_zero t (Projectivization.rep_nonzero p))) :=
    projRot_mk s (diagRot t p.rep) (diagRot_ne_zero t (Projectivization.rep_nonzero p))
  rw [hL, hR]
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, by rw [one_smul, diagRot_add]⟩

theorem projRot_zero_apply (p : Projectivization ℝ (Eucl 3)) : projRot 0 p = p := by
  calc projRot 0 p = Projectivization.mk ℝ (diagRot 0 p.rep)
        (diagRot_ne_zero 0 (Projectivization.rep_nonzero p)) := rfl
    _ = Projectivization.mk ℝ p.rep (Projectivization.rep_nonzero p) :=
        (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, by
          rw [one_smul]
          exact (diagRot_zero p.rep).symm⟩
    _ = p := Projectivization.mk_rep p

/-- The function form of the action law. -/
theorem projRot_add (s t : ℝ) : projRot (s + t) = projRot s ∘ projRot t :=
  funext fun p => projRot_add_apply s t p

/-- The function form of the identity law. -/
theorem projRot_zero : projRot 0 = id := funext fun p => projRot_zero_apply p

theorem projRot_neg_comp (t : ℝ) : projRot (-t) ∘ projRot t = id := by
  rw [← projRot_add, neg_add_cancel, projRot_zero]

theorem projRot_neg_apply (t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
    projRot (-t) (projRot t p) = p := congrFun (projRot_neg_comp t) p

/-! ## 2. The one-variable slice of the joint smoothness of `projRot` -/

/-- **The slice differentiability of the rotation of `ℝP³`.**  This is the one-variable form of
`Work.Drive.contMDiffAt_projRot`, obtained by composing with the slice `p ↦ (t, p)`; the `letI` block
supplies the charted-space structures of the product manifold `ℝ × ℝP³` both in the `ModelProd`
spelling demanded by `Work.Drive.contMDiffAt_projRot` and in the plain-product spelling on which type
class search runs inside `ContMDiffAt.comp`. -/
theorem mdifferentiableAt_projRot_aux (t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
    MDifferentiableAt (𝓡 3) (𝓡 3) (projRot t) p := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3)))
      (ℝ × Projectivization ℝ (Eucl 3)) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3))
  letI : ChartedSpace (ℝ × EuclideanSpace ℝ (Fin 3)) (ℝ × Projectivization ℝ (Eucl 3)) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (EuclideanSpace ℝ (Fin 3)))
      (ℝ × Projectivization ℝ (Eucl 3)))
  have hprod := contMDiffAt_projRot t p
  have hslice : ContMDiffAt (𝓡 3) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : Projectivization ℝ (Eucl 3) => ((t, q) : ℝ × Projectivization ℝ (Eucl 3))) p :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := t)) (contMDiffAt_id (I := 𝓡 3))
  have hmain := hprod.comp p hslice
  simpa only [Function.comp_def] using hmain.mdifferentiableAt (by simp)

/-- **The derivative of the rotation of `ℝP³` is injective**: `projRot (-t)` is a left inverse of
`projRot t`, so the chain rule exhibits the derivative of the identity as the composite of the two
derivatives. -/
theorem injective_mfderiv_projRot (t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (projRot t) p) := by
  have hmd := mdifferentiableAt_projRot_aux t p
  have hmd' := mdifferentiableAt_projRot_aux (-t) (projRot t p)
  have hcomp := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) p hmd' hmd
  have hid : (projRot (-t) ∘ projRot t) = id := projRot_neg_comp t
  have hcomp' : ContinuousLinearMap.id ℝ _ =
      (mfderiv (𝓡 3) (𝓡 3) (projRot (-t)) (projRot t p)).comp
        (mfderiv (𝓡 3) (𝓡 3) (projRot t) p) := by
    rw [← hcomp, hid, mfderiv_id]
  have key : ∀ w : TangentSpace (𝓡 3) p,
      (mfderiv (𝓡 3) (𝓡 3) (projRot (-t)) (projRot t p))
        ((mfderiv (𝓡 3) (𝓡 3) (projRot t) p) w) = w := fun w =>
    (congrArg (fun L => L w) hcomp').symm
  intro u v huv
  exact (key u).symm.trans (by rw [huv]; exact key v)

/-! ## 3. The class map of a rotated plane -/

/-- The class map of the rotated presentation is the class map of the base presentation composed with
the rotation of `ℝP³`. -/
theorem cls_rotPresentation_eq (Q : ℂ → CappingSpace) (t : ℝ) :
    (fun y : EuclideanSpace ℝ (Fin 2) =>
        (cappingSpaceHomeoProj (rotPresentation Q ((t : ℝ) : UnitAddCircle) y)).2)
      = projRot t ∘ (fun y : EuclideanSpace ℝ (Fin 2) =>
          (cappingSpaceHomeoProj (diskPlane Q y)).2) := by
  funext y
  rw [rotPresentation, Function.comp_apply, diskPlane_apply, diskPlane_apply]
  exact congrArg Prod.snd (cappingSpaceHomeoProj_rotCapping t _)

/-- The value form of `Work.Drive.cls_rotPresentation_eq`: the projective class of the rotated plane at
`y` is the rotation of the class of the base plane at `y`. -/
theorem cls_rotPresentation_apply (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (rotPresentation Q ((t : ℝ) : UnitAddCircle) y)).2
      = projRot t ((cappingSpaceHomeoProj (diskPlane Q y)).2) := by
  rw [rotPresentation, diskPlane_apply, diskPlane_apply]
  exact congrArg Prod.snd (cappingSpaceHomeoProj_rotCapping t _)

/-- **The immersion condition `hc` transfers to the rotated presentation** (real rotation parameter).

This is the form in which the counting route needs `hc` for each of the three swept planes
`P k = rotPresentation Q (u k)`: the base chart `Q` has to be an immersion, and the rotation is
harmless because its differential is injective (`Work.Drive.injective_mfderiv_projRot`).

The two hypotheses on the base chart are exactly the ones supplied by
`Work.Drive.injective_mfderiv_cls_diskPlane_of_openSquare` (which derives them from the immersion of
the *disk* presentation of the plane). -/
theorem injective_mfderiv_cls_rotPresentation_real (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2))
    (hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y)
    (hbase : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (rotPresentation Q ((t : ℝ) : UnitAddCircle) y')).2)
      y) := by
  rw [cls_rotPresentation_eq Q t]
  have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) y
    (g := projRot t) (f := fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2)
    (mdifferentiableAt_projRot_aux t _) hcls
  rw [hcomp]
  show Function.Injective (fun w : TangentSpace (𝓡 2) y =>
    (mfderiv (𝓡 3) (𝓡 3) (projRot t)
        ((fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y))
      ((mfderiv (𝓡 2) (𝓡 3)
        (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y) w))
  intro u v huv
  exact hbase (injective_mfderiv_projRot t
    ((fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y) huv)

/-- **The immersion condition `hc` transfers to the rotated presentation**, for an arbitrary rotation
angle `w : UnitAddCircle` (which is the form in which the design's angles `u k` occur). -/
theorem injective_mfderiv_cls_rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2))
    (hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y)
    (hbase : Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (rotPresentation Q w y')).2) y) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective w
  rw [← ht]
  exact injective_mfderiv_cls_rotPresentation_real Q t y hcls hbase

/-- **Seam invariance of a rotated presentation**, from seam invariance of the base chart: the
rotation transports the agreement `Q (-z) = Q z` of the chart at antipodal boundary points, and the
statement is `Work.Drive.diskPlane_seamInv2` applied to the presentation `fun z => rotCapping w (Q z)`
— which is `Work.Drive.rotPresentation Q w` definitionally.  This is the `seam` clause of
`Work.Drive.Meet3Hyp` for the three swept chains of the counting route. -/
theorem seam_rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : onSeam2 y) :
    rotPresentation Q w (seamInv2 y) = rotPresentation Q w y :=
  diskPlane_seamInv2 (Q := fun z => rotCapping w (Q z)) (fun z hz => by rw [hQ z hz]) hy

set_option backward.isDefEq.respectTransparency true in
/-- **The tangent space of a rotated plane is the rotated tangent space of the base plane**: the range
of the class derivative of the rotated presentation — written here through the composite
`y ↦ projRot t (cls (diskPlane Q y))`, which is the class map of `rotPresentation Q (↑t)` by
`Work.Drive.cls_rotPresentation_eq` — is the image of the range of the base chart's class derivative
under the differential of the rotation of `ℝP³`.

This is the `hV` companion of `Work.Drive.injective_mfderiv_cls_rotPresentation`: the general-position
condition of the engine, `range_0 ⊓ range_1 ⊓ range_2 = ⊥`, becomes, after this lemma, a statement
about the three *base* tangent planes of the chart and the three rotation differentials — the form in
which the genericity argument (`Submission/Work/Drive/GENERICITY_ASSEMBLY_STATUS.md`) has to produce
it.  The rotation angle is a real number `t` (a general `w : UnitAddCircle` is `(t : UnitAddCircle)`
for some `t`, `QuotientAddGroup.mk_surjective`).

The hypothesis is exactly the differentiability of the base class map used by
`Work.Drive.injective_mfderiv_cls_rotPresentation`; no injectivity is needed here. -/
theorem range_mfderiv_cls_rotPresentation_real (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2))
    (hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y) :
    (mfderiv (𝓡 2) (𝓡 3)
        (fun y' => projRot t ((cappingSpaceHomeoProj (diskPlane Q y')).2)) y).range
      = Submodule.map (σ₁₂ := RingHom.id ℝ)
          (mfderiv (𝓡 3) (𝓡 3) (projRot t) ((cappingSpaceHomeoProj (diskPlane Q y)).2))
          (mfderiv (𝓡 2) (𝓡 3)
            (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y).range := by
  have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3) y
    (g := projRot t) (f := fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2)
    (mdifferentiableAt_projRot_aux t _) hcls
  have key := hcomp
  simp only [Function.comp_def] at key
  rw [key]
  rw [show ((mfderiv (𝓡 3) (𝓡 3) (projRot t)
          ((cappingSpaceHomeoProj (diskPlane Q y)).2)).comp
        (mfderiv (𝓡 2) (𝓡 3)
          (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y)).range
      = ((mfderiv (𝓡 3) (𝓡 3) (projRot t)
            ((cappingSpaceHomeoProj (diskPlane Q y)).2)).toLinearMap.comp
          (mfderiv (𝓡 2) (𝓡 3)
            (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y).toLinearMap).range
      from rfl]
  exact LinearMap.range_comp _ _

/-! ## 4. The immersed form: `hc` for the rotated presentations from the disk presentation -/

/-- **The immersion condition `hc` for every rotated presentation, from the immersion of the disk
presentation of the plane.**  This is the form the counting route uses: for the chart `Q` of a plane
whose *disk* presentation has injective class differential everywhere (for instance a Cartesian
presentation, `Work.Drive.injective_class_of_cartesian`), every rotated presentation
`Work.Drive.rotPresentation Q w` has `hc` at every point of the open parameter square, so the engine
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion` receives its immersion
hypothesis for all three swept chains.

The two square hypotheses are needed for the folding `Work.Drive.sqDisk ∘ Work.Drive.foldBox`
(which is an immersion exactly on the open square, `Work.Drive.injective_fderiv_sqDisk_foldBox`). -/
theorem injective_mfderiv_cls_rotPresentation_of_diskImmersion (Q : ℂ → CappingSpace)
    (w : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)))
    (hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (rotPresentation Q w y')).2) y) := by
  have hfold : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox :=
    contDiff_iff_contDiffAt.mpr fun y =>
      contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)
  have hgd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) :=
    sqDisk_contDiff.comp hfold
  have hg : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) y :=
    (contMDiffAt_iff_contDiffAt.mpr (hgd.contDiffAt)).mdifferentiableAt (by simp)
  have hcls : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y' => (cappingSpaceHomeoProj (diskPlane Q y')).2) y := by
    have h := hf.comp y hg
    simpa only [Function.comp_def, diskPlane_apply] using h
  exact injective_mfderiv_cls_rotPresentation Q w y hcls
    (injective_mfderiv_cls_diskPlane_of_openSquare Q y h0 h1 hf hf_inj)

end

end Work.Drive
