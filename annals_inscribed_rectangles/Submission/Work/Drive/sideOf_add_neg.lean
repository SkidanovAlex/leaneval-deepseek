import Mathlib
import Submission.Work.Drive.sideAntisymmetry
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.projRot
import Submission.Work.Drive.projLine_preconnected
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping

/-!
# The antisymmetry of the side function: `e t + e (-t) = 1`

The side function of the order route is

> `e w = [the cut of the chart `Q` by the sweep of the rotated plane `w·P₀` is non-empty]`

(`Work.Drive.sideOf`, `Submission/Work/Drive/sideValue.lean`).  The order of Hugelmeyer's Theorem 2
takes its values on the *non-collision* angles and is antisymmetric: the two cuts of the chart by the
sweeps of the planes `w·P₀` and `(−w)·P₀` are *never both* non-empty, and (off the collisions)
*never both* empty.  This file proves that, in the profile formulation of
`Submission/Work/Drive/sideAntisymmetry.lean`:

> **`Work.Drive.sideOf_add_neg`** — for a continuous chart `Q` of the capping space, a truncation
> level `c`, a cutoff `ψ`, an angle `t` and a *profile* `ρ` of the chart's class-line
> (`ρ (class (Q z)) = levelOf (Q z)` for `‖z‖ ≤ 1`, `hcov`, `hQcls`), with the two class planes of
> `φ` and `φu` exchanged by the rotation of the angle `t` (`hrelu`) and disjoint along their common
> class line (`hne`): `e t + e (-t) = 1` in `ZMod 2`.

The mathematical content is the *rigidity* of the level comparison along the common class line `L`:
the two cuts compare `ρ` with `ρ ∘ projRot (-t)` on `L`, in the two opposite orders (rotation by
`t` turns the cut of the chart by the swept plane into the cut of the rotated chart by the *base*
plane, swapping the roles of the two profiles).  Since `L` is a projective line, hence preconnected,
and the difference of the two profiles is nowhere zero on it by `hne`, the sign is constant, so
exactly one of the two cuts is the whole class-cut and the other is empty.

## Contents

* `Work.Drive.sna_continuous_projRot` — the rotation `projRot t` of `ℝP³` is continuous (from the
  quotient topology of `Submission/Work/Drive/ProjectiveTopology.lean`);
* `Work.Drive.sna_projRot_add`, `sna_projRot_zero`, `sna_projRot_neg` — it is an action;
* `Work.Drive.sna_finrank_ker`, `sna_Lpre`, `sna_Lnonempty` — the common class line is a
  non-empty preconnected projective line;
* `Work.Drive.sna_cut_t_empty`, `sna_cut_t_classCut`, `sna_cut_neg_empty`,
  `sna_cut_neg_classCut` — the four halves of the rigidity;
* `Work.Drive.sideOf_add_neg` — the antisymmetry.

## The degenerate angles

The *negative* angle `-t` is taken in `UnitAddCircle = ℝ/ℤ`, so the two summands of the conclusion
coincide as soon as `(t : UnitAddCircle) = -(t : UnitAddCircle)`, i.e. as soon as `2t ∈ ℤ` (the angles
`0` and `1/2` modulo `1`).  There the conclusion reads `2 · e t = 1`, which is *false* in `ZMod 2`
for a given value `e t` — but at such an angle the **hypotheses are inconsistent** and the clause is
vacuous: since `projRot (-t) = projRot t =:` R` and `hrelu` exhibits `L` as `R`-invariant, the
function `q ↦ ρ q - ρ (R q)` is continuous on the preconnected `L`, nowhere zero by `hne`, and
satisfies `d (R q) = - d q`, whence a contradiction
(`Work.Drive.sna_hypotheses_inconsistent_of_self_neg`, recorded below).  In the intended application
the angles are the non-collision angles `u ∈ Zc γ`, for which `2u = 0` would put `u` in `GoodC γ`
(so `u = 0` or `u = 1/2`, both excluded), which is exactly the extra hypothesis `ht2` of
`Submission/Work/Drive/sideOf_add_neg_of_ne_neg.lean`; the present file shows that `ht2` is
nevertheless *not needed* for the truth of the statement as given here.
-/

set_option autoImplicit false

namespace Work.Drive

open scoped Topology Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

/-! ## 1. Continuity and the action law of the projective rotation -/

/-- `c₁` is additive. -/
lemma sna_c₁_add (x y : Eucl 3) : c₁ (x + y) = c₁ x + c₁ y := by
  rw [← confProjVecOf_c₁CLM_apply, map_add, confProjVecOf_c₁CLM_apply, confProjVecOf_c₁CLM_apply]

/-- `c₂` is additive. -/
lemma sna_c₂_add (x y : Eucl 3) : c₂ (x + y) = c₂ x + c₂ y := by
  rw [← confProjVecOf_c₂CLM_apply, map_add, confProjVecOf_c₂CLM_apply, confProjVecOf_c₂CLM_apply]

/-- `ofComplex` is additive. -/
lemma sna_ofComplex_add (z z' w w' : ℂ) :
    ofComplex (z + w) (z' + w') = ofComplex z z' + ofComplex w w' := by
  conv_lhs => rw [← ofComplex_c₁_c₂ (ofComplex (z + w) (z' + w'))]
  conv_rhs => rw [← ofComplex_c₁_c₂ (ofComplex z z' + ofComplex w w')]
  refine ofComplex_congr ?_ ?_
  · rw [← confProjVecOf_c₁CLM_apply (ofComplex z z' + ofComplex w w'), map_add]
    simp only [confProjVecOf_c₁CLM_apply, c₁_ofComplex]
  · rw [← confProjVecOf_c₂CLM_apply (ofComplex z z' + ofComplex w w'), map_add]
    simp only [confProjVecOf_c₂CLM_apply, c₂_ofComplex]

/-- The diagonal rotation is additive in the vector variable. -/
lemma sna_diagRot_add (t : ℝ) (x y : Eucl 3) :
    diagRot t (x + y) = diagRot t x + diagRot t y := by
  simp only [diagRot, sna_c₁_add, sna_c₂_add, mul_add, sna_ofComplex_add]

/-- The diagonal rotation as a linear map. -/
noncomputable def snaDiagRotLin (t : ℝ) : Eucl 3 →ₗ[ℝ] Eucl 3 where
  toFun := diagRot t
  map_add' := sna_diagRot_add t
  map_smul' := fun c x => by
    simp only [RingHom.id_apply]
    exact diagRot_smul t c x

/-- The diagonal rotation is continuous (finite dimension). -/
theorem sna_continuous_diagRot (t : ℝ) : Continuous (fun x : Eucl 3 => diagRot t x) :=
  (LinearMap.toContinuousLinearMap (snaDiagRotLin t)).continuous

/-- **The rotation of `ℝP³` is continuous.**  The projectivisation carries the quotient topology of
the non-zero vectors, and `projRot t` is the descent of the continuous linear map `diagRot t`. -/
theorem sna_continuous_projRot (t : ℝ) : Continuous (projRot t) := by
  have hq : Topology.IsQuotientMap
      (fun p : {v : Eucl 3 // v ≠ 0} => Projectivization.mk ℝ p.1 p.2) :=
    (isOpenMap_projectivizationMk ℝ (Eucl 3)).isQuotientMap
      (continuous_projectivizationMk ℝ (Eucl 3))
      (fun q => ⟨⟨q.rep, q.rep_nonzero⟩, Projectivization.mk_rep q⟩)
  refine (hq.continuous_iff (g := projRot t)).mpr ?_
  have hg : Continuous fun p : {v : Eucl 3 // v ≠ 0} =>
      (⟨diagRot t p.1, diagRot_ne_zero t p.2⟩ : {v : Eucl 3 // v ≠ 0}) :=
    Continuous.subtype_mk ((sna_continuous_diagRot t).comp continuous_subtype_val) _
  refine Continuous.congr ((continuous_projectivizationMk ℝ (Eucl 3)).comp hg) ?_
  intro p
  exact (projRot_mk t p.1 p.2).symm

/-- The rotation law of `projRot` (from `projRot_mk` and the additivity of `diagRot`). -/
theorem sna_projRot_add (s t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
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

/-- `projRot 0` is the identity. -/
theorem sna_projRot_zero (p : Projectivization ℝ (Eucl 3)) : projRot 0 p = p := by
  calc projRot 0 p = Projectivization.mk ℝ (diagRot 0 p.rep)
        (diagRot_ne_zero 0 (Projectivization.rep_nonzero p)) := rfl
    _ = Projectivization.mk ℝ p.rep (Projectivization.rep_nonzero p) :=
        (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, by
          rw [one_smul]
          exact (diagRot_zero p.rep).symm⟩
    _ = p := Projectivization.mk_rep p

/-- `projRot (-t)` is a left inverse of `projRot t`. -/
theorem sna_projRot_neg (t : ℝ) (p : Projectivization ℝ (Eucl 3)) :
    projRot (-t) (projRot t p) = p := by
  rw [← sna_projRot_add, neg_add_cancel, sna_projRot_zero]

/-! ## 2. The class and the level of a rotated point -/

/-- The class of a rotated point of the capping space is the rotated class. -/
theorem sna_cls_rotCapping (t : ℝ) (X : CappingSpace) :
    (cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle) X)).2
      = projRot t ((cappingSpaceHomeoProj X).2) := by
  simp only [cappingSpaceHomeoProj_rotCapping]

/-- The level of a rotated point of the capping space is unchanged. -/
theorem sna_levelOf_rotCapping (t : ℝ) (X : CappingSpace) :
    levelOf (rotCapping ((t : ℝ) : UnitAddCircle) X) = levelOf X := by
  simp only [levelOf, cappingSpaceHomeoProj_rotCapping]

/-! ## 3. The common class line -/

/-- A non-zero functional of `Eucl 3` has a kernel of dimension `3`. -/
theorem sna_finrank_ker (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) = 3 := by
  have hne : (φ : Eucl 3 →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    exact hφ (ContinuousLinearMap.ext fun x => congrArg (fun f => f x) h)
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := (φ : Eucl 3 →ₗ[ℝ] ℝ)) hne
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := finrank_euclideanSpace_fin
  omega

/-- The common class line of two non-zero functionals is a preconnected projective line. -/
theorem sna_Lpre (φ φu : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (hφu : φu ≠ 0) :
    IsPreconnected (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) := by
  rw [← projLine_inf_eq]
  exact isPreconnected_projLine_inf (sna_finrank_ker φ hφ) (sna_finrank_ker φu hφu)

/-- The common class line of two non-zero functionals is non-empty. -/
theorem sna_Lnonempty (φ φu : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (hφu : φu ≠ 0) :
    (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))).Nonempty := by
  have hfr : 2 ≤ Module.finrank ℝ
      ↥(LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ) ⊓ LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
    have hle : Module.finrank ℝ ↥(LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)
        ⊔ LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) ≤ 4 := by
      calc Module.finrank ℝ ↥(LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)
            ⊔ LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) ≤ Module.finrank ℝ (Eucl 3) :=
            Submodule.finrank_le _
        _ = 4 := finrank_euclideanSpace_fin
    rw [sna_finrank_ker φ hφ, sna_finrank_ker φu hφu] at hsup
    omega
  have hpos : 0 < Module.finrank ℝ (↥(LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)
      ⊓ LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨Projectivization.mk ℝ x.1 (fun h => hx (Subtype.ext (by simpa using h))), ?_⟩
  exact ⟨⟨x.1, _, x.2.1, rfl⟩, ⟨x.1, _, x.2.2, rfl⟩⟩

/-- **The rotation identity for the negative angle**: the cut of the chart by the sweep of the plane
rotated by `-t` is the cut of the chart rotated by `t` by the sweep of the base plane. -/
theorem sna_cut_neg_rotate (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ) (t : ℝ) :
    diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle)))
      = diskCut (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z))
          (clampedSweep c ψ (diskPlane Q)) := by
  have h1 := diskCut_clampedSweep_rotCapping Q c ψ
    (rotPresentation Q ((-t : ℝ) : UnitAddCircle)) ((t : ℝ) : UnitAddCircle)
  have h2 : (fun y => rotCapping ((t : ℝ) : UnitAddCircle)
      (rotPresentation Q ((-t : ℝ) : UnitAddCircle) y))
      = rotPresentation Q (((t : ℝ) : UnitAddCircle) + ((-t : ℝ) : UnitAddCircle)) :=
    rotPresentation_add Q (t : UnitAddCircle) ((-t : ℝ) : UnitAddCircle)
  rw [h2] at h1
  have h3 : ((t : ℝ) : UnitAddCircle) + ((-t : ℝ) : UnitAddCircle) = 0 := by
    rw [← AddCircle.coe_add]
    simp
  rw [h3, rotPresentation, rotCapping_zero] at h1
  simpa using h1.symm


/-! ## 4. The dictionary of the rotation on the presentations -/

/-- The class of the rotated presentation at a box point. -/
theorem sna_cls_rotPresentation (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (rotPresentation Q (t : UnitAddCircle) y)).2
      = projRot t ((cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2) :=
  sna_cls_rotCapping t _

/-- The level of the rotated presentation at a box point. -/
theorem sna_levelOf_rotPresentation (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf (rotPresentation Q (t : UnitAddCircle) y) = levelOf (Q (sqDisk (foldBox y))) :=
  sna_levelOf_rotCapping t _

/-- The class of the rotated *chart* at a disk point. -/
theorem sna_cls_rotChart (Q : ℂ → CappingSpace) (t : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle) (Q (cplxOf x)))).2
      = projRot t ((cappingSpaceHomeoProj (Q (cplxOf x))).2) :=
  sna_cls_rotCapping t _

/-- The level of the rotated *chart* at a disk point is the level of the chart. -/
theorem sna_levelOf_rotChart (Q : ℂ → CappingSpace) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    levelOf (rotCapping ((t : ℝ) : UnitAddCircle) (Q (cplxOf x)))
      = levelOf (Q (cplxOf x)) :=
  sna_levelOf_rotCapping t _

/-! ## 5. The four halves of the rigidity -/

/-- Forwards: the rotation by `t` carries the class plane of `φ` into the class plane of `φu`. -/
theorem sna_rot_mem_fwd {φ φu : Eucl 3 →L[ℝ] ℝ} {t : ℝ}
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      projRot t q ∈ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) := by
  intro q hq
  rw [hrelu]
  exact ⟨q, hq, rfl⟩

/-- Backwards: the rotation by `-t` carries the class plane of `φu` into the class plane of `φ`. -/
theorem sna_rot_mem_bwd {φ φu : Eucl 3 →L[ℝ] ℝ} {t : ℝ}
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    ∀ p ∈ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)),
      projRot (-t) p ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) := by
  intro p hp
  rw [hrelu] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [sna_projRot_neg]
  exact hq

/-- A point whose `(-t)`-rotation lies in the class plane of `φ` lies in the class plane of `φu`. -/
theorem sna_rot_mem_iff {φ φu : Eucl 3 →L[ℝ] ℝ} {t : ℝ}
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))) :
    ∀ p : Projectivization ℝ (Eucl 3),
      projRot (-t) p ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) →
      p ∈ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) := by
  intro p hp
  rw [hrelu]
  refine ⟨projRot (-t) p, hp, ?_⟩
  rw [← sna_projRot_add t (-t) p, add_neg_cancel, sna_projRot_zero]

/-- **Half A of the rigidity.**  If the chart's profile dominates the rotated one along the common
class line, the cut of the chart by the sweep of the `t`-rotated plane is empty. -/
theorem sna_cut_t_empty (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0) (t : ℝ)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hlev : ∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 → c ≤ levelOf (rotPresentation Q v y))
    (hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ (projRot (-t) q) < ρ q) :
    diskCut Q (clampedSweep c ψ (rotPresentation Q (t : UnitAddCircle))) = ∅ := by
  refine diskCut_eq_empty_of_lt_profile_classLine Q c hc ψ hψ0 hψ1 hψ01 hcont
    (rotPresentation Q (t : UnitAddCircle)) (fun y hy => hlev _ y hy) φu ?hPcls
    (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) ?hLmem
    ρ (fun q => ρ (projRot (-t) q)) ?hFQ ?hGmax hsign
  · intro y hy
    have hy' := foldBox_mem_unitBox y
    rw [sna_cls_rotPresentation]
    exact sna_rot_mem_fwd hrelu _ (hQcls _)
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    exact ⟨hQcls _, h2⟩
  · intro x hx
    exact hρval _ (mem_classCut.mp hx).1
  · intro x hx y hy hcls
    have hz : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
    have h2 : (cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2
        = projRot (-t) ((cappingSpaceHomeoProj (Q (cplxOf x))).2) := by
      have h3 : projRot t ((cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2)
          = (cappingSpaceHomeoProj (Q (cplxOf x))).2 := by
        rw [← sna_cls_rotPresentation, hcls]
      calc (cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2
          = projRot (-t) (projRot t ((cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2)) :=
            (sna_projRot_neg t _).symm
        _ = projRot (-t) ((cappingSpaceHomeoProj (Q (cplxOf x))).2) := by rw [h3]
    calc levelOf (rotPresentation Q (t : UnitAddCircle) y)
        = levelOf (Q (sqDisk (foldBox y))) := sna_levelOf_rotPresentation Q t y
      _ = ρ ((cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2) := (hρval _ hz).symm
      _ ≤ ρ (projRot (-t) ((cappingSpaceHomeoProj (Q (cplxOf x))).2)) := le_of_eq (by rw [h2])

/-- **Half B of the rigidity.**  If the rotated profile dominates the chart's along the common class
line, the cut of the chart by the sweep of the `t`-rotated plane is the whole class-cut. -/
theorem sna_cut_t_classCut (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0) (t : ℝ)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q)
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hlev : ∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 → c ≤ levelOf (rotPresentation Q v y))
    (hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ q < ρ (projRot (-t) q)) :
    diskCut Q (clampedSweep c ψ (rotPresentation Q (t : UnitAddCircle))) = classCut Q φu := by
  refine diskCut_eq_classCut_of_lt_profile_classLine Q c hc ψ hψ0 hψ1 hψ01 hcont
    (rotPresentation Q (t : UnitAddCircle)) (fun y hy => hlev _ y hy) φu ?hPcls
    (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) ?hLmem
    (fun q => ρ (projRot (-t) q)) ?hGatt ?hclow ρ ?hFQ hsign
  · intro y hy
    rw [sna_cls_rotPresentation]
    exact sna_rot_mem_fwd hrelu _ (hQcls _)
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    exact ⟨hQcls _, h2⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    rw [hrelu] at h2
    obtain ⟨q, hq, hqp⟩ := h2
    obtain ⟨z, hz, hzq⟩ := hcov q hq
    obtain ⟨y, ⟨hybox, hysq⟩, -⟩ := sqDisk_foldBox_existsUnique z hz
    have hy' : rotPresentation Q (t : UnitAddCircle) y
        = rotCapping ((t : ℝ) : UnitAddCircle) (Q z) := by
      rw [show rotPresentation Q (t : UnitAddCircle) y
          = rotCapping ((t : ℝ) : UnitAddCircle) (Q (sqDisk (foldBox y))) from rfl, hysq]
    refine ⟨y, hybox, ?_, ?_⟩
    · rw [hy', sna_cls_rotCapping, hzq, hqp]
    · rw [hy', sna_levelOf_rotCapping]
      rw [(hρval z hz).symm, hzq, ← hqp, sna_projRot_neg]
  · intro x hx
    exact hcne _ (mem_classCut.mp hx).1
  · intro x hx
    exact hρval _ (mem_classCut.mp hx).1


/-- **Half C of the rigidity.**  If the rotated profile dominates the chart's along the common class
line, the cut of the chart by the sweep of the `(-t)`-rotated plane (read as the cut of the rotated
chart by the sweep of the base plane) is empty. -/
theorem sna_cut_neg_empty (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0) (t : ℝ)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ q < ρ (projRot (-t) q)) :
    diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle))) = ∅ := by
  rw [sna_cut_neg_rotate]
  refine diskCut_eq_empty_of_lt_profile_classLine
    (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) c hc ψ hψ0 hψ1 hψ01 hcont
    (diskPlane Q) ?hr φ ?hPcls
    (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) ?hLmem
    (fun p => ρ (projRot (-t) p)) ρ ?hFQ ?hGmax hsign
  case hr =>
    intro y hy
    rw [diskPlane_apply]
    exact hcne _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox y))
  case hPcls =>
    intro y hy
    exact hQcls _
  case hLmem =>
    intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    exact ⟨h2, by
      rw [sna_cls_rotCapping]
      exact sna_rot_mem_fwd hrelu _ (hQcls _)⟩
  case hFQ =>
    intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    calc ρ (projRot (-t)
          (cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle)
            (Q (cplxOf x)))).2)
        = ρ (projRot (-t) (projRot t ((cappingSpaceHomeoProj (Q (cplxOf x))).2))) := by
          rw [sna_cls_rotCapping]
      _ = ρ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) := by rw [sna_projRot_neg]
      _ = levelOf (Q (cplxOf x)) := hρval _ h1
      _ = levelOf (rotCapping ((t : ℝ) : UnitAddCircle) (Q (cplxOf x))) :=
          (sna_levelOf_rotCapping t _).symm
  case hGmax =>
    intro x hx y hy hcls
    have hz : ‖sqDisk (foldBox y)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
    calc levelOf (diskPlane Q y) = levelOf (Q (sqDisk (foldBox y))) := rfl
      _ = ρ ((cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2) := (hρval _ hz).symm
      _ ≤ ρ ((cappingSpaceHomeoProj (diskPlane Q y)).2) := le_of_eq rfl
      _ = ρ ((cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle)
            (Q (cplxOf x)))).2) := by rw [hcls]

/-- **Half D of the rigidity.**  If the chart's profile dominates the rotated one along the common
class line, the cut of the chart by the sweep of the `(-t)`-rotated plane (read as the cut of the
rotated chart by the sweep of the base plane) is the whole class-cut of the rotated chart. -/
theorem sna_cut_neg_classCut (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0) (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0) (t : ℝ)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q)
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ (projRot (-t) q) < ρ q) :
    diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle)))
      = classCut (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) φ := by
  rw [sna_cut_neg_rotate]
  refine diskCut_eq_classCut_of_lt_profile_classLine
    (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) c hc ψ hψ0 hψ1 hψ01 hcont
    (diskPlane Q) ?hr φ ?hPcls
    (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) ?hLmem
    ρ ?hGatt ?hclow (fun p => ρ (projRot (-t) p)) ?hFQ hsign
  case hr =>
    intro y hy
    rw [diskPlane_apply]
    exact hcne _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox y))
  case hPcls =>
    intro y hy
    exact hQcls _
  case hLmem =>
    intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    exact ⟨h2, by
      rw [sna_cls_rotCapping]
      exact sna_rot_mem_fwd hrelu _ (hQcls _)⟩
  case hGatt =>
    intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    obtain ⟨z, hz, hzq⟩ := hcov _ h2
    obtain ⟨y, ⟨hybox, hysq⟩, -⟩ := sqDisk_foldBox_existsUnique z hz
    have hy' : diskPlane Q y = Q z := by rw [diskPlane_apply, hysq]
    refine ⟨y, hybox, ?_, ?_⟩
    · rw [hy']
      exact hzq.symm
    · rw [hy', ← hzq]
      exact hρval z hz
  case hclow =>
    intro x hx
    rw [sna_levelOf_rotCapping]
    exact hcne _ (mem_classCut.mp hx).1
  case hFQ =>
    intro x hx
    obtain ⟨h1, h2⟩ := mem_classCut.mp hx
    calc ρ (projRot (-t)
          (cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle)
            (Q (cplxOf x)))).2)
        = ρ (projRot (-t) (projRot t ((cappingSpaceHomeoProj (Q (cplxOf x))).2))) := by
          rw [sna_cls_rotCapping]
      _ = ρ ((cappingSpaceHomeoProj (Q (cplxOf x))).2) := by rw [sna_projRot_neg]
      _ = levelOf (Q (cplxOf x)) := hρval _ h1
      _ = levelOf (rotCapping ((t : ℝ) : UnitAddCircle) (Q (cplxOf x))) :=
          (sna_levelOf_rotCapping t _).symm

/-! ## 6. Non-emptiness of the two class-cuts -/

/-- The class-cut of the chart in the plane of `φu` is non-empty. -/
theorem sna_classCut_nonempty (Q : ℂ → CappingSpace) (φ φu : Eucl 3 →L[ℝ] ℝ)
    (hφ : φ ≠ 0) (hφu : φu ≠ 0)
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q) :
    (classCut Q φu).Nonempty := by
  obtain ⟨q, hq⟩ := sna_Lnonempty φ φu hφ hφu
  obtain ⟨z, hz, hzq⟩ := hcov q hq.1
  refine ⟨cplxOfInv z, ?_, ?_⟩
  · rw [cplxOf_cplxOfInv]
    exact hz
  · rw [cplxOf_cplxOfInv, hzq]
    exact hq.2

/-- The class-cut of the `t`-rotated chart in the plane of `φ` is non-empty. -/
theorem sna_classCut_rot_nonempty (Q : ℂ → CappingSpace) (φ φu : Eucl 3 →L[ℝ] ℝ)
    (hφ : φ ≠ 0) (hφu : φu ≠ 0) (t : ℝ)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q) :
    (classCut (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) φ).Nonempty := by
  obtain ⟨q, hq⟩ := sna_Lnonempty φ φu hφ hφu
  have hq' : projRot (-t) q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)) :=
    sna_rot_mem_bwd hrelu q hq.2
  obtain ⟨z, hz, hzq⟩ := hcov _ hq'
  refine ⟨cplxOfInv z, ?_, ?_⟩
  · rw [cplxOf_cplxOfInv]
    exact hz
  · rw [cplxOf_cplxOfInv, sna_cls_rotCapping, hzq]
    rw [← sna_projRot_add t (-t) q, add_neg_cancel, sna_projRot_zero]
    exact hq.1

/-- The side function, unfolded. -/
theorem sna_sideOf_apply (Q : ℂ → CappingSpace) (c : ℝ) (ψ : ℝ → ℝ) (w : UnitAddCircle) :
    sideOf Q (fun _ => c) ψ w
      = side (diskCut Q (clampedSweep c ψ (rotPresentation Q w))) := rfl

/-! ## 7. The antisymmetry -/


/-- **The antisymmetry of the side function**: the cuts of the chart by the sweeps of the planes
rotated by `t` and by `-t` cannot be both non-empty nor both empty. -/
theorem sideOf_add_neg (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (t : ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hQcont : Continuous Q)
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0)
    (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρcont : ContinuousOn ρ (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))))
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q)
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hlev : ∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 → c ≤ levelOf (rotPresentation Q v y))
    (hne : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ) ⊓
        LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)),
      ρ q ≠ ρ (projRot (-t) q))
    : sideOf Q (fun _ => c) ψ (t : UnitAddCircle) +
        sideOf Q (fun _ => c) ψ (-(t : UnitAddCircle)) = 1 := by
  have hcoe : (-(t : UnitAddCircle)) = ((-t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_neg]
  have hLdef : projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ) ⊓
          LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)) := (projLine_inf_eq _ _).symm
  -- the difference of the two profiles along the common class line
  have hpre : IsPreconnected (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) :=
    sna_Lpre φ φu hφ hφu
  have hcontρ : ContinuousOn ρ (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) :=
    hρcont.mono inter_subset_left
  have hcont2 : ContinuousOn (fun q => ρ (projRot (-t) q))
      (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))) :=
    hρcont.comp (sna_continuous_projRot (-t)).continuousOn
      (fun q hq => sna_rot_mem_bwd hrelu q hq.2)
  have hdiff_ne : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
      ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)),
      ρ q - ρ (projRot (-t) q) ≠ 0 := by
    intro q hq
    exact sub_ne_zero.mpr (hne q (by rw [← hLdef]; exact hq))
  rcases preconnected_forall_pos_or_neg hpre (hcontρ.sub hcont2) hdiff_ne with hpos | hnegcase
  · -- the chart's profile dominates the rotated one
    have hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ (projRot (-t) q) < ρ q :=
      fun q hq => by
        have h := hpos q hq
        simp only [Pi.sub_apply] at h
        linarith
    have hcut_t : diskCut Q (clampedSweep c ψ (rotPresentation Q (t : UnitAddCircle))) = ∅ :=
      sna_cut_t_empty Q c hc ψ hψ0 hψ1 hψ01 hcont φ hφ φu hφu t hrelu ρ hρval hQcls hlev hsign
    have hcut_neg : diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle)))
        = classCut (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) φ :=
      sna_cut_neg_classCut Q c hc ψ hψ0 hψ1 hψ01 hcont φ hφ φu hφu t hrelu ρ hρval hQcls
        hcov hcne hsign
    have hne_cut : diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle)))
        ≠ ∅ := by
      rw [hcut_neg, ← Set.nonempty_iff_ne_empty]
      exact sna_classCut_rot_nonempty Q φ φu hφ hφu t hrelu hcov
    rw [sna_sideOf_apply, sna_sideOf_apply, hcoe, side_eq_zero_iff.mpr hcut_t,
      side_eq_one_iff.mpr hne_cut]
    norm_num
  · -- the rotated profile dominates the chart's
    have hsign : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))
        ∩ projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)), ρ q < ρ (projRot (-t) q) :=
      fun q hq => by
        have h := hnegcase q hq
        simp only [Pi.sub_apply] at h
        linarith
    have hcut_neg : diskCut Q (clampedSweep c ψ (rotPresentation Q ((-t : ℝ) : UnitAddCircle)))
        = ∅ :=
      sna_cut_neg_empty Q c hc ψ hψ0 hψ1 hψ01 hcont φ hφ φu hφu t hrelu ρ hρval hQcls hcne hsign
    have hcut_t : diskCut Q (clampedSweep c ψ (rotPresentation Q (t : UnitAddCircle)))
        = classCut Q φu :=
      sna_cut_t_classCut Q c hc ψ hψ0 hψ1 hψ01 hcont φ hφ φu hφu t hrelu ρ hρval hQcls
        hcov hcne hlev hsign
    have hne_cut : diskCut Q (clampedSweep c ψ (rotPresentation Q (t : UnitAddCircle))) ≠ ∅ := by
      rw [hcut_t, ← Set.nonempty_iff_ne_empty]
      exact sna_classCut_nonempty Q φ φu hφ hφu hcov
    rw [sna_sideOf_apply, sna_sideOf_apply, hcoe, side_eq_one_iff.mpr hne_cut,
      side_eq_zero_iff.mpr hcut_neg]
    norm_num


/-! ## 8. The degenerate angles: `(t : UnitAddCircle) = -(t : UnitAddCircle)` -/

/-- `1/2` is its own negative in `ℝ/ℤ` (it differs from `-1/2` by the period `1`); the same holds for
`0` and for `1`. -/
theorem sna_coe_half_eq_neg_coe_half :
    ((1 / 2 : ℝ) : UnitAddCircle) = -(((1 / 2 : ℝ)) : UnitAddCircle) := by
  rw [← AddCircle.coe_neg]
  conv_lhs => rw [show (1 / 2 : ℝ) = -1 / 2 + 1 by norm_num, AddCircle.coe_add_period]
  congr 1
  norm_num

/-- **The apparent exception at the degenerate angles is not one.**  If the angle satisfies
`(t : UnitAddCircle) = -(t : UnitAddCircle)` (equivalently `2t ∈ ℤ`, e.g. `t = 1/2`), then the
hypotheses of `Work.Drive.sideOf_add_neg` are *inconsistent*: by `hrelu` the class line `L` is
preserved by the rotation `projRot (-t) = projRot t`, so the continuous nowhere-vanishing function
`q ↦ ρ q - ρ (projRot (-t) q)` on the preconnected `L` changes sign under `q ↦ projRot (-t) q`,
which is impossible.  Hence the conclusion of `sideOf_add_neg` is vacuous at those angles and no
counterexample can be built there. -/
theorem sna_hypotheses_inconsistent_of_self_neg (Q : ℂ → CappingSpace) (c : ℝ) (hc : 0 < c)
    (ψ : ℝ → ℝ) (t : ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hQcont : Continuous Q)
    (φ : Eucl 3 →L[ℝ] ℝ) (hφ : φ ≠ 0)
    (φu : Eucl 3 →L[ℝ] ℝ) (hφu : φu ≠ 0)
    (hrelu : projLine (LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ))
      = projRot t '' projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ)
    (hρcont : ContinuousOn ρ (projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ))))
    (hρval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ρ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hQcls : ∀ z : ℂ, (cappingSpaceHomeoProj (Q z)).2
      ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)))
    (hcov : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ)),
      ∃ z : ℂ, ‖z‖ ≤ 1 ∧ (cappingSpaceHomeoProj (Q z)).2 = q)
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hlev : ∀ (v : UnitAddCircle) (y : EuclideanSpace ℝ (Fin 2)),
      y ∈ Submission.Drive.unitBox 1 → c ≤ levelOf (rotPresentation Q v y))
    (hne : ∀ q ∈ projLine (LinearMap.ker (φ : Eucl 3 →ₗ[ℝ] ℝ) ⊓
        LinearMap.ker (φu : Eucl 3 →ₗ[ℝ] ℝ)),
      ρ q ≠ ρ (projRot (-t) q))
    (hself : (t : UnitAddCircle) = -(t : UnitAddCircle)) : False := by
  have h := sideOf_add_neg Q c hc ψ t hψ0 hψ1 hψ01 hcont hQcont φ hφ φu hφu hrelu ρ hρcont hρval
    hQcls hcov hcne hlev hne
  have hxy : sideOf Q (fun _ => c) ψ (t : UnitAddCircle)
      = sideOf Q (fun _ => c) ψ (-(t : UnitAddCircle)) :=
    congrArg (fun w => sideOf Q (fun _ => c) ψ w) hself
  rw [hxy] at h
  have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [hxx] at h
  exact zero_ne_one h

end

end Work.Drive
