import Mathlib
import Submission.Work.Drive.cutClassImage
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.sideOf_profileData
import Submission.Work.Drive.sideOf_add_neg

/-!
# The covariant profile of the rotation family, and the bridge in base coordinates

With the *covariant* choice of the rotated profiles — the profile of the rotated plane at the angle `t`
is `FQ ∘ projRot (-t)` where `FQ` is the profile of the chart's own plane — the profile of the plane of
angle `t` at the class `projRot t q` equals `FQ q`, so the profile difference of the pair
`(P_0, P_t)` at the class `projRot t q` is `FQ (projRot t q) - FQ q`: a single function of the base
class `q` alone.  This is what turns the *transitivity* of the order into the **function identity**

> `(FQ ∘ projRot (a+c) - FQ) = (FQ ∘ projRot a - FQ) ∘ projRot c + (FQ ∘ projRot c - FQ)`,

i.e. the chain of the linear-plane proof becomes an algebraic identity, the only geometric input being
the *sign constancy* on the connected union `Y ∪ projRot c '' Y` (see `Drive/add_sign_of_chain`).

This file provides the bridge of `Submission/Work/Drive/sideOf_profileData.lean` in those *base*
coordinates.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Set

noncomputable section

/-- **The class of a rotated configuration point.** -/
theorem cls_rotCapping_coe (t : ℝ) (X : CappingSpace) :
    (cappingSpaceHomeoProj (rotCapping (t : UnitAddCircle) X)).2
      = projRot t ((cappingSpaceHomeoProj X).2) :=
  sna_cls_rotCapping t X

/-- **The class of a rotated presentation point.** -/
theorem cls_rotPresentation (Q : ℂ → CappingSpace) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (rotPresentation Q (t : UnitAddCircle) y)).2
      = projRot t ((cappingSpaceHomeoProj (diskPlane Q y)).2) :=
  sna_cls_rotCapping t (diskPlane Q y)

/-- **The class image of a rotated presentation is the rotation of the base class image.** -/
theorem classImage_rotPresentation (Q : ℂ → CappingSpace) (t : ℝ) :
    classImage (rotPresentation Q (t : UnitAddCircle))
      = projRot t '' classImage (diskPlane Q) := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(cappingSpaceHomeoProj (diskPlane Q y)).2, ⟨y, hy, rfl⟩, (cls_rotPresentation Q t y).symm⟩
  · rintro ⟨q', ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, cls_rotPresentation Q t y⟩

/-- **The bridge in base coordinates, for the covariant profile.**  With `FQ` the (continuous) profile
of the chart's plane, the rotated plane's profile `FQ ∘ projRot (-t)` is the value of `FQ` at the
rotated class, so the side value at the angle `t` is the profile comparison read on the *base* class
image `classImage (diskPlane Q)`:

> `sideOf Q c ψ (t : UnitAddCircle) = 1 ↔ ∀ q ∈ classImage (diskPlane Q), FQ (projRot t q) < FQ q`. -/
theorem sideOf_eq_one_iff_profile_covariant (Q : ℂ → CappingSpace) (hQ : Continuous Q)
    (c : UnitAddCircle → ℝ) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ψ s ∈ Set.Icc (0 : ℝ) 1)
    (hcontψ : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (t : ℝ)
    (FQ : Projectivization ℝ (Eucl 3) → ℝ) (hFQc : Continuous FQ)
    (hFQval : ∀ z : ℂ, ‖z‖ ≤ 1 →
      FQ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (hc : 0 < c (t : UnitAddCircle))
    (hcne : ∀ z : ℂ, ‖z‖ ≤ 1 → c (t : UnitAddCircle) ≤ levelOf (Q z))
    (hlev : ∀ y ∈ Submission.Drive.unitBox 1,
      c (t : UnitAddCircle) ≤ levelOf (rotPresentation Q (t : UnitAddCircle) y))
    (hne : ∀ q ∈ classImage (diskPlane Q), FQ (projRot t q) ≠ FQ q)
    (hccne : classCutSet Q (classImage (rotPresentation Q (t : UnitAddCircle))) ≠ ∅) :
    sideOf Q c ψ (t : UnitAddCircle) = 1 ↔
      ∀ q ∈ classImage (diskPlane Q), FQ (projRot t q) < FQ q := by
  have hG : Continuous (fun q : Projectivization ℝ (Eucl 3) => FQ (projRot (-t) q)) :=
    hFQc.comp (sna_continuous_projRot (-t))
  have hval := sideOf_eq_one_iff_profile_of_classImage Q hQ c ψ hψ0 hψ1 hψ01 hcontψ
    (t : UnitAddCircle) hc FQ (fun q => FQ (projRot (-t) q)) hFQc hG hFQval
    (fun y hy => by
      rw [cls_rotPresentation Q t y, sna_projRot_neg t ((cappingSpaceHomeoProj (diskPlane Q y)).2),
        show (cappingSpaceHomeoProj (diskPlane Q y)).2
          = (cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2 from rfl,
        hFQval _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox y)),
        show rotPresentation Q ((t : ℝ) : UnitAddCircle) y
          = rotCapping ((t : ℝ) : UnitAddCircle) (Q (sqDisk (foldBox y))) from rfl,
        sna_levelOf_rotCapping t _])
    hcne hlev
    (fun q hq => by
      rw [classImage_rotPresentation Q t] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [sna_projRot_neg t q']
      exact hne q' hq')
    hccne
  rw [hval, classImage_rotPresentation Q t]
  constructor
  · intro h q hq
    have hh := h (projRot t q) ⟨q, hq, rfl⟩
    rwa [sna_projRot_neg t q] at hh
  · rintro h q ⟨q', hq', rfl⟩
    rw [sna_projRot_neg t q']
    exact h q' hq'

end

end Work.Drive
