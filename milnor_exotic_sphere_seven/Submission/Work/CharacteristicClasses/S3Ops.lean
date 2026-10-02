import Mathlib
import Submission.Work.Milnor.QuatSphere

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The unit quaternions `S³` as a group, and the standard operations on it

`Submission.Milnor.QS3` is the unit sphere of the quaternions, i.e. `S³ = Sp(1)`.  This file
provides the group operations on it (`s3Mul`, `s3One`, `s3Inv`) together with their continuity,
so that the characteristic-class chapter can speak of *pointwise products* of maps `S³ → S³` —
the operation under which the second Chern class of quaternionic line bundles is additive (the
H-space/Hopf additivity of degrees).

The operations are *not* registered as global instances: the chapter only needs them where they
are applied to continuous maps, and keeping them as plain definitions avoids any interaction with
the existing `Metric.sphere` API of the workspace.
-/

namespace Work.CharacteristicClasses

open scoped Topology
open Metric

noncomputable section

/-- `S³`, the unit sphere of the quaternions (the group `Sp(1)`). -/
abbrev S3 : Type := Submission.Milnor.QS3

/-- The unit quaternion `1` of `S³`. -/
def s3One : S3 :=
  ⟨1, by simp [Metric.mem_sphere]⟩

/-- Quaternion multiplication, restricted to unit quaternions: `S³ × S³ → S³`. -/
def s3Mul (x y : S3) : S3 :=
  ⟨(x : Quaternion ℝ) * (y : Quaternion ℝ), by
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, Submission.Milnor.norm_coe,
      Submission.Milnor.norm_coe, one_mul]⟩

/-- Quaternion conjugation, restricted to unit quaternions: the inverse map of `S³`. -/
def s3Inv (x : S3) : S3 :=
  ⟨star (x : Quaternion ℝ), by
    rw [Metric.mem_sphere, dist_zero_right, Quaternion.norm_star]
    exact Submission.Milnor.norm_coe x⟩

@[simp] lemma s3One_coe : ((s3One : S3) : Quaternion ℝ) = 1 := rfl
@[simp] lemma s3Mul_coe (x y : S3) : ((s3Mul x y : S3) : Quaternion ℝ) =
    (x : Quaternion ℝ) * (y : Quaternion ℝ) := rfl
@[simp] lemma s3Inv_coe (x : S3) : ((s3Inv x : S3) : Quaternion ℝ) = star (x : Quaternion ℝ) := rfl

lemma continuous_s3Mul : Continuous (fun p : S3 × S3 => s3Mul p.1 p.2) :=
  Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)) _

lemma continuous_s3Inv : Continuous s3Inv :=
  Continuous.subtype_mk (continuous_star.comp continuous_subtype_val) _

@[simp] lemma s3Mul_one (x : S3) : s3Mul x s3One = x := by
  refine Subtype.ext ?_
  simp [s3Mul, s3One]

@[simp] lemma s3One_mul (x : S3) : s3Mul s3One x = x := by
  refine Subtype.ext ?_
  simp [s3Mul, s3One]

lemma s3Mul_assoc (x y z : S3) : s3Mul (s3Mul x y) z = s3Mul x (s3Mul y z) := by
  refine Subtype.ext ?_
  simp [s3Mul, mul_assoc]

/-- `x * x⁻¹ = 1` in the unit quaternions (the inverse is conjugation, because `‖x‖ = 1`). -/
lemma s3Mul_inv (x : S3) : s3Mul x (s3Inv x) = s3One := by
  refine Subtype.ext ?_
  have h : (x : Quaternion ℝ) * star (x : Quaternion ℝ) = ((Quaternion.normSq (x : Quaternion ℝ) : ℝ) : Quaternion ℝ) :=
    Quaternion.self_mul_star _
  have h2 : Quaternion.normSq (x : Quaternion ℝ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, Submission.Milnor.norm_coe, mul_one]
  simp only [s3Mul_coe, s3Inv_coe, s3One_coe, h, h2, Quaternion.coe_one]

end

end Work.CharacteristicClasses

namespace Work.CharacteristicClasses

open scoped Topology
open Metric

noncomputable section

/-- The constant map `S³ → S³` with value `1`. -/
def s3OneCm : C(S3, S3) := ContinuousMap.const S3 s3One

/-- The pointwise product of two continuous self-maps of `S³`: `q ↦ f q * g q`.  This is the
H-space product whose effect on degrees is additive (the Hopf formula). -/
def s3MulCm (f g : C(S3, S3)) : C(S3, S3) :=
  ⟨fun q => s3Mul (f q) (g q),
    continuous_s3Mul.comp (f.continuous.prodMk g.continuous)⟩

/-- The inverse map `q ↦ q⁻¹` on `S³` (= conjugation), as a continuous map. -/
def s3InvCm : C(S3, S3) := ⟨s3Inv, continuous_s3Inv⟩

/-- The squaring map `q ↦ q²` on `S³`. -/
def s3Sq : C(S3, S3) := s3MulCm (ContinuousMap.id S3) (ContinuousMap.id S3)

@[simp] lemma s3OneCm_apply (q : S3) : s3OneCm q = s3One := rfl
@[simp] lemma s3MulCm_apply (f g : C(S3, S3)) (q : S3) : s3MulCm f g q = s3Mul (f q) (g q) := by
  simp [s3MulCm]
@[simp] lemma s3InvCm_apply (q : S3) : s3InvCm q = s3Inv q := rfl
@[simp] lemma s3Sq_apply (q : S3) : s3Sq q = s3Mul q q := by
  simp [s3Sq]

end

end Work.CharacteristicClasses
