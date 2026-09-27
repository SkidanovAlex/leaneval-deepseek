/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The unit octonions `S⁷` as an H-space

The unit sphere of the octonion algebra `𝕆 = WithLp 2 (ℍ × ℍ)` (see
`Submission/Work/Octonion/Basic.lean`) inherits a multiplication, a unit and hence an `HSpace`
structure which is *not* that of a topological group, the octonion multiplication being neither
associative nor commutative.

Because the octonions are not associative, the usual `Submonoid.unitSphere` construction (which
produces a monoid) is unavailable; the instances below are built directly with
`Submission.unitSphereMul`, `Submission.unitSphereOne` and
`IsTopologicalGroup.toHSpace` (which only needs `MulOneClass` and `ContinuousMul`).
-/
import Submission.Work.HSpace.Basic
import Submission.Work.Octonion.Basic
import Submission.Work.Octonion.one_mul
import Submission.Work.Octonion.mul_one
import Submission.Work.Octonion.norm_one
import Submission.Work.Octonion.norm_mul
import Submission.Work.Octonion.continuous_mul

namespace Submission

namespace Octonion

/-- The octonion multiplication is continuous. -/
noncomputable instance continuousMul : ContinuousMul Octonion :=
  ⟨Work.Octonion.continuous_mul⟩

/-- Multiplication on the unit sphere of `𝕆`, inherited from the octonion product. -/
noncomputable instance unitSphereMul : Mul (Metric.sphere (0 : Octonion) 1) :=
  Submission.unitSphereMul Work.Octonion.norm_mul

/-- The unit `(1, 0)` of `𝕆` lies on the unit sphere. -/
noncomputable instance unitSphereOne : One (Metric.sphere (0 : Octonion) 1) :=
  Submission.unitSphereOne Work.Octonion.norm_one

/-- The unit sphere of `𝕆` is a `MulOneClass` (but not a monoid: `𝕆` is not associative). -/
noncomputable instance unitSphereMulOneClass : MulOneClass (Metric.sphere (0 : Octonion) 1) :=
  { one_mul := fun x => Subtype.ext (Work.Octonion.one_mul x.1)
    mul_one := fun x => Subtype.ext (Work.Octonion.mul_one x.1) }

/-- The multiplication on the unit sphere of `𝕆` is continuous. -/
noncomputable instance unitSphereContinuousMul : ContinuousMul (Metric.sphere (0 : Octonion) 1) :=
  ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)) _⟩

/-- **`S⁷` is an H-space**. -/
noncomputable instance unitSphereHSpace : HSpace (Metric.sphere (0 : Octonion) 1) :=
  IsTopologicalGroup.toHSpace _

end Octonion

end Submission
