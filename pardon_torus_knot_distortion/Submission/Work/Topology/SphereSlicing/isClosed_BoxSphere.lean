import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

open LeanEval.KnotTheory.PardonDistortion

/-- The `i`-th coordinate of `ℝ³` is continuous. -/
theorem continuous_coordR3' (i : Fin 3) : Continuous fun y : R3 => y i :=
  PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i

/-- Each of the three terms occurring in `Submission.boxNorm` is continuous. -/
theorem continuous_boxNorm_term' (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Continuous fun y : R3 => |y (σ i) - c (σ i)| / Submission.boxSide i :=
  (((continuous_coordR3' (σ i)).sub continuous_const).abs).div_const _

/-- The box norm is continuous. -/
theorem boxNorm_continuous' (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous fun y : R3 => Submission.boxNorm c σ y := by
  have h := continuous_boxNorm_term' c σ
  unfold Submission.boxNorm
  exact ((h 0).max (h 1)).max (h 2)

/-- **The box sphere is closed**: it is the level set of the (continuous) box norm, hence the
preimage of the closed singleton `{s}`. -/
theorem isClosed_BoxSphere (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    IsClosed (Work.Topology.SphereSlicing.BoxSphere s c σ) := by
  have hset : BoxSphere s c σ = (fun y : R3 => Submission.boxNorm c σ y) ⁻¹' {s} := rfl
  rw [hset]
  exact isClosed_singleton.preimage (boxNorm_continuous' c σ)

end Work.Topology.SphereSlicing
