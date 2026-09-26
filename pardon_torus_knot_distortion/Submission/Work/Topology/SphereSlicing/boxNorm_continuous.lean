import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

namespace Work.Topology.SphereSlicing

open LeanEval.KnotTheory.PardonDistortion

/-- The `i`-th coordinate of `ℝ³` is continuous. -/
theorem continuous_coordR3 (i : Fin 3) : Continuous fun y : R3 => y i :=
  PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i

/-- Each of the three terms occurring in `Submission.boxNorm` is continuous. -/
theorem continuous_boxNorm_term (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Continuous fun y : R3 => |y (σ i) - c (σ i)| / Submission.boxSide i :=
  (((continuous_coordR3 (σ i)).sub continuous_const).abs).div_const _

theorem boxNorm_continuous (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous fun y : LeanEval.KnotTheory.PardonDistortion.R3 => Submission.boxNorm c σ y := by
  have h := continuous_boxNorm_term c σ
  unfold Submission.boxNorm
  exact ((h 0).max (h 1)).max (h 2)

end Work.Topology.SphereSlicing
