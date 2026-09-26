import Mathlib
import Submission.Work.Modular.ThetaImagAxis

namespace Work.Modular

open Work.Modular
open scoped Real MatrixGroups
open UpperHalfPlane

/-- The modular `S`-action on the imaginary axis: `S • (i t) = i / t` for `t > 0`. -/
lemma imagPoint_S_smul {t : ℝ} (ht : 0 < t) :
    ModularGroup.S • imagPoint t = imagPoint (1 / t) := by
  -- `S` acts on `ℍ` by `z ↦ -1/z`, so on the imaginary axis we get
  -- `S • (i t) = -(i t)⁻¹ = i/t`; compare the two complex numbers.
  have hS : ((ModularGroup.S • imagPoint t : ℍ) : ℂ) = (-(↑(imagPoint t)))⁻¹ :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (imagPoint t))
  apply UpperHalfPlane.ext
  rw [hS, coe_imagPoint ht, coe_imagPoint (one_div_pos.mpr ht)]
  field_simp
  rw [pow_two, Complex.I_mul_I]
  push_cast
  ring

end Work.Modular
