import Mathlib
import Submission.Work.Analysis.CzShift.Defs

/-!
# The formal adjoint of a finite sum of convolution operators

For a kernel family `K : ι → ℝ → ℂ` the *formal adjoint* (in the sense of `L²` duality) of the
convolution operator `czOp D K ε` is the convolution operator with kernel family
`K* i x = conj (K i (-x))` and conjugates signs `conj ∘ ε`:

`(czOp D K ε)† = czOp D (adjKernel K) (adjSigns ε)`.

This module only sets up the vocabulary; the adjointness identity itself
(`Work.Analysis.CzShift.czOp_adjoint_pairing`) and the `L²` bound transfer
(`Work.Analysis.CzShift.adjoint_l2_bound`) live in separate modules.
-/

namespace Work.Analysis.CzShift

open MeasureTheory

set_option autoImplicit false

/-- The reflected-conjugate (formal adjoint) kernel family of `K`: `adjKernel K i x = conj (K i (-x))`. -/
noncomputable def adjKernel {ι : Type*} (K : ι → ℝ → ℂ) : ι → ℝ → ℂ :=
  fun i x => star (K i (-x))

/-- The conjugated sign family of `ε`. -/
noncomputable def adjSigns {ι : Type*} (ε : ι → ℂ) : ι → ℂ := fun i => star (ε i)

@[simp] theorem adjKernel_apply {ι : Type*} (K : ι → ℝ → ℂ) (i : ι) (x : ℝ) :
    adjKernel K i x = star (K i (-x)) := rfl

@[simp] theorem adjSigns_apply {ι : Type*} (ε : ι → ℂ) (i : ι) : adjSigns ε i = star (ε i) := rfl

theorem norm_adjKernel {ι : Type*} (K : ι → ℝ → ℂ) (i : ι) (x : ℝ) :
    ‖adjKernel K i x‖ = ‖K i (-x)‖ := by simp

theorem norm_adjSigns {ι : Type*} (ε : ι → ℂ) (i : ι) : ‖adjSigns ε i‖ = ‖ε i‖ := by simp

theorem adjKernel_neg {ι : Type*} (K : ι → ℝ → ℂ) (i : ι) (x : ℝ) :
    adjKernel K i (-x) = star (K i x) := by simp

end Work.Analysis.CzShift
