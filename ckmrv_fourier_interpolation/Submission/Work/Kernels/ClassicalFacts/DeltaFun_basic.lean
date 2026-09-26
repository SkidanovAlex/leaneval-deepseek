/-
# Basic facts about `Δ` and the `j`-invariant

Elementary consequences of the definitions in `Submission/Work/Kernels/Classical.lean`.
-/
import Mathlib
import Submission.Work.Kernels.Classical

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.ClassicalFacts

/-- `Δ` does not vanish on `ℍ`. -/
lemma DeltaFun_ne_zero : ∀ τ : UpperHalfPlane, Work.Kernels.DeltaFun τ ≠ 0 := by
  intro τ
  simpa only [Work.Kernels.DeltaFun, CuspForm.coe_discriminant] using ModularForm.discriminant_ne_zero τ

/-- `Δ · j = E₄³`, the defining relation of the `j`-invariant. -/
lemma DeltaFun_mul_jInvariantFun : ∀ τ : UpperHalfPlane,
    Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ = Work.Kernels.E4Fun τ ^ 3 := by
  intro τ
  have h := DeltaFun_ne_zero τ
  simp only [Work.Kernels.jInvariantFun]
  field_simp

end Work.Kernels.ClassicalFacts
