import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

namespace Work.Kernels.TildeFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- The coefficient matrix `Υ_-^{(d)}` depends on its second (upper-half-plane) argument
only through `T`-invariant data: the discriminant `Δ`, the modular `j`-invariant, and the
level-one modular forms `E₆, E₈, E₁₀` (via `PiMat`).  Hence it is invariant under the
translation `z ↦ z + 1 = (1 : ℝ) +ᵥ z`. -/
theorem UpsilonMinus_vadd_one_z (d : ℕ) (τ : UpperHalfPlane) (i j : Fin 3) (z : UpperHalfPlane) :
    Work.Kernels.UpsilonMinus d τ ((1 : ℝ) +ᵥ z) i j = Work.Kernels.UpsilonMinus d τ z i j := by
  simp only [Work.Kernels.UpsilonMinus]
  split_ifs with h8 h24 <;>
    simp only [Work.Kernels.KernelFacts.PiMat_vadd_one,
      Work.Kernels.KernelFacts.jInvariantFun_vadd_one,
      Work.Kernels.KernelFacts.DeltaFun_vadd_one]

end Work.Kernels.TildeFacts
