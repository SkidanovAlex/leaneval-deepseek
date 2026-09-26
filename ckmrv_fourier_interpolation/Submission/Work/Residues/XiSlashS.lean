import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

/-- The `S`-slash (`τ ↦ -1/τ`) of the two theta quartics `ξ₂ = U+W` (weight 2) and
`ξ₄ = U²+W²-2V²` (weight 4).  Pointwise versions are already proved in the workspace
(`Work.Kernels.KernelFacts.xi2Fun_slash_S`, `Work.Kernels.KernelFacts.KMinus_T2`). -/
theorem XiSlashS :
    ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) =
        fun τ : UpperHalfPlane => -(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) ∧
    ((Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) =
        fun τ : UpperHalfPlane =>
          Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2) := by
  refine ⟨funext (fun τ => ?_), funext (fun τ => ?_)⟩
  · exact Work.Kernels.KernelFacts.xi2Fun_slash_S τ
  · exact Work.Kernels.KernelFacts.xi4S_apply τ

end Work.Residues
