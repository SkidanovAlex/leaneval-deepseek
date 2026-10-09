import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Shafarevich
import Submission.Crossing
import Submission.CoprimeProduct
import Submission.ClassicalRoute
import Submission.Work.SSGRoute.ZConstruction.genericKernelSolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

theorem shafarevich_solvable_galois (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
      Nonempty (G ≃* (K ≃ₐ[ℚ] K)) :=
  -- final assembly 2026-10-08: the kernel step comes from
  -- ZConstruction.minimalNormalKernelStep_proved (not the sorry of Submission.minimalNormalKernelStep)
  Work.SSGRoute.ZConstruction.shafarevich_solvable_galois_of_genericKernel G

end Submission
