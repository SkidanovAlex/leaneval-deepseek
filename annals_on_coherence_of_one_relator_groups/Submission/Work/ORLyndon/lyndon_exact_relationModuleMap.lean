import Mathlib
import Submission.Work.ORLyndon.Lyndon

namespace Work.ORLyndon

theorem lyndon_exact_relationModuleMap {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    {r u : FreeGroup X} {l : ℕ} (h : Work.ORLyndon.LyndonIdentity K X r u l) :
    LinearMap.range (Work.ORLyndon.relationModuleMap K r u l h) =
      LinearMap.ker (Work.ORLyndon.lyndonDelta (K := K) r) := by
  rw [relationModuleMap, Submodule.range_liftQ]
  exact h.range_theta

end Work.ORLyndon
