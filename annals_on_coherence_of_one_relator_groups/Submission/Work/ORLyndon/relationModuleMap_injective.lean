import Mathlib
import Submission.Work.ORLyndon.Lyndon

/-!
# Injectivity of `K[G]/K[G](u-1) → K[G]^X`

The relation module `K[G] ⧸ K[G](u-1)` of the one-relator presentation maps to the free module
`K[G]^X` through the Fox derivative vector `θ` (`Work.ORLyndon.relationModuleMap`).  Since the
Lyndon identity hypothesis identifies `K[G](u-1)` with the kernel of `θ`
(`Work.ORLyndon.LyndonIdentity.ker_theta`), the induced quotient map is injective: an element of
the quotient dies only if it lies in the kernel that was divided out.
-/

namespace Work.ORLyndon

open MonoidAlgebra

theorem relationModuleMap_injective {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    {r u : FreeGroup X} {l : ℕ} (h : Work.ORLyndon.LyndonIdentity K X r u l) :
    Function.Injective (Work.ORLyndon.relationModuleMap K r u l h) := by
  rw [← LinearMap.ker_eq_bot]
  unfold relationModuleMap
  exact Submodule.ker_liftQ_eq_bot' _ _ h.ker_theta.symm

end Work.ORLyndon
