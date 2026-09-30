import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.Models
import Submission.Work.SSSR.StemsB.Fibrations
import Submission.Work.SSSR.Cohomology.Chains
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open CategoryTheory
namespace Work.SSSR.PiS

noncomputable section

/-- Integral singular homology `H_i(X;ℤ)`. -/
abbrev HZ (R : Type) [CommRing R] [Nontrivial R] (X : Type) [TopologicalSpace X] (i : ℕ) : ModuleCat R :=
  (Work.SSSR.Cohomology.singularChains R (TopCat.of X)).homology i

/-- `X` is path connected and simply connected (cube model: `π₀` and `π₁` at `x` are trivial). -/
def SimplyConn (X : Type) [TopologicalSpace X] (x : X) : Prop :=
  Subsingleton (HomotopyGroup.Pi 0 X x) ∧ Subsingleton (HomotopyGroup.Pi 1 X x)

end

end Work.SSSR.PiS
