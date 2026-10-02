import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.Gen.DualLineCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The twisted pullback `ℓ^* ⊗ π^*E`

The bundle `V = ℓ^* ⊗ π^*E` over `P(E)` carries the **tautological nowhere-zero section** (the
inclusion `ℓ ↪ π^*E` read as a section of `Hom(ℓ, π^*E) = ℓ^* ⊗ π^*E`), which is the input of
Whitney's splitting `Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact`; the
splitting of the tautological sequence `0 → ℓ → π^*E → Q → 0` is then the un-twisting by `ℓ`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The twist `ℓ^* ⊗ π^*E`** over `P(E)`, of rank `m` — the bundle whose tautological
nowhere-zero section encodes the inclusion `ℓ ↪ π^*E`. -/
abbrev tautTwist (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    VectorBundleCore ℂ (ProjSpace Z) (EuclideanSpace ℂ (Fin (m + 1)))
      ((ι × Fin (m + 1)) × ι) :=
  twistCore (Work.Gen.dualLineCore (tautLine Z)) (bundleComap Z (projMap Z))

@[simp] theorem tautTwist_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p : (ι × Fin (m + 1)) × ι) :
    (tautTwist Z).baseSet p
      = (Work.Gen.dualLineCore (tautLine Z)).baseSet p.1 ∩ (bundleComap Z (projMap Z)).baseSet p.2 :=
  rfl

@[simp] theorem tautTwist_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (p q : (ι × Fin (m + 1)) × ι) (x : ProjSpace Z) :
    (tautTwist Z).coordChange p q x
      = Work.Gen.scl ((Work.Gen.dualLineCore (tautLine Z)).coordChange p.1 q.1 x)
        • (bundleComap Z (projMap Z)).coordChange p.2 q.2 x :=
  rfl

end

end Work.LerayHirsch
