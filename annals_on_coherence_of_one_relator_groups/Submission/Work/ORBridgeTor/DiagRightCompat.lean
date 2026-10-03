/-
# Compatibility of `Work.ORFlatness.diagRightModule` with the `K`-scalars

The right diagonal `K[G]`-module structure `Work.ORFlatness.diagRightModule` on `S ⊗[K] X` is
built by `Module.compHom` from a ring homomorphism, so the `K`-scalar action and the
`(K[G])ᵐᵒᵖ`-action are compatible only up to a small computation.  This file records the three
facts needed to apply Jaikin-Zapirain--Linton Lemma 5.2(2) (whose first variable is a right
`K[G]`-module with a compatible `K`-action) to the module `S ⊗[K] X` of N9's `hswap`:

* `diagRightModule_algebraMap_smul` — the action of a scalar `algebraMap K ((K[G])ᵐᵒᵖ) c` is the
  `K`-scalar action;
* `smulCommClass_diagRightModule` — `SMulCommClass K (K[G])ᵐᵒᵖ (S ⊗[K] X)`;
* `isScalarTower_diagRightModule` — `IsScalarTower K (K[G])ᵐᵒᵖ (S ⊗[K] X)`.
-/
import Submission.Work.ORBridgeTor.Mirror

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
variable (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
variable [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]

/-- The scalar action of `algebraMap K ((K[G])ᵐᵒᵖ) c` on `S ⊗[K] X` (for the right diagonal
structure) is the `K`-scalar action. -/
theorem diagRightModule_algebraMap_smul (c : K) (z : S ⊗[K] X) :
    letI := Work.ORFlatness.diagRightModule K G S φ X
    (algebraMap K ((MonoidAlgebra K G)ᵐᵒᵖ)) c • z = c • z := by
  letI := Work.ORFlatness.diagRightModule K G S φ X
  letI := Work.ORFlatness.diagModuleR K G S φ X
  show Work.ORFlatness.diagRingHomR K G S φ X
      (Work.ORFlatness.opRingHom K G (algebraMap K ((MonoidAlgebra K G)ᵐᵒᵖ) c)) z = c • z
  rw [show (algebraMap K ((MonoidAlgebra K G)ᵐᵒᵖ)) c
      = MulOpposite.op (MonoidAlgebra.single (1 : G) c) from rfl,
    Work.ORFlatness.opRingHom_op_single, Work.ORFlatness.diagRingHomR_single,
    Work.ORFlatness.diagLinR_one]
  rfl

/-- The `K`-action on `S ⊗[K] X` commutes with the right diagonal `(K[G])ᵐᵒᵖ`-action. -/
theorem smulCommClass_diagRightModule :
    letI := Work.ORFlatness.diagRightModule K G S φ X
    SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] X) := by
  letI := Work.ORFlatness.diagRightModule K G S φ X
  refine ⟨fun c a z => ?_⟩
  show c • (diagRightAct K G S φ X a z) = diagRightAct K G S φ X a (c • z)
  exact (map_smul (Work.ORFlatness.diagRingHomR K G S φ X
    (Work.ORFlatness.opRingHom K G a)) c z).symm

/-- The `K`-action on `S ⊗[K] X` is a scalar tower over the right diagonal `(K[G])ᵐᵒᵖ`-action. -/
theorem isScalarTower_diagRightModule :
    letI := Work.ORFlatness.diagRightModule K G S φ X
    IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] X) := by
  letI := Work.ORFlatness.diagRightModule K G S φ X
  refine ⟨fun c a z => ?_⟩
  show (c • a) • z = c • (a • z)
  rw [Algebra.smul_def, mul_smul,
    diagRightModule_algebraMap_smul K G S φ X c (a • z)]

end Work.ORBridgeTor
