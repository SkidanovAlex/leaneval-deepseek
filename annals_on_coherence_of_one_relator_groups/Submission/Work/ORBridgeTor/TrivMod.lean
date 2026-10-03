/-
# The trivial left `K[G]`-module structure on `K`

Needed to write a left `K[G]`-module `N` as `K ⊗[K] N`, which is the shape in which
Jaikin-Zapirain--Linton Lemma 5.2(2) (`Work.ORHomAlg.JL52.jl_5_2_2`, whose second variable is a
diagonal tensor `M ⊗[K] N`) takes its arguments when one runs it in both directions
(mismatch (M4)).

The action is `x • k = ε(x) · k` where `ε` is the augmentation `K[G] → K`, so that
`single g 1 • k = k` — the trivial `G`-action.
-/
import Mathlib
import Submission.Work.ORHomAlg.GroupAlgebra
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.ORBridgeTor

section Triv

variable (K : Type u) [Field K] (G : Type u) [Group G]

/-- The trivial left `K[G]`-module structure on `K`: `x • k = ε(x) · k`, with `ε` the
augmentation. -/
noncomputable instance instTrivLeftModule : Module (MonoidAlgebra K G) K :=
  Module.compHom K (Work.ORHomAlg.augmentation K G)

theorem instTrivLeftModule_smul (x : MonoidAlgebra K G) (k : K) :
    x • k = Work.ORHomAlg.augmentation K G x * k := rfl

@[simp] theorem instTrivLeftModule_single (g : G) (k : K) :
    (MonoidAlgebra.single g (1 : K)) • k = k := by
  rw [instTrivLeftModule_smul, Work.ORHomAlg.JL52.augmentation_single, one_mul]

@[simp] theorem instTrivLeftModule_one (k : K) : (1 : MonoidAlgebra K G) • k = k := by
  rw [instTrivLeftModule_smul, map_one, one_mul]

/-- The `K`-action on `K` commutes with the trivial `K[G]`-action. -/
instance instSMulCommClassTrivLeft : SMulCommClass K (MonoidAlgebra K G) K where
  smul_comm c x k := by
    rw [instTrivLeftModule_smul, instTrivLeftModule_smul]
    ring

end Triv

end Work.ORBridgeTor
