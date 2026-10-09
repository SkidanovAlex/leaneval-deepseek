import Mathlib
import Submission.Work.Shrinking.Basic
import Submission.Work.SSGRoute.PTCore.invariantsSubmodule
import Submission.Work.ArtinInduction.LatticeModp.Infra
import Submission.Work.SSGRoute.E7Fin.RedLattice.F
import Submission.Work.SSGRoute.E7Fin.RedLattice.Regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The additive invariant `X ↦ dim (X ⊗ N)^G`

Lane `Work.SSGRoute.coker_obstruction_pt`.  The `(ε)` identity of this lane
(`RedRhoF_localLevelIntegers_of_basis`, `RedLattice/LevelEpsilonFinal.lean`) is stated for an
arbitrary **additive invariant** `ρ : Inv p G` of finite `𝔽_p[G]`-modules:

  `ρ (𝒪_{L_v}/p𝒪_{L_v}) = n · ρ (𝔽_p[G])`.

This file supplies the *invariant that the arithmetic chapter actually consumes*, namely the
dimension of the `G`-invariants of `X ⊗ N` for a fixed finite `𝔽_p[G]`-module `N`:

  `invDimFunctional p G N := fun X ↦ dim (X ⊗ N)^G`

(with the diagonal `G`-action on `X ⊗ N` supplied by `Work.Shrinking.instDistribMulActionTensorProduct`,
which is a global instance).

For `p ∤ |G|` this is an additive invariant — a `G`-equivariant short exact sequence of finite
`𝔽_p[G]`-modules splits (Maschke), and the invariant dimension is additive over direct sums — so the
`(ε)` identity specialises to

  `dim ((𝒪_{L_v}/p𝒪_{L_v}) ⊗ N)^G = n · dim N`,

which is the `Λ/pΛ ≅ 𝔽_p[Γ]^n` input of Milne *ADT* I.2.11 in the form the Euler-characteristic
engine (`E7Fin.hasUniformConstant_of_structure`, `E7Fin.diagTensorInvariants_of_structure`) consumes.
The two facts are delegated as
`RedLattice.invDimFunctional_isAddInv` and `RedLattice.invDimFunctional_regMod`.

## Contents

* `RedLattice.invDimFunctional` — the invariant `X ↦ dim (X ⊗ N)^G` as an element of `Inv p G`.
-/

namespace Work.SSGRoute.E7Fin.RedLattice

open Work.ArtinInduction.LatticeModp

/-- **The invariant `X ↦ dim (X ⊗ N)^G`**, as an additive invariant of finite `𝔽_p[G]`-modules
(the diagonal action on the tensor product is `Work.Shrinking.instDistribMulActionTensorProduct`). -/
noncomputable def invDimFunctional (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] : Inv p G :=
  fun X _ _ _ _ _ =>
    Module.finrank (ZMod p)
      ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) (TensorProduct (ZMod p) X N))

end Work.SSGRoute.E7Fin.RedLattice
