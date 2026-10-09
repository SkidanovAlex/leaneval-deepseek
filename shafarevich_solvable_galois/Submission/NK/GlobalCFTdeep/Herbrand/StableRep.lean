/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G`-stable additive subgroups as `ℤ[G]`-modules

The action of a group `G` on an additive group `M` restricts to any `G`-stable additive subgroup
`H ≤ M`, giving `H` the structure of a `ℤ[G]`-module (`Rep ℤ G`).  This is the additive analogue
of `NK.GlobalCFTdeep.stableMulDistribMulAction` and is used to see the log lattice, the divisor
lattice and the sum-zero hyperplane inside `∏_{w ∈ T} ℝ` as `ℤ[Gal(L/K)]`-modules.

## Main definitions

* `NK.GlobalCFTdeep.stableDistribMulActionSubgroup`;
* `NK.GlobalCFTdeep.repOfStableAddSubgroup`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace NK.GlobalCFTdeep

/-- A `G`-stable additive subgroup of a `G`-module is itself a `G`-module. -/
noncomputable def stableDistribMulActionSubgroup {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) : DistribMulAction G H where
  smul g x := ⟨g • (x : M), hH g x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : M))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : M) (y : M))

/-- The action of `G` on a stable additive subgroup, unfolded. -/
theorem stableDistribMulActionSubgroup_smul_apply {G : Type*} [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) (g : G) (x : H) :
    letI := stableDistribMulActionSubgroup H hH
    ((g • x : H) : M) = g • (x : M) := rfl

/-- A `G`-stable additive subgroup of a `ℤ[G]`-module, as a `ℤ[G]`-module. -/
noncomputable def repOfStableAddSubgroup {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [Module ℤ M] [DistribMulAction G M] [SMulCommClass G ℤ M] (H : AddSubgroup M)
    (hH : ∀ (g : G) {x : M}, x ∈ H → g • x ∈ H) : Rep ℤ G :=
  letI := stableDistribMulActionSubgroup H hH
  Rep.ofDistribMulAction ℤ G H

end NK.GlobalCFTdeep
