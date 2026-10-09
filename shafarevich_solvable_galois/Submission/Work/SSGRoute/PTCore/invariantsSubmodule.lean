import Mathlib
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariants of a finite group action, and the rank of the transpose

The base case of the `Γ`-prime-to-`p` computation of the Euler symmetry
(`Submission/Work/SSGRoute/euler_symm_input.lean`, node `C6`) needs two elementary facts of
`𝔽_p[Γ]`-modules for a finite group `Γ` of order prime to `p`:

* the invariants of a module and of its contragredient dual have the same `𝔽_p`-dimension
  (proved from averaging over `Γ`);
* the rank of a linear map and of its transpose agree (pure linear algebra over a field).

This file provides the vocabulary (`invariantsSubmodule`) and the second fact; the first is
delegated as `Work.SSGRoute.PTCore.pprime_invariants_dual` on top of this module.
-/

namespace Work.SSGRoute.PTCore

set_option linter.style.haveILetI false

/-- **The invariants of a `Γ`-action**, as a submodule: the common fixed points of the action. -/
def invariantsSubmodule (Γ : Type) (R V : Type) [Group Γ] [Semiring R] [AddCommMonoid V]
    [Module R V] [DistribMulAction Γ V] [SMulCommClass Γ R V] : Submodule R V where
  carrier := {v | ∀ γ : Γ, γ • v = v}
  add_mem' := by
    intro a b ha hb γ
    rw [smul_add, ha γ, hb γ]
  zero_mem' := by
    intro γ
    rw [smul_zero]
  smul_mem' := by
    intro c v hv γ
    rw [smul_comm γ c v, hv γ]

/-- Membership in `invariantsSubmodule` is the naive fixed-point condition. -/
@[simp] theorem mem_invariantsSubmodule {Γ : Type} {R V : Type} [Group Γ] [Semiring R]
    [AddCommMonoid V] [Module R V] [DistribMulAction Γ V] [SMulCommClass Γ R V] {v : V} :
    v ∈ invariantsSubmodule Γ R V ↔ ∀ γ : Γ, γ • v = v := Iff.rfl

/-- **The rank of a linear map and of its transpose agree.**

For finite-dimensional vector spaces over a field, `finrank (range f) = finrank (range f.dualMap)`.
This is the rank–nullity theorem applied to `f` and to `f.dualMap`, together with the description
of `ker f.dualMap` as the annihilator of `range f`. -/
theorem finrank_range_eq_finrank_range_dualMap
    (p : ℕ) [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    [AddCommGroup W] [Module (ZMod p) W] [Finite W] (f : V →ₗ[ZMod p] W) :
    Module.finrank (ZMod p) ↥(LinearMap.range f.dualMap)
      = Module.finrank (ZMod p) ↥(LinearMap.range f) := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) W := Module.Finite.of_finite
  haveI : Finite (DualMod p W) :=
    Finite.of_injective (fun g : DualMod p W => (g : W → ZMod p)) DFunLike.coe_injective
  haveI : Module.Finite (ZMod p) (DualMod p W) := Module.Finite.of_finite
  -- rank--nullity for the transpose, with the kernel described by the annihilator
  have h2 : Module.finrank (ZMod p) ↥(LinearMap.range f.dualMap)
      + Module.finrank (ZMod p) ↥(LinearMap.ker f.dualMap)
      = Module.finrank (ZMod p) (DualMod p W) :=
    LinearMap.finrank_range_add_finrank_ker f.dualMap
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range] at h2
  -- the annihilator of `range f` has codimension `finrank (range f)` in `W`
  have h3 : Module.finrank (ZMod p) ↥((LinearMap.range f).dualAnnihilator)
      + Module.finrank (ZMod p) ↥(LinearMap.range f) = Module.finrank (ZMod p) W := by
    simpa [add_comm] using Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have hdualW : Module.finrank (ZMod p) (DualMod p W) = Module.finrank (ZMod p) W :=
    Subspace.dual_finrank_eq
  omega

end Work.SSGRoute.PTCore
