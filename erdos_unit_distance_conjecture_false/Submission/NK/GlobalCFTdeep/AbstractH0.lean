/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The group `Ĥ⁰(G, M) = M^G ⧸ N_G M` in multiplicative notation

Let `G` be a finite group acting on a commutative group `M` by group automorphisms.  This file
provides the elementary model of the degree-zero Tate cohomology group `Ĥ⁰(G, M)`:

* `NK.GlobalCFTdeep.normHom G M : M →* M`, the norm `x ↦ ∏_{g : G} g • x`;
* `NK.GlobalCFTdeep.fixedSubgroup G M`, the subgroup `M^G` of `G`-fixed points, which contains
  the range of the norm;
* `NK.GlobalCFTdeep.H0 G M := M^G ⧸ N_G M`, the quotient.

For a finite Galois extension `L / K` of number fields and `M = C_L` with the Galois action, the
`H⁰`-computation of global class field theory identifies `H0 (Gal(L/K)) C_L` with
`C_K ⧸ N_{L/K} C_L`, so `Nat.card (H0 …)` is the norm index `[C_K : N_{L/K} C_L]`.

This is the form in which the second inequality is proved: restriction to a Sylow subgroup is an
isomorphism on `p`-primary parts away from the index, which reduces the general case to the
solvable (in fact `p`-group) case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped BigOperators

noncomputable section

namespace NK.GlobalCFTdeep

variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [CommGroup M] [MulDistribMulAction G M]

/-- The **norm** of a finite group action on a commutative group, in multiplicative notation:
`normHom G M x = ∏_{g : G} g • x`. -/
def normHom (G : Type*) [Group G] [Fintype G] (M : Type*) [CommGroup M]
    [MulDistribMulAction G M] : M →* M where
  toFun x := ∏ g : G, g • x
  map_one' := by simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => smul_mul' g x y

@[simp] theorem normHom_apply (x : M) : normHom G M x = ∏ g : G, g • x := rfl

/-- The subgroup of `G`-fixed points of `M`. -/
def fixedSubgroup (G : Type*) [Group G] (M : Type*) [CommGroup M] [MulDistribMulAction G M] :
    Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' := by simp
  mul_mem' hx hy g := by rw [smul_mul', hx g, hy g]
  inv_mem' hx g := by rw [smul_inv', hx g]

@[simp] theorem mem_fixedSubgroup {x : M} :
    x ∈ fixedSubgroup G M ↔ ∀ g : G, g • x = x := Iff.rfl

/-- The norm of an element is fixed by `G`. -/
theorem normHom_mem_fixedSubgroup (x : M) : normHom G M x ∈ fixedSubgroup G M := by
  intro g
  show g • (∏ h : G, h • x) = ∏ h : G, h • x
  rw [show g • (∏ h : G, h • x) =
      (MulDistribMulAction.toMulAut G M g) (∏ h : G, h • x) from rfl, map_prod]
  exact Finset.prod_equiv (Equiv.mulLeft g) (fun i => by simp) (fun h _ => by
    show (MulDistribMulAction.toMulAut G M g) (h • x) = (g * h) • x
    rw [mul_smul]
    change g • (h • x) = g • (h • x)
    rfl)

/-- The range of the norm is contained in the fixed points. -/
theorem normHom_range_le_fixedSubgroup :
    (normHom G M).range ≤ fixedSubgroup G M :=
  fun _x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact normHom_mem_fixedSubgroup y

/-- **The degree-zero Tate cohomology** `Ĥ⁰(G, M) = M^G ⧸ N_G M` of a finite group action on a
commutative group, in multiplicative notation. -/
def H0 (G : Type*) [Group G] [Fintype G] (M : Type*) [CommGroup M]
    [MulDistribMulAction G M] : Type _ :=
  ↥(fixedSubgroup G M) ⧸ ((normHom G M).range.subgroupOf (fixedSubgroup G M))

end NK.GlobalCFTdeep
