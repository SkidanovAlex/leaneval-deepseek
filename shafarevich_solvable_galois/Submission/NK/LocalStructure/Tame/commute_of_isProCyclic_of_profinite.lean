/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A profinite group with cyclic finite quotients is abelian

This file proves `NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite`: a compact totally
disconnected topological group `H` all of whose finite quotients are cyclic
(`NK.LocalTame.IsProCyclic H`) is abelian.

## The mathematics

Let `N ⊴ H` have finite index.  By hypothesis the quotient `H ⧸ N` is cyclic, hence commutative,
so the commutator `x * y * x⁻¹ * y⁻¹` of two elements of `H` is trivial in `H ⧸ N`, i.e. it lies
in `N`.  As `x`, `y` are arbitrary, the commutator lies in *every* finite-index normal subgroup,
and a fortiori in every *open* normal subgroup.

The open normal subgroups of a profinite group have trivial intersection: if `z ≠ 1`, then `{z}` is
closed, so `{z}ᶜ` is an open neighbourhood of `1`, and in a compact totally disconnected group an
open neighbourhood of `1` contains an open normal subgroup
(`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`, whose hypothesis
`TotallyDisconnectedSpace` supplies the Hausdorff separation needed to separate the points `1`
and `z`).  That subgroup does not contain `z`, so `z` is not in the intersection.

Consequently the commutator of any two elements of `H` is `1`.

This is exactly the group-theoretic step by which the pro-cyclicity of the tame inertia `I_κ/V_κ`
yields its commutativity, hence `[I_κ, I_κ] ≤ V_κ` — the field
`NK.LocalStructure.TameCore.tameInertia_commutator_mem` of the local structure theory.  Indeed
`V_κ` is open normal in `G_κ`, so `I_κ/V_κ` is again a compact totally disconnected topological
group, and by `TameCore.isTameInertia` it is pro-cyclic in the sense of
`NK.LocalTame.IsProCyclic`; the lemma below then makes it abelian.  (What remains to be supplied
at the point of use is the transportation of the topological group structure to the quotient
`I_κ/V_κ`.)

## Main result

* `NK.LocalStructure.Tame.commute_of_isProCyclic_of_profinite`
-/
import Mathlib
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tame

/-! ## Two elementary group-theoretic lemmas -/

/-- **A commutator lies in every normal subgroup with cyclic quotient.**

If `H ⧸ N` is cyclic then it is commutative, so the image of `x * y * x⁻¹ * y⁻¹` in `H ⧸ N` is
trivial, i.e. the commutator lies in `N`. -/
theorem commutator_mem_of_isCyclic_quotient {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (h : IsCyclic (G ⧸ N)) (x y : G) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  have hc : ∀ a b : G ⧸ N, a * b = b * a :=
    fun a b => (IsMulCommutative.is_comm (M := G ⧸ N)).comm a b
  rw [← QuotientGroup.eq_one_iff (N := N) (x * y * x⁻¹ * y⁻¹)]
  have key : QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      hc (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)]
    group
  rwa [QuotientGroup.mk'_apply] at key

/-- **An element lying in every open normal subgroup of a profinite group is trivial.**

Given `z ≠ 1`, the complement of the closed point `{z}` is an open neighbourhood of `1`, hence
contains an open normal subgroup `N` (`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`,
which uses that a compact totally disconnected group is Hausdorff), and `z ∉ N`. -/
theorem eq_one_of_mem_openNormalSubgroups {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] {z : H}
    (hz : ∀ N : OpenNormalSubgroup H, z ∈ N) : z = 1 := by
  by_contra hz1
  have hU : IsOpen ({z}ᶜ : Set H) := isClosed_singleton.isOpen_compl
  have h1U : (1 : H) ∈ ({z}ᶜ : Set H) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hz1 h.symm
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U
  exact (hN (hz N)) (by simp)

/-! ## The main result -/

theorem commute_of_isProCyclic_of_profinite {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (h : NK.LocalTame.IsProCyclic H) : ∀ x y : H, x * y = y * x := by
  intro x y
  -- the commutator lies in every open normal subgroup
  have hmem : ∀ N : OpenNormalSubgroup H, x * y * x⁻¹ * y⁻¹ ∈ N := by
    intro N
    have hfin : Finite (H ⧸ N.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen N.toSubgroup N.toOpenSubgroup.isOpen'
    have hfi : N.toSubgroup.FiniteIndex := N.toSubgroup.finiteIndex_of_finite_quotient
    exact commutator_mem_of_isCyclic_quotient (h N.toSubgroup hfi) x y
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := eq_one_of_mem_openNormalSubgroups hmem
  have h2 : x * y * x⁻¹ * y⁻¹ = (x * y) * (y * x)⁻¹ := by group
  rw [h2] at h1
  exact mul_inv_eq_one.mp h1

end NK.LocalStructure.Tame
