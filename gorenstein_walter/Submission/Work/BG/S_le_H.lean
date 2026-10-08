import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.sq_eq_one_eq_of_isCyclic

/-!
# Area BG: `S ≤ H = C_G(t)` for the Bender–Glauberman data

Bender–Glauberman 1981 use without comment that the involution `t` of the cyclic subgroup
`S₀` of index two in the dihedral Sylow `2`-subgroup `S` is **central in** `S`; equivalently

  `S ≤ C_G(t) = H`.

This is the statement that `Work.GW2.BGData`'s `H = C_G(t)` (see `Work.GW2.BGData.H`) makes
available to the whole BG character computation (`H₁ = US₀ ≤ H`, `T = H₀ ∖ U ⊆ H`, …).

Nothing from Hypothesis 1.1 beyond the displayed field data is needed: `S₀ ⊴ S` because
`[S : S₀] = 2`, and a cyclic group contains at most one involution
(`Work.BG.sq_eq_one_eq_of_isCyclic`), so for `x ∈ S` either `x ∈ S₀`, and `S₀` is abelian,
or `x t x⁻¹` is an involution of `S₀`, hence `x t x⁻¹ = t`.  The same argument appears in
the Bender-setup API (`Work.CORE2A.bSetup_S_le_H`); it is reproduced here for
`Work.GW2.BGData` so that area BG does not depend on area CORE2A.
-/

set_option linter.style.haveILetI false

namespace Work.BG

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- The index-two subgroup `S₀` of `S` is normal in `S`. -/
theorem BGData_S0_subgroupOf_normal (D : Work.GW2.BGData G) :
    (D.S0.subgroupOf (D.S : Subgroup G)).Normal := by
  refine Subgroup.normal_of_index_eq_two ?_
  simpa [Subgroup.relIndex] using D.S0_index

/-- An element of the cyclic group `S₀` commutes with the involution `t ∈ S₀`. -/
theorem BGData_comm_of_mem_S0 (D : Work.GW2.BGData G) {x : G} (hx : x ∈ D.S0) :
    x * D.t = D.t * x := by
  haveI : IsCyclic ↥D.S0 := D.S0_cyclic
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥D.S0) ⟨D.t, D.t_mem⟩)

/-- A finite cyclic group has a unique element of order two. -/
theorem eq_of_orderOf_eq_two_of_isCyclic {C : Type} [Group C] [Finite C] [IsCyclic C]
    {a b : C} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  refine sq_eq_one_eq_of_isCyclic (z := a) (a := b) ?_ ?_ ?_ ?_
  · rintro rfl; rw [orderOf_one] at ha; exact absurd ha (by norm_num)
  · rintro rfl; rw [orderOf_one] at hb; exact absurd hb (by norm_num)
  · simpa [ha] using pow_orderOf_eq_one a
  · simpa [hb] using pow_orderOf_eq_one b

/-- **Bender–Glauberman 1981**: the involution `t` of the cyclic maximal subgroup `S₀` is
central in the Sylow `2`-subgroup `S`, i.e. `S ≤ C_G(t) = H`. -/
theorem S_le_H {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    (D.S : Subgroup G) ≤ D.H := by
  intro x hxS
  rw [show D.H = Subgroup.centralizer ({D.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  by_cases hx0 : x ∈ D.S0
  · exact (BGData_comm_of_mem_S0 D hx0).symm
  · -- `x t x⁻¹` is an involution of the cyclic group `S₀`, hence equal to `t`
    have hN := BGData_S0_subgroupOf_normal D
    have hconj : x * D.t * x⁻¹ ∈ D.S0 := by
      have hmem := hN.conj_mem (⟨D.t, D.S0_le D.t_mem⟩ : ↥(D.S : Subgroup G))
        (by rw [Subgroup.mem_subgroupOf]; exact D.t_mem) (⟨x, hxS⟩ : ↥(D.S : Subgroup G))
      simpa [Subgroup.mem_subgroupOf] using hmem
    have hord : orderOf (x * D.t * x⁻¹) = 2 := by
      have hsemi : SemiconjBy x D.t (x * D.t * x⁻¹) := by
        simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq x hsemi).symm.trans D.t_order
    haveI : IsCyclic ↥D.S0 := D.S0_cyclic
    have heq : (⟨x * D.t * x⁻¹, hconj⟩ : ↥D.S0) = ⟨D.t, D.t_mem⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic
        (a := (⟨x * D.t * x⁻¹, hconj⟩ : ↥D.S0)) (b := (⟨D.t, D.t_mem⟩ : ↥D.S0))
        (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact D.t_order)
    have hval : x * D.t * x⁻¹ = D.t := congrArg Subtype.val heq
    have h2 : (x * D.t * x⁻¹) * x = D.t * x := by rw [hval]
    have hx1 : x * D.t = D.t * x := by simpa [mul_assoc] using h2
    exact hx1.symm

end Work.BG
