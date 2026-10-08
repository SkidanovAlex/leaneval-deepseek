import Mathlib
import Submission.Work.CORE2B.Defs

/-!
# `Work.CORE2B.t_central_in_S` — Bender p. 219: `S ≤ C_G(t)`

In Bender's notation (`Submission/Work/CORE2B/Defs.lean`) `S` is a Sylow 2-subgroup of `G`,
`S₀ ≤ S` is a **cyclic** subgroup of index two, and `t ∈ S₀` is an involution.

**Bender p. 219**: the involution `t` of the cyclic `S₀` is central in `S`, i.e. `S ≤ C_G(t) = H`.
The argument is purely elementary:

* `S₀` has index two in `S`, so `S₀ ◁ S` (`Subgroup.normal_of_index_eq_two`);
* hence for `x ∈ S` the conjugate `x t x⁻¹` again lies in `S₀` and has order two;
* a finite cyclic group has a *unique* element of order two (an element of order dividing two is
  a `2`-torsion element and `#{a | orderOf a = 2} = φ(2) = 1`,
  `IsCyclic.card_orderOf_eq_totient`), so `x t x⁻¹ = t`.

No hypothesis beyond the field of `BenderSetup` is used (in particular neither `BenderCtx` nor the
Feit–Thompson theorem).
-/

namespace Work.CORE2B

open Subgroup

theorem t_central_in_S {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := by
  -- A finite cyclic group has at most one element of order two.
  have uniq : ∀ {H : Type} [Group H] [Finite H] [IsCyclic H] {a b : H},
      orderOf a = 2 → orderOf b = 2 → a = b := by
    intro H _ _ _ a b ha hb
    classical
    have hfin : Fintype H := Fintype.ofFinite H
    have hd : 2 ∣ Fintype.card H := by
      rw [← Nat.card_eq_fintype_card, ← ha]
      exact orderOf_dvd_natCard a
    have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
      rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
    exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hxS
  by_cases hx0 : x ∈ B.S0
  · -- `x ∈ S₀`, and `S₀` is cyclic, hence commutative.
    have hcyc : IsCyclic ↥B.S0 := B.S0_cyclic
    exact (congrArg Subtype.val (mul_comm' (⟨B.t, B.t_mem⟩ : ↥B.S0) ⟨x, hx0⟩)).symm
  · -- `S₀ ◁ S`, so `x * t * x⁻¹ ∈ S₀`; it has order two, hence equals `t`.
    have hN : (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
      refine Subgroup.normal_of_index_eq_two ?_
      simpa [Subgroup.relIndex] using B.S0_index
    have hconj : x * B.t * x⁻¹ ∈ B.S0 := by
      have hmem : (⟨x, hxS⟩ : ↥(B.S : Subgroup G)) *
          (⟨B.t, B.S0_le B.t_mem⟩ : ↥(B.S : Subgroup G)) *
          ((⟨x, hxS⟩ : ↥(B.S : Subgroup G)))⁻¹ ∈ B.S0.subgroupOf (B.S : Subgroup G) :=
        hN.conj_mem _ (by rw [Subgroup.mem_subgroupOf]; exact B.t_mem) _
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem
    have hord : orderOf (x * B.t * x⁻¹) = 2 := by
      have hsemi : SemiconjBy x B.t (x * B.t * x⁻¹) := by
        show x * B.t = (x * B.t * x⁻¹) * x
        group
      exact (SemiconjBy.orderOf_eq x hsemi).symm.trans B.t_order
    have hcyc : IsCyclic ↥B.S0 := B.S0_cyclic
    have heq : (⟨x * B.t * x⁻¹, hconj⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ :=
      uniq (by rw [Subgroup.orderOf_mk]; exact hord)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    have hval : x * B.t * x⁻¹ = B.t := congrArg Subtype.val heq
    calc x * B.t = (x * B.t * x⁻¹) * x := by group
      _ = B.t * x := by rw [hval]

end Work.CORE2B
