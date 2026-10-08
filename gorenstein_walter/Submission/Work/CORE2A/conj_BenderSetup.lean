/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# CORE2A: conjugation of Bender's notation `(S, S₀, t, Ĥ)`

The structural facts about a `BenderSetup G` (`Work.GW2.BenderSetup`) are all of the form "`S` is
a Sylow 2-subgroup, `S₀ ≤ S` is cyclic of index two, `t` is the involution of `S₀`, and `Ĥ` is a
coatom containing `C_G(t)`".  Conjugation by `g ∈ G` is an automorphism of the lattice of
subgroups, so it carries every one of these facts to the corresponding fact about the conjugate
subgroups: this file records the four one-step facts and then the resulting statement
`conj_BenderSetup`, that the conjugate data is again a Bender setup.

The one-step facts (all proved from `Work.CORE2A.conjSub`, the conjugation helper of
`Submission.Work.CORE2A.Basic`), collected in the sub-namespace `Work.CORE2A.BenderConj` so that
they cannot collide with the conjugacy helpers of other modules:

* `BenderConj.centralizer_conj` — `C_G(t^g) = C_G(t)^g`;
* `BenderConj.isCoatom_conjSub` — coatoms are carried to coatoms;
* `BenderConj.isCyclic_conjSub` — cyclic (sub)groups are carried to cyclic ones;
* `BenderConj.relIndex_conjSub` — the relative index is invariant;
* `BenderConj.orderOf_mul_conj` — `orderOf (g t g⁻¹) = orderOf t`.

The target `conj_BenderSetup` is used to move a minimal counterexample configuration `B` to a
conjugate one (e.g. Bender's choice of a Sylow 2-subgroup compatible with a fixed maximal
subgroup `M`, `Submission/Work/CORE4/Case2Setup9.lean`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

namespace BenderConj

variable {G : Type*} [Group G]

/-- Conjugation carries the centralizer of an element to the centralizer of its conjugate:
`C_G(t^g) = C_G(t)^g`. -/
theorem centralizer_conj (g t : G) :
    centralizer ({g * t * g⁻¹} : Set G) = conjSub g (centralizer ({t} : Set G)) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h]
      _ = t * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * t * g⁻¹) = g * (g⁻¹ * x * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = (g * t * g⁻¹) * x := by group

/-- Conjugation carries coatoms to coatoms: `Ĥ` maximal and proper forces `Ĥ^g` maximal and
proper.  (Both directions of the argument use that `conjSub g` is an order isomorphism of the
subgroup lattice, whose inverse is `conjSub g⁻¹` and which fixes `⊤`.) -/
theorem isCoatom_conjSub {H : Subgroup G} (h : IsCoatom H) (g : G) :
    IsCoatom (conjSub g H) := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : conjSub g⁻¹ (conjSub g H) = conjSub g⁻¹ (⊤ : Subgroup G) := by rw [htop]
    rw [conjSub_inv_conjSub, conjSub_top] at h1
    exact h.1 h1
  · intro b hb
    have hle : H ≤ conjSub g⁻¹ b := by
      have := conjSub_mono hb.le g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hne : H ≠ conjSub g⁻¹ b := by
      intro heq
      have hEq : conjSub g H = b := by rw [heq, conjSub_conjSub_inv]
      exact absurd hEq hb.ne
    have htop : conjSub g⁻¹ b = ⊤ := h.2 _ (lt_of_le_of_ne hle hne)
    calc b = conjSub g (conjSub g⁻¹ b) := (conjSub_conjSub_inv g b).symm
      _ = conjSub g (⊤ : Subgroup G) := by rw [htop]
      _ = ⊤ := conjSub_top g

/-- Conjugation carries cyclic subgroups to cyclic subgroups (conjugation is an isomorphism onto
the conjugate subgroup). -/
theorem isCyclic_conjSub (g : G) {K : Subgroup G} (hK : IsCyclic K) :
    IsCyclic (conjSub g K) := by
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom hf)
    (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom hf).surjective

/-- The relative index is invariant under conjugation. -/
theorem relIndex_conjSub (g : G) (K L : Subgroup G) :
    (conjSub g K).relIndex (conjSub g L) = K.relIndex L := by
  rw [conjSub_eq_map g K, conjSub_eq_map g L,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

/-- Conjugates have the same order. -/
theorem orderOf_mul_conj (g t : G) : orderOf (g * t * g⁻¹) = orderOf t := by
  rw [show g * t * g⁻¹ = (MulAut.conj g) t by simp [MulAut.conj_apply]]
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow]
  exact (MulAut.conj g).map_eq_one_iff

end BenderConj

open BenderConj

/-- **Conjugation of a Bender setup.**  If `B` is Bender's minimal-counterexample configuration
with notation `S, S₀, t, Ĥ`, then for every `g ∈ G` the conjugate data
`S^g, S₀^g, t^g, Ĥ^g` is again a `BenderSetup` (with the same structural properties: `S^g` a
Sylow 2-subgroup, `S₀^g ≤ S^g` cyclic of index two, `t^g` the involution of `S₀^g`, and `Ĥ^g` a
coatom containing `C_G(t^g) = C_G(t)^g`). -/
theorem conj_BenderSetup {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (g : G) :
    ∃ B' : Work.GW2.BenderSetup G,
      (B'.S : Subgroup G) = Work.GW2.conjSub g (B.S : Subgroup G) ∧
      B'.S0 = Work.GW2.conjSub g B.S0 ∧
      B'.t = g * B.t * g⁻¹ ∧
      B'.Hhat = Work.GW2.conjSub g B.Hhat := by
  classical
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom :=
    fun x => ⟨g⁻¹ * x * g,
      by show (MulAut.conj g) (g⁻¹ * x * g) = x; rw [MulAut.conj_apply]; group⟩
  have hScoe :
      ((B.S.mapSurjective (f := (MulAut.conj g).toMonoidHom) hsurj : Sylow 2 G) : Subgroup G)
        = Work.GW2.conjSub g (B.S : Subgroup G) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  refine ⟨{ S := B.S.mapSurjective (f := (MulAut.conj g).toMonoidHom) hsurj
            S0 := Work.GW2.conjSub g B.S0
            t := g * B.t * g⁻¹
            Hhat := Work.GW2.conjSub g B.Hhat
            S0_le := Work.CORE2A.conjSub_mono B.S0_le g
            S0_cyclic := isCyclic_conjSub g B.S0_cyclic
            S0_index := by rw [hScoe, relIndex_conjSub]; exact B.S0_index
            t_mem := by
              rw [Work.CORE2A.mem_conjSub_iff]
              have h : g⁻¹ * (g * B.t * g⁻¹) * g = B.t := by group
              rw [h]
              exact B.t_mem
            t_order := by rw [orderOf_mul_conj, B.t_order]
            Hhat_coatom := isCoatom_conjSub B.Hhat_coatom g
            H_le_Hhat := by
              calc Subgroup.centralizer ({g * B.t * g⁻¹} : Set G)
                  = Work.GW2.conjSub g (Subgroup.centralizer ({B.t} : Set G)) :=
                    centralizer_conj g B.t
                _ ≤ Work.GW2.conjSub g B.Hhat := Work.CORE2A.conjSub_mono B.H_le_Hhat g },
    ?_, rfl, rfl, rfl⟩
  exact hScoe

end Work.CORE2A
