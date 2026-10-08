/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.OddOrder.GroupTheory.ThompsonSubgroupAbelian

/-!
# CORE2A: `Z(J(P))` is conjugation covariant

`Work.CORE2A.ZJ_conj` : for every subgroup `P ≤ G` and every `g : G`,

  `Z(J(P^g)) = Z(J(P))^g`,   where `P^g = Work.GW2.conjSub g P = g P g⁻¹`.

This is the conjugation case of the general fact that `Z(J(-))` is carried to `Z(J(-))` by
every isomorphism of the ambient group; Bender uses it to move statements about `Z(J(P))`
between conjugate `2`-subgroups.

`Z(J(P)) = J(P) ⊓ C_G(J(P))` (`Work.GW2.ZJ`), so the statement is assembled from three
elementary facts about `Subgroup.map` along the multiplication map
`φ_g = (MulAut.conj g).toMonoidHom : G →* G` (which is bijective):

* `thompsonJ` is covariant: `J(P^g) = J(P)^g`;
* the centralizer of a subgroup is covariant: `C_G(H^g) = C_G(H)^g`;
* for an injective `f`, `Subgroup.map f` preserves infima: `(H ⊓ K)^f = H^f ⊓ K^f`.

The first of these is proved by transporting the odd-order library's
`Subgroup.thompsonJAbelian_map_of_injective` across the bridge
`Work.GW2.thompsonJ = Subgroup.thompsonJAbelian` (both are the join of the maximal-order
abelian subgroups, so the bridge is definitional after `sSup = iSup`).  The other two are
proved here, directly from `Subgroup.mem_centralizer_iff` and `Subgroup.mem_map`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

section Helpers

variable {G : Type*} [Group G]

/-- **Bridge.** Our `Work.GW2.thompsonJ` is the odd-order library's abelian Thompson
subgroup `J_a`: both are the join of the maximal-order abelian subgroups of `P`. -/
theorem ZJ_conj_thompsonJ_eq_thompsonJAbelian (P : Subgroup G) :
    Work.GW2.thompsonJ P = Subgroup.thompsonJAbelian P := by
  rw [Work.GW2.thompsonJ, Subgroup.thompsonJAbelian, Subgroup.maxAbelianIn, sSup_eq_iSup]

/-- `J(-)` is covariant under injective homomorphisms: `J(P)^f = J(P^f)`. -/
theorem ZJ_conj_thompsonJ_map_of_injective {H N : Type*} [Group H] [Group N]
    (f : H →* N) (hf : Function.Injective f) (P : Subgroup H) :
    (Work.GW2.thompsonJ P).map f = Work.GW2.thompsonJ (P.map f) := by
  rw [ZJ_conj_thompsonJ_eq_thompsonJAbelian, ZJ_conj_thompsonJ_eq_thompsonJAbelian]
  exact (Subgroup.thompsonJAbelian_map_of_injective hf P).symm

/-- **Conjugation covariance of the centralizer.**  For a bijective `f : H →* N` and a
subgroup `K ≤ H` one has `C_N(K^f) = C_H(K)^f`.

Injectivity (needed to move commutativity *back* along `f`) and surjectivity (needed to write
every `y ∈ C_N(K^f)` as `f x`) are both essential here: `map_centralizer_le_centralizer_image`
is the general inclusion, valid for *every* homomorphism with no surjectivity hypothesis. -/
theorem ZJ_conj_centralizer_map_of_bijective {H N : Type*} [Group H] [Group N]
    (f : H →* N) (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    (K : Subgroup H) :
    Subgroup.centralizer ((K.map f : Subgroup N) : Set N)
      = (Subgroup.centralizer (K : Set H)).map f := by
  refine le_antisymm ?_ ?_
  · -- `C(K^f) ≤ C(K)^f`: write `y = f x` using surjectivity of `f`.
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro k hk
    exact hinj (by
      rw [map_mul, map_mul]
      exact hy (f k) (by rw [Subgroup.coe_map]; exact ⟨k, hk, rfl⟩))
  · -- `C(K)^f ≤ C(K^f)`: the general inclusion `map_centralizer_le_centralizer_image`.
    rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image (K : Set H) f

end Helpers

/-- **`Z(J(P))` is conjugation covariant**: `Z(J(P^g)) = Z(J(P))^g`. -/
theorem ZJ_conj {G : Type} [Group G] (P : Subgroup G) (g : G) :
    Work.GW2.ZJ (Work.GW2.conjSub g P) = Work.GW2.conjSub g (Work.GW2.ZJ P) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  -- unfold the two conjugation maps `conjSub g`
  show Work.GW2.ZJ (P.map (MulAut.conj g).toMonoidHom)
      = (Work.GW2.ZJ P).map (MulAut.conj g).toMonoidHom
  -- unfold `ZJ _ = J(_) ⊓ C(J(_))`
  rw [Work.GW2.ZJ, Work.GW2.ZJ]
  -- conjugation covariance of `J`
  rw [← ZJ_conj_thompsonJ_map_of_injective (MulAut.conj g).toMonoidHom hinj P]
  -- conjugation covariance of the centralizer
  rw [ZJ_conj_centralizer_map_of_bijective (MulAut.conj g).toMonoidHom hinj hsurj
    (Work.GW2.thompsonJ P)]
  -- `Subgroup.map` of an injective homomorphism preserves the infimum `J(P) ⊓ C(J(P))`
  rw [← Subgroup.map_inf (Work.GW2.thompsonJ P)
    (Subgroup.centralizer ((Work.GW2.thompsonJ P : Subgroup G) : Set G))
    (MulAut.conj g).toMonoidHom hinj]

end Work.CORE2A
