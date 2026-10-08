/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Defs

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: the Thompson subgroup `J(P)`, `Z(J(P))`, and the library's `J_a(P)`

`Work.GW2.thompsonJ P` is the join of the abelian subgroups of `P` of maximal order, and
`Work.GW2.ZJ P = J(P) ∩ C_G(J(P)) = Z(J(P))`.

The odd-order library works with the *same* subgroup under the name
`Subgroup.thompsonJAbelian` (Gorenstein Ch. 8 §2, `J_a(P) = ⟨A(P)⟩`), and **all** of its
`Z(J)`-theorem machinery (`Subgroup.zCenter_thompsonJAbelian_normal`, Glauberman replacement,
…) is stated with that name.  This file is the bridge:

* `thompsonJ_eq_thompsonJAbelian` — the two are literally the same subgroup;
* `ZJ_eq_thompsonJAbelian` — the FT-normal form of `Z(J(P))`.

plus the elementary API of `J(P)` and `Z(J(P))` that the `ZJ`-area (`ZJB`) and the `CORE`
areas consume.
-/

namespace Work.GW2

variable {G : Type*} [Group G]

/-- `J(P)` is the supremum of the abelian subgroups of `P` of maximal order, i.e. exactly
the *set* used in `Subgroup.maxAbelianIn P`. -/
theorem thompsonJ_eq_sSup (P : Subgroup G) :
    thompsonJ P = sSup (Subgroup.maxAbelianIn P) := rfl

/-- **Bridge.** Our `J(P)` is the odd-order library's abelian Thompson subgroup `J_a(P)`.
(As `J_a(P) = ⨆_{A ∈ A(P)} A` and `A(P)` is our index set, this is `sSup` = `iSup`.) -/
theorem thompsonJ_eq_thompsonJAbelian (P : Subgroup G) :
    thompsonJ P = Subgroup.thompsonJAbelian P := by
  rw [thompsonJ, Subgroup.thompsonJAbelian, Subgroup.maxAbelianIn, sSup_eq_iSup]

/-- `Z(J(P)) = J(P) ∩ C_G(J(P))`, in the shape in which the odd-order library states its
`Z(J)`-theorems (there `Z` is `C(J) ⊓ J`). -/
theorem ZJ_eq_thompsonJAbelian (P : Subgroup G) :
    ZJ P = Subgroup.centralizer (Subgroup.thompsonJAbelian P : Set G)
      ⊓ Subgroup.thompsonJAbelian P := by
  rw [ZJ, thompsonJ_eq_thompsonJAbelian, inf_comm]

theorem thompsonJ_le (P : Subgroup G) : thompsonJ P ≤ P := by
  rw [thompsonJ]
  exact sSup_le fun A hA => hA.1

/-- Each maximal-order abelian subgroup of `P` lies in `J(P)`. -/
theorem le_thompsonJ_of_mem_maxAbelianIn {P A : Subgroup G}
    (hA : A ∈ Subgroup.maxAbelianIn P) : A ≤ thompsonJ P := by
  rw [thompsonJ]
  exact le_sSup hA

theorem ZJ_le_thompsonJ (P : Subgroup G) : ZJ P ≤ thompsonJ P := inf_le_left

theorem ZJ_le_centralizer (P : Subgroup G) :
    ZJ P ≤ Subgroup.centralizer (thompsonJ P : Set G) := inf_le_right

theorem ZJ_le (P : Subgroup G) : ZJ P ≤ P := (ZJ_le_thompsonJ P).trans (thompsonJ_le P)

/-- `Z(J(P))` is abelian. -/
theorem ZJ_isMulCommutative (P : Subgroup G) : IsMulCommutative (ZJ P) := by
  rw [ZJ]
  refine IsMulCommutative.of_comm ?_
  intro x y
  refine Subtype.ext ?_
  have hx : (x : G) ∈ Subgroup.centralizer ((thompsonJ P : Subgroup G) : Set G) := x.2.2
  have hy : (y : G) ∈ thompsonJ P := y.2.1
  exact (Subgroup.mem_centralizer_iff.mp hx (y : G) hy).symm

/-- Conjugation covariance of `J(P)`. -/
theorem thompsonJ_map_conj (P : Subgroup G) (g : G) :
    thompsonJ (P.map (MulAut.conj g).toMonoidHom)
      = (thompsonJ P).map (MulAut.conj g).toMonoidHom := by
  simp only [thompsonJ_eq_thompsonJAbelian]
  exact Subgroup.thompsonJAbelian_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective P

/-- `J(P)` is fixed by elements of `N_G(P)` (Gorenstein Lemma 2.2(c)). -/
theorem thompsonJ_map_conj_eq_of_mem_normalizer {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (thompsonJ P).map (MulAut.conj g).toMonoidHom = thompsonJ P := by
  rw [thompsonJ_eq_thompsonJAbelian]
  exact Subgroup.thompsonJAbelian_map_conj_eq_of_mem_normalizer hg

end Work.GW2
