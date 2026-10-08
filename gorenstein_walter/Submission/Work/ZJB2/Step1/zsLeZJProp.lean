import Mathlib
import Submission.Work.ZJB.Step1.Defs

/-!
# ZJB2, step (I), leaf F0: `Z(P) ≤ Z(J(P))`

This file proves `Work.ZJB.ZSLeZJProp G`, i.e. `ZS P ≤ ZJ P` for every subgroup `P ≤ G`
(of a finite group `G`), where

* `ZS P = C_G(P) ⊓ P = Z(P)`,
* `ZJ P = J(P) ⊓ C_G(J(P)) = Z(J(P))`, with `J(P) = Work.GW2.thompsonJ P`.

The two halves are the classical facts

* `Z(P) ≤ J(P)`: `Z(P)` is abelian, hence lies in some maximum-order abelian subgroup
  `A ≤ P` (Gorenstein, *Finite Groups*, Lemma 2.1: `Z(P) ≤ A` for every `A ∈ A(P)`), and
  `A ≤ J(P)` because `J(P)` is the join of the members of `A(P)`;
* `Z(P) ≤ C_G(J(P))`: `Z(P) ≤ C_G(P)` and `J(P) ≤ P`.

Both are consumed from the odd-order library (`Subgroup.maxAbelianIn`,
`Subgroup.centralizer_inf_le_of_mem_maxAbelianIn`) through the GLUE bridge
(`Work.GW2.le_thompsonJ_of_mem_maxAbelianIn`, `Work.GW2.thompsonJ_le`).
-/

namespace Work.ZJB2.Step1

open Subgroup

/-- `Z(P) ≤ J(P)`: choose a maximum-order abelian subgroup `A ≤ P`; Gorenstein's Lemma 2.1
gives `Z(P) ≤ A`, and `A ≤ J(P)` since `J(P)` is the join of the `A ∈ A(P)`. -/
theorem zs_le_thompsonJ {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Work.ZJB.ZS P ≤ Work.GW2.thompsonJ P := by
  obtain ⟨A, hA⟩ := Subgroup.maxAbelianIn_nonempty (G := G) P
  rw [Work.ZJB.ZS]
  exact (Subgroup.centralizer_inf_le_of_mem_maxAbelianIn hA).trans
    (Work.GW2.le_thompsonJ_of_mem_maxAbelianIn hA)

/-- `Z(P) ≤ C_G(J(P))`: `Z(P) ≤ C_G(P)` and `J(P) ≤ P`. -/
theorem zs_le_centralizer_thompsonJ {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Work.ZJB.ZS P ≤ Subgroup.centralizer (Work.GW2.thompsonJ P : Set G) := by
  rw [Work.ZJB.ZS]
  refine (le_trans ?_ (Subgroup.centralizer_le (Work.GW2.thompsonJ_le P)))
  exact inf_le_left

/-- **F0.** `Z(P) ≤ Z(J(P))`. -/
theorem zsLeZJProp {G : Type*} [Group G] [Finite G] : Work.ZJB.ZSLeZJProp G := by
  intro P
  show Work.ZJB.ZS P ≤
    Work.GW2.thompsonJ P ⊓ Subgroup.centralizer (Work.GW2.thompsonJ P : Set G)
  exact le_inf (zs_le_thompsonJ P) (zs_le_centralizer_thompsonJ P)

end Work.ZJB2.Step1
