/-
# Components of a finite group and the join `E(X)`

This file starts the layer of Bender's components theory that the workspace does not have yet:
a **component** of a group `X` is a subnormal quasisimple subgroup of `X` (Bender's `E(X)`
is the join of the components, i.e. the last term of the derived series of the generalized
Fitting subgroup `F*(X) = F(X)·E(X)`).

The workspace's own `Work.GW2.layer X` is the join of the **normal** quasisimple subgroups;
it is contained in `E(X)` (`layer_le_Ejoin`), and the two notions coincide precisely when every
component of `X` is normal in `X`.  This gap is exactly what makes the degenerate case of
Bender 1970, 1.6 (the case `F*(A) = ⊥` for the workspace's `F*`) non-vacuous.

## Contents

* `IsComponent` : subnormal + quasisimple;
* `Ejoin X` : the join of the components;
* `IsSubnormal.of_normal`, `isComponent_of_normal_isQuasisimple` : normality implies
  subnormality, so normal quasisimple subgroups are components;
* `le_Ejoin`, `layer_le_Ejoin` : monotonicity and `layer X ≤ E(X)`.

The two deep inputs of the theory, to be proved separately, are

* `commutator_eq_bot_of_isComponent_of_isComponent` : distinct components commute;
* `centralizer_le_fitting_sup_Ejoin` : Bender's theorem
  `C_X(F(X)·E(X)) ≤ F(X)·E(X)` (equivalently, `F(X)·E(X)` is the largest normal subgroup `N`
  with `C_X(N) ≤ N`).

From these, `E(X) ≠ 1` for `X ≠ 1` with `F(X) = 1`, and then — because a single component is
normal in `X` — a group `X ≠ 1` with `F(X) = 1` and `layer X = ⊥` has **at least two**
components.  This is the structural statement that the degenerate case of Bender 1.6 turns on.
-/
import Mathlib
import Submission.Work.BMAX.Defs

namespace Work.BMAX

open Subgroup

universe u

/-- A **component** of a group `X` is a subnormal quasisimple subgroup of `X`. -/
def IsComponent {X : Type*} [Group X] (E : Subgroup X) : Prop :=
  E.IsSubnormal ∧ Work.GW2.IsQuasisimple E

/-- `E(X)`: the join of the components of `X`. -/
def Ejoin (X : Type*) [Group X] : Subgroup X :=
  sSup {E : Subgroup X | IsComponent E}

theorem isComponent_iff {X : Type*} [Group X] {E : Subgroup X} :
    IsComponent E ↔ E.IsSubnormal ∧ Work.GW2.IsQuasisimple E := Iff.rfl

/-- A normal subgroup is subnormal. -/
theorem IsSubnormal.of_normal {X : Type*} [Group X] {E : Subgroup X} (h : E.Normal) :
    E.IsSubnormal := by
  have hN : (E.subgroupOf (⊤ : Subgroup X)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (le_top : E ≤ (⊤ : Subgroup X))]
    intro a b ha _
    exact h.conj_mem a ha b
  exact Subgroup.IsSubnormal.step E (⊤ : Subgroup X) le_top
    (Subgroup.IsSubnormal.top (G := X)) hN

/-- A normal quasisimple subgroup is a component. -/
theorem isComponent_of_normal_isQuasisimple {X : Type*} [Group X] {E : Subgroup X}
    (h : E.Normal) (hq : Work.GW2.IsQuasisimple E) : IsComponent E :=
  ⟨IsSubnormal.of_normal h, hq⟩

/-- A component is contained in `E(X)`. -/
theorem le_Ejoin {X : Type*} [Group X] {E : Subgroup X} (h : IsComponent E) : E ≤ Ejoin X :=
  le_sSup h

/-- The workspace's `layer X` (join of the **normal** quasisimple subgroups) is contained in
`E(X)` (join of the components). -/
theorem layer_le_Ejoin (X : Type*) [Group X] : Work.GW2.layer X ≤ Ejoin X := by
  refine sSup_le ?_
  rintro E ⟨hEn, hEq⟩
  exact le_Ejoin (isComponent_of_normal_isQuasisimple hEn hEq)

end Work.BMAX
