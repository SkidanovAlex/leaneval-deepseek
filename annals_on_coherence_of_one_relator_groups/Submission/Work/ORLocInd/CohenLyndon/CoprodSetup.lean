/-
# Notation for the free-product transfer of the Cohen--Lyndon property

This file fixes the notation used by `Work.ORLocInd.CohenLyndon.cohenLyndonNC_coprod`: for groups
`A`, `B` and an element `r ∈ A` we write

* `NA r`  : the normal closure `⟪r⟫_A ⊆ A`;
* `QA r`  : the subgroup `⟪r⟫_A ⊔ C_A(r) ⊆ A` whose cosets index the classical Cohen--Lyndon
  transversal;
* `rS r`  : the normal closure `⟪inl r⟫_{A ∗ B}` of the image of `r` in the free product;
* `QG r`  : the subgroup `⟪inl r⟫ {A∗B} ⊔ A` of `A ∗ B`; its right cosets are the
  `(⟪inl r⟫, A)`-double cosets, i.e. the orbits of the action of `⟪inl r⟫` on the `A`-cosets of
  the Bass--Serre tree of `A ∗ B`.
-/
import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.ORBassSerre.CoprodTree.Tree
import Submission.Work.OROneRel.coprod_normalClosure

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

open Monoid

variable {A B : Type u} [Group A] [Group B]

/-- The normal closure `⟪r⟫_A` of `r` in `A`. -/
abbrev NA (r : A) : Subgroup A := Subgroup.normalClosure ({r} : Set A)

/-- The subgroup `⟪r⟫_A ⊔ C_A(r)` of `A`, whose right cosets index the Cohen--Lyndon
transversal (`Work.CohenLyndon.CohenLyndonNC`). -/
abbrev QA (r : A) : Subgroup A :=
  Subgroup.normalClosure ({r} : Set A) ⊔ Subgroup.centralizer ({r} : Set A)

/-- The normal closure `⟪inl r⟫_{A ∗ B}` of the image of `r` in the free product. -/
abbrev rS (r : A) : Subgroup (Monoid.Coprod A B) :=
  Subgroup.normalClosure ({Monoid.Coprod.inl r} : Set (Monoid.Coprod A B))

/-- The subgroup `⟪inl r⟫_{A ∗ B} ⊔ A` of the free product.  Its right cosets are the
`(⟪inl r⟫, A)`-double cosets. -/
abbrev QG (r : A) : Subgroup (Monoid.Coprod A B) :=
  rS r ⊔ Work.ORBassSerre.CoprodTree.SubA A B

/-- The image of `A` in `A ∗ B`. -/
abbrev SubA' (A B : Type u) [Group A] [Group B] : Subgroup (Monoid.Coprod A B) :=
  Work.ORBassSerre.CoprodTree.SubA A B

/-- The image of `B` in `A ∗ B`. -/
abbrev SubB' (A B : Type u) [Group A] [Group B] : Subgroup (Monoid.Coprod A B) :=
  Work.ORBassSerre.CoprodTree.SubB A B

end Work.ORLocInd.CohenLyndon
