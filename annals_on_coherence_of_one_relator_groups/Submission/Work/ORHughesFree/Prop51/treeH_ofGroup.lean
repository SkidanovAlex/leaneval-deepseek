/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `H`-complexity of the image of a group element is `1`

[JZLA20, Lemma 4.3(ii)] says that an element `α` of `Rat(U)` has complexity `Tree(α) = 1` if and
only if it is the image `ofGroup u` of a group element `u : U` (`Rat.treeOfRat_eq_one_iff`).  The
converse inequality holds for the `H`-complexity `treeH` of a `Prop51Data`: since `treeH` is the
*minimum* of `Tree` over the fibre of `Φ` (`Prop51Data.treeH_spec`), `treeH (Φ α) ≤ Tree α`, and
hence `treeH (Φ (ofGroup v)) ≤ 1` for every `v : Γ`.

Here we upgrade this to the equality `treeH (Φ (ofGroup v)) = 1`.  The missing ingredient is that
`treeH (Φ (ofGroup v))` is non-zero: `Φ` carries the unit `ofGroup v` of `Rat(Γ)` to a unit of `P`
(a ring homomorphism maps units to units), and `P` is non-trivial because its subring `DN` is a
non-trivial ring (`Prop51Data.nontrivialDN`), so that unit is `≠ 0`.  Then `treeH a = 0` would
force `a = 0` (`Prop51Data.treeH_eq_zero_iff`), and finally `Tree.le 1 t` for `t ≠ 0`
(`Rat.treeOrderFacts`: `1` is the least non-zero tree) together with `Tree.le t 1` gives `t = 1`
by antisymmetry of the tree order.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.treeOrderFacts

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- A subring `DN` which is a division ring makes the ambient ring `P` non-trivial. -/
theorem nontrivial_of_isDivisionRing_subring (h : Work.ORHughesFree.IsDivisionRing ↥DN) :
    Nontrivial P := by
  haveI : Nontrivial ↥DN := h.1
  exact Function.Injective.nontrivial (f := fun a : ↥DN => (a : P)) Subtype.coe_injective

/-- The image `ofGroup v` of a group element in `Rat(Γ)` is a unit. -/
theorem isUnit_ratU_ofGroup (v : Γ) : IsUnit (Work.ORHughesFree.RatU.ofGroup v) :=
  ⟨Work.ORHughesFree.RatU.ofGroupHom.toHomUnits v, by simp⟩

/-- `Φ (ofGroup v)` is a unit of `P`, hence non-zero (as `P` is non-trivial whenever `DN` is a
division ring). -/
theorem Phi_ofGroup_ne_zero (d : Work.ORHughesFree.Prop51Data Γ P DN) (v : Γ) :
    d.Φ (Work.ORHughesFree.RatU.ofGroup v) ≠ 0 := by
  have hP : Nontrivial P := by
    obtain ⟨a, b, hab⟩ := d.nontrivialDN
    exact ⟨(a : P), (b : P), fun h => hab (Subtype.ext h)⟩
  exact (isUnit_ratU_ofGroup v |>.map d.Φ).ne_zero

theorem treeH_ofGroup {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN) (v : Γ) :
    d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup v)) = 1 := by
  -- `treeH (Φ (ofGroup v))` is non-zero, since `Φ (ofGroup v)` is a unit of the non-trivial
  -- ring `P`.
  have hne : d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup v)) ≠ 0 := fun h =>
    Phi_ofGroup_ne_zero d v ((d.treeH_eq_zero_iff (d.map_mem _)).mp h)
  -- `treeH` is the minimum of `Tree` over the fibre of `Φ`, and `Tree (ofGroup v) = 1`.
  have hle : Tree.le (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup v))) 1 := by
    simpa using d.treeH_le_treeOfRat (Work.ORHughesFree.RatU.ofGroup v)
  -- `1` is the least non-zero tree, and the tree order is antisymmetric.
  exact Tree.le_antisymm hle (Rat.treeOrderFacts.1 _ hne)

end Work.ORHughesFree.Prop51
