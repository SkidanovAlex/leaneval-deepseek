/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The complexity of `-1` is `1`: the missing ingredient of the `⋄`-case of Proposition 5.1

The `⋄`-case of [JZLA20, Proposition 5.1] computes the coefficients of the inverse of the series
realising `x` from the coefficients of that series *and the sign `-1`*: the coefficient recursion
of `D_{N,P}((t;τ))` expresses the `n`-th coefficient of `f⁻¹` as a sum of products of coefficients
of `f` and coefficients of `-1`, so controlling the complexity of that coefficient requires
controlling the complexity of `-1`.

In the paper this is automatic: `Γ = E^×H` is the group of units of the crossed product, so
`-1 ∈ E^× ⊆ Γ`, hence `Tree_H(-1) = Tree_H(Φ(ofGroup u)) = 1` for the `u ∈ Γ` with
`Φ (ofGroup u) = -1`.  The formalisation records this as the field `Prop51Data.Phi_neg_one`.

Here we derive the two consequences used in the `⋄`-case: `treeH (-1) = 1` and
`d2log (treeH (-1)) = none`, the second giving the strict bound
`Olt (d2log (treeH (-1))) (some T)` for *every* tree `T`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.treeH_ofGroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.Prop51

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- **The `H`-complexity of `-1` is `1`**: `-1` is the image of a group element
(`Prop51Data.Phi_neg_one`) and the complexity of such an image is `1` (`treeH_ofGroup`). -/
theorem treeH_neg_one (d : Prop51Data Γ P DN) : d.treeH (d.coeffToP (-1)) = 1 := by
  obtain ⟨u, hu⟩ := d.Phi_neg_one
  have hcoe : d.coeffToP (-1) = d.Φ (RatU.ofGroup u) := by
    have h1 : d.coeffToP (-1) = -1 := by
      show (Subring.subtype DN) (-1 : ↥DN) = -1
      rw [map_neg, map_one]
    rw [h1, hu]
  rw [hcoe, treeH_ofGroup]

/-- The double logarithm of `treeH (-1) = 1` is `none`, i.e. `-∞`: the double logarithm of a tree
of width one is undefined. -/
theorem d2log_treeH_neg_one (d : Prop51Data Γ P DN) :
    Tree.d2log (d.treeH (d.coeffToP (-1))) = none := by
  rw [treeH_neg_one d]
  rw [show (1 : Tree) = Tree.exp (0 : Tree) from rfl]
  rw [Tree.d2log_eq_some (Tree.log_exp 0)]
  exact (Tree.log_spec 0).1 rfl

/-- **The sign bound of the `⋄`-case**: `d2log (treeH (-1)) < some T` for every tree `T`. -/
theorem olt_d2log_treeH_neg_one (d : Prop51Data Γ P DN) (T : Tree) :
    Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (-1)))) (some T) := by
  rw [d2log_treeH_neg_one d]
  exact ⟨trivial, fun h => h⟩

end Work.ORHughesFree.Prop51
