/-
# The FKS/Kurosh structure of the kernel of `⟨X | u ^ l⟩ → ⟨X | u⟩`

`Work.ORLocInd.FKSStruc` isolates the remaining input of Howie's Corollary 3.2
(`Brodskii.torsionFree_subgroup_locallyIndicable`) as `FKSKernelCondition P`: every torsion-free
subgroup of the kernel of the canonical map `⟨X | u ^ l⟩ →* ⟨X | u⟩` is locally indicable.

The literature theorem that supplies it (Fischer--Karrass--Solitar 1972, used by Howie 2000 as
reference [4]; see also the Kurosh subgroup theorem) is:

> for `G = ⟨X | u ^ l⟩` with `u` not a proper power, the kernel `N = ⟪u⟫_G` of `π : G →* Q` with
> `Q = ⟨X | u⟩` is the free product of the conjugates of `⟨u⟩` in `G`; since `u` has order exactly
> `l` in `G` (Karrass--Magnus--Solitar), the free factors are cyclic of order `l`, one for each
> element of `Q`:
>
> `N ≅ ∗_{q ∈ Q} ℤ/l`.

This module records that theorem in two forms.

* `FKSKernelStructure P`, the *algebraic* form: `ker π ≃* Monoid.CoprodI (fun _ : Q => ℤ/l)`.
* `FKSKernelTreeData P`, the *geometric* form: `ker π` acts on a non-empty tree without self-inverse
  arrows and without inversions, with finite vertex stabilisers (the conjugates of `⟨u⟩ ≅ ℤ/l`) and
  trivial edge stabilisers.  This is the Bass--Serre tree of the free-product decomposition.

`fksKernelCondition_of_kernelTree` below turns the geometric form into `FKSKernelCondition` using
`FKSTree.fksKernelCondition_of_tree` only (no further input), so `fksStructure_of_kernelTree` is
complete.  The algebraic form implies the geometric one via
`Work.ORLocInd.CoprodTree.isFreeGroup_of_isTorsionFree_subgroup` (a torsion-free subgroup of a free
product of finite groups is free -- the Kurosh subgroup theorem applied to the Bass--Serre tree of
the free product); that implication is recorded in
`Submission.Work.ORLocInd.FKSKernelCondition`.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORLocInd.FKSTree
import Submission.Work.OROneRel.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

open Quiver

variable {G : Type u} [Group G]

/-! ## The two forms of the structure theorem -/

/-- **The FKS structure theorem for the kernel, algebraic form** (Fischer--Karrass--Solitar 1972;
Howie 2000, reference [4]; Kurosh).

For a root presentation `P` of `G` (so `G ≅ ⟨X | u ^ l⟩` with `u` not a proper power) and
`Q = FKSQuotient P = ⟨X | u⟩`, the kernel of the canonical map `⟨X | u ^ l⟩ →* ⟨X | u⟩` is the free
product of `|Q|` copies of the cyclic group `ℤ/l` (the conjugates of `⟨u⟩ ≅ ℤ/l`, indexed by `Q`).
For `l = 1` the group `ZMod 1` is trivial and the statement says that the kernel is trivial, which
is exactly the case `G = Q`. -/
def FKSKernelStructure (P : RootPresentation G) : Prop :=
  Nonempty ((fksQuotientHom P).ker ≃*
    Monoid.CoprodI (fun _ : FKSQuotient P => Multiplicative (ZMod P.l)))

/-- **The FKS structure theorem for the kernel, geometric (Bass--Serre) form.**

The free-product decomposition `ker π ≅ ∗_{q ∈ Q} ℤ/l` of the FKS structure theorem exhibits a tree
on which `ker π` acts with finite vertex stabilisers (the conjugates of `⟨u⟩`) and trivial edge
stabilisers.  This structure records exactly what `Work.ORLocInd.fksKernelCondition_of_tree`
consumes. -/
structure FKSKernelTreeData (P : RootPresentation G) where
  /-- the tree -/
  T : Type u
  /-- the quiver structure -/
  [quiver : Quiver T]
  /-- the reversal of arrows -/
  [hasReverse : Quiver.HasInvolutiveReverse T]
  /-- the action of the kernel -/
  [action : MulAction (fksQuotientHom P).ker T]
  /-- the action on arrows -/
  [graphAction : Work.ORBassSerre.GraphAction (fksQuotientHom P).ker T]
  /-- the tree is non-empty -/
  [nonempty : Nonempty T]
  /-- it is a tree -/
  isTree : Work.ORBassSerre.IsTree T
  /-- no arrow is its own reverse -/
  noSelfLoop : ∀ e : Quiver.Total T, e.reverse ≠ e
  /-- the action has no inversions -/
  noInversions : Work.ORBassSerre.ActsWithoutInversions (fksQuotientHom P).ker T
  /-- vertex stabilisers are finite (they are the conjugates of `⟨u⟩ ≅ ℤ / l`) -/
  finiteVertexStab : ∀ x : T, Finite (MulAction.stabilizer (fksQuotientHom P).ker x)
  /-- edge stabilisers are trivial -/
  trivialEdgeStab : ∀ e : Quiver.Total T,
    Subsingleton (MulAction.stabilizer (fksQuotientHom P).ker e)

/-! ## The geometric form implies the kernel condition (complete, no further input) -/

/-- The Bass--Serre form of the FKS structure theorem implies the kernel condition, by
`FKSTree.fksKernelCondition_of_tree`: a torsion-free subgroup of `ker π` meets the finite vertex
stabilisers trivially, acts freely on the tree, and is therefore free. -/
theorem fksKernelCondition_of_kernelTree (P : RootPresentation G)
    (d : FKSKernelTreeData P) : FKSKernelCondition P := by
  letI := d.quiver
  letI := d.hasReverse
  letI := d.action
  letI := d.graphAction
  letI := d.nonempty
  exact fksKernelCondition_of_tree P d.isTree d.noSelfLoop d.noInversions
    d.finiteVertexStab d.trivialEdgeStab

/-- `FKSStructure G` from the geometric form of the FKS structure theorem. -/
theorem fksStructure_of_kernelTree (P : RootPresentation G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) (d : FKSKernelTreeData P) : FKSStructure G :=
  fksStructure_of_kernelCondition P C (fksKernelCondition_of_kernelTree P d)

end Work.ORLocInd
