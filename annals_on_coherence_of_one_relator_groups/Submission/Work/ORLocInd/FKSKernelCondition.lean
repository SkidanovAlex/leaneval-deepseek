/-
# The algebraic FKS structure theorem implies the kernel condition

`FKSKernelTree.FKSKernelStructure P` is the algebraic form of the FKS/Kurosh structure theorem: the
kernel of `⟨X | u ^ l⟩ →* ⟨X | u⟩` is the free product of the conjugates of `⟨u⟩ ≅ ℤ / l`, indexed by
`⟨X | u⟩`.  This module records the (short) implication

  `FKSKernelStructure P → FKSKernelCondition P`,

which is how the algebraic form feeds Howie's Corollary 3.2.  It uses the Kurosh subgroup theorem
for free products of finite groups, `CoprodTree.isFreeGroup_of_isTorsionFree_subgroup`: a
torsion-free subgroup of a free product of finite groups is free, hence locally indicable.

The geometric form is handled separately and completely by
`FKSKernelTree.fksKernelCondition_of_kernelTree`, which needs no input at all.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSKernelTree
import Submission.Work.ORLocInd.CoprodTree.isFreeGroup_of_isTorsionFree_subgroup_univ
import Submission.Work.ORLocInd.LI.isFreeGroup_locallyIndicable
import Submission.Work.ORLocInd.LI.locallyIndicable_of_injective
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective
import Submission.Work.OROneRel.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd

variable {G : Type u} [Group G]

/-- **The algebraic FKS structure theorem implies the kernel condition.**

Let `e : ker π ≃* ∗_{q ∈ Q} ℤ / l` be the isomorphism of `FKSKernelStructure P`, and let
`K ≤ ker π` be torsion-free.  Its image `K' = K.map e` is a torsion-free subgroup of a free product
of finite groups, hence free (Kurosh) and therefore locally indicable; local indicability pulls back
along the injection `K →* K'`.

(The factors `Multiplicative (ZMod P.l)` are finite because `P.l ≠ 0`, which is
`NeZero.of_pos` applied to `P.one_le_l`.) -/
theorem fksKernelCondition_of_kernelStructure (P : RootPresentation G)
    (h : FKSKernelStructure P) : FKSKernelCondition P := by
  obtain ⟨e⟩ := h
  intro K hK
  haveI : NeZero P.l :=
    NeZero.of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one P.one_le_l)
  -- the image of `K` in the free product
  let K' : Subgroup (Monoid.CoprodI (fun _ : FKSQuotient P => Multiplicative (ZMod P.l))) :=
    K.map e.toMonoidHom
  -- `K'` is torsion-free, being isomorphic to `K`
  have hK' : IsTorsionFree ↥K' :=
    Work.ORLocInd.TF.isTorsionFree_of_injective
      (((e.subgroupMap K).symm).toMonoidHom : ↥K' →* ↥K) (e.subgroupMap K).symm.injective hK
  -- hence `K'` is free and locally indicable
  haveI : IsFreeGroup ↥K' :=
    Work.ORLocInd.CoprodTree.isFreeGroup_of_isTorsionFree_subgroup_univ (K := K') hK'
  have hLI' : Group.LocallyIndicable ↥K' := Work.ORLocInd.LI.isFreeGroup_locallyIndicable ↥K'
  -- and local indicability pulls back along the injection `K →* K'`
  exact Work.ORLocInd.LI.locallyIndicable_of_injective
    ((e.subgroupMap K).toMonoidHom : ↥K →* ↥K') (e.subgroupMap K).injective hLI'

/-- `FKSStructure G` from the algebraic form of the FKS structure theorem. -/
theorem fksStructure_of_kernelStructure (P : RootPresentation G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) (h : FKSKernelStructure P) : FKSStructure G :=
  fksStructure_of_kernelCondition P C (fksKernelCondition_of_kernelStructure P h)

/-- `FKSStructure G` from *some* root presentation of `G` satisfying the algebraic FKS structure
theorem.  (For a one-relator group with torsion, any root presentation does: `u ≠ 1` is forced, and
`FKSKernel.fksKernelStructure` supplies the isomorphism.) -/
theorem fksStructure_of_exists_kernelStructure
    (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (h : ∃ P : RootPresentation G, FKSKernelStructure P) : FKSStructure G := by
  obtain ⟨P, hP⟩ := h
  exact fksStructure_of_kernelStructure P C hP

end Work.ORLocInd
