/-
# Node N4: the two theorems (virtual torsion-freeness; local indicability of torsion-free subgroups)

This module states and proves the two theorems of node N4 of the route design (see `README.md`),
from the structural inputs declared in `Submission.Work.ORLocInd.Basic`:

* `HNNVirtualTorsionFree` (the HNN step of the Fischer--Karrass--Solitar induction),
* `BrodskiiTorsionFreeOneRelator` (Brodskii 1984; Howie 2000, Theorem 3.1),
* `FKSStructure` (the structural half of FKS 1972 used by Howie's Corollary 3.2).

The API (`IsTorsionFree`, `Group.LocallyIndicable`, `VirtuallyTorsionFree`, the KMS kernel argument,
...) is in `Submission.Work.ORLocInd.Core`; the hierarchy base case and its propagation in
`Submission.Work.ORLocInd.FKS` / `Submission.Work.ORLocInd.Hierarchy`; the reduction of
`Group.OneRelator G` to a hierarchy in `Submission.Work.ORLocInd.Assembly`; and Howie's reduction in
`Submission.Work.ORLocInd.Brodskii`.
-/
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Core
import Submission.Work.ORLocInd.Assembly.oneRelator_virtually_torsionFree
import Submission.Work.ORLocInd.FKS.oneRelator_virtually_torsionFree
import Submission.Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable
import Submission.Work.ORLocInd.Brodskii.brodskiiTorsionFreeOneRelator
import Submission.Work.ORLocInd.FKSStruc
import Submission.Work.ORLocInd.FKSKernelTree
import Submission.Work.ORLocInd.FKSKernelCondition
import Submission.Work.ORLocInd.FKSKernel.fksKernelStructure
import Submission.Work.ORLocInd.RootPresentation.exists_rootPresentation_of_oneRelator
import Submission.Work.OROneRel.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open Work.ORLocInd

namespace Work.ORLocInd

/-! ## 5. Auxiliary forms of the FKS input -/

/-- Over the Magnus--Karrass--Solitar torsion theory, the FKS finite quotient formulation of
virtual torsion-freeness and virtual torsion-freeness itself are equivalent. -/
theorem hasFKSTorsionQuotient_iff_virtuallyTorsionFree {G : Type u} [Group G]
    (P : RootPresentation G) (hKMS : TorsionTheory P) :
    HasFKSTorsionQuotient P ↔ VirtuallyTorsionFree G := by
  constructor
  · rintro ⟨Q, hQ, hQfin, φ, hφ⟩
    letI := hQ
    letI := hQfin
    refine ⟨MonoidHom.ker φ, ?_, ?_, ?_⟩
    · exact MonoidHom.normal_ker φ
    · exact Subgroup.finiteIndex_ker φ
    · exact isTorsionFree_ker_of_orderOf hKMS.orderOf_root hKMS.torsion_conj φ hφ
  · exact exists_finiteQuotient_of_virtuallyTorsionFree P hKMS

/-- The two formulations of the FKS/KMS input are interchangeable: from a root presentation
satisfying KMS and the literature form of FKS (`VirtuallyTorsionFree G`) one obtains
`HasTorsionInput G` with the sharp FKS finite quotient. -/
theorem hasTorsionInput_of_kms_of_virtuallyTorsionFree {G : Type u} [Group G]
    (hP : ∃ P : RootPresentation G, TorsionTheory P) (hvt : VirtuallyTorsionFree G) :
    HasTorsionInput G := by
  obtain ⟨P, hKMS⟩ := hP
  exact ⟨P, hKMS, (hasFKSTorsionQuotient_iff_virtuallyTorsionFree P hKMS).mpr hvt⟩

/-! ## 6. The two theorems of node N4

Both theorems are proved from the *structural* inputs recorded in
`Submission.Work.ORLocInd.Basic`:

* `HNNVirtualTorsionFree` -- the HNN step of the FKS induction over the Magnus--Moldavanskii
  hierarchy (FKS 1972);
* `BrodskiiTorsionFreeOneRelator` -- Brodskii's theorem (Brodskii 1984; Howie 2000, Theorem 3.1);
* `FKSStructure` -- the structural half of Fischer--Karrass--Solitar 1972 used by Howie's
  Corollary 3.2.

The one-relator-specific content -- the terminal base case of the hierarchy, the propagation up the
hierarchy, the cyclically-reduced-conjugate reduction, the extension step for local indicability and
Howie's reduction of the torsion case to Brodskii's theorem -- is proved in this subproject
(`FKS/`, `Hierarchy/`, `HNN/`, `Extension/`, `Brodskii/`).

**The two remaining inputs, and where they come from.**  *FKS 1972* prove the HNN step
`HNNVirtualTorsionFree` by a double induction over the Magnus--Moldavanskii hierarchy (the step
being: an HNN extension of a virtually torsion-free group along finitely generated Magnus subgroups
is virtually torsion-free); here the step is isolated as a general statement about HNN extensions,
and the special case in which the compatible finite quotient is available is proved in
`Work.ORLocInd.HNN.virtuallyTorsionFree_hnnExtension_of_quotient` /
`..._of_normal`.  *Brodskii's theorem* and the *FKS structure theorem* are used in Howie's form of
the argument (`Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable`, which formalises
Howie 2000, Corollary 3.2). -/

set_option linter.unusedVariables false in
/-- **Fischer--Karrass--Solitar (1972)**: every one-relator group has a normal torsion-free
subgroup of finite index.  The conclusion is `VirtuallyTorsionFree G` unfolded, i.e.
`∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G'`. -/
theorem oneRelator_virtually_torsionFree {G : Type u} [Group G] (hG : Group.OneRelator G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) :
    VirtuallyTorsionFree G :=
  FKS.oneRelator_virtually_torsionFree hG C

set_option linter.unusedVariables false in
/-- **Brodskii (1984); Howie (2000), Corollary 3.2**: every torsion-free subgroup of a one-relator
group is locally indicable, given the FKS structure input `S : FKSStructure G` (which supplies the
Fischer--Karrass--Solitar decomposition of `G` used by Howie).  The *unconditional* form (from the
FKS structure theorem, i.e. from `FKSKernel.fksKernelStructure`) is
`torsionFree_subgroup_locallyIndicable` below; this variant is kept for callers that already have an
`FKSStructure`. -/
theorem torsionFree_subgroup_locallyIndicable_of_fksStructure {G : Type u} [Group G]
    (hG : Group.OneRelator G)
    (S : FKSStructure G) (H : Subgroup G)
    (hH : IsTorsionFree H) : Group.LocallyIndicable H :=
  _root_.Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable
    Work.ORLocInd.brodskiiTorsionFreeOneRelator S H hH

set_option linter.unusedVariables false in
/-- For a **torsion-free** one-relator group the structural input `FKSStructure G` is automatic
(`Work.ORLocInd.fksStructure_of_torsionFree`), so Howie's Corollary 3.2 holds with no input beyond
Brodskii's theorem (which is proved, hypothesis-free, in `Brodskii/brodskiiTorsionFreeOneRelator`):
every subgroup of a torsion-free one-relator group is locally indicable.

Equivalently: the only one-relator groups for which `FKSStructure` is a genuine input are those
with torsion. -/
theorem torsionFree_subgroup_locallyIndicable_of_torsionFree {G : Type u} [Group G]
    (hG : Group.OneRelator G) (htf : IsTorsionFree G) (H : Subgroup G)
    (hH : IsTorsionFree H) : Group.LocallyIndicable H :=
  torsionFree_subgroup_locallyIndicable_of_fksStructure hG
    (Work.ORLocInd.fksStructure_of_torsionFree hG htf) H hH

set_option linter.unusedVariables false in
/-- **Brodskii (1984); Howie (2000), Theorem 3.1**: a torsion-free one-relator group is locally
indicable. -/
theorem torsionFree_oneRelator_locallyIndicable {G : Type u} [Group G] (hG : Group.OneRelator G)
    (htf : IsTorsionFree G) : Group.LocallyIndicable G :=
  Work.ORLocInd.brodskiiTorsionFreeOneRelator.locallyIndicable G hG htf

/-! ## 6′. The two theorems of node N4, unconditionally

The hypotheses `FKSStructure G` of §6 are now *proved* for every one-relator group: for a
torsion-free `G` by `FKSStruc.fksStructure_of_torsionFree`, and in general by the FKS/Kurosh
structure theorem `FKSKernel.fksKernelStructure` (proved in `Submission/Work/ORLocInd/FKSKernel/`)
combined with `RootPresentation.exists_rootPresentation_of_oneRelator`.  The theorems below carry
therefore the same single hypothesis as Theorem 1: node N2's `OneRelatorCombinatorics` (`C`). -/

set_option linter.unusedVariables false in
/-- **Brodskii (1984); Howie (2000), Corollary 3.2**, unconditionally: every torsion-free subgroup
of a one-relator group is locally indicable. -/
theorem torsionFree_subgroup_locallyIndicable {G : Type u} [Group G] (hG : Group.OneRelator G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) (H : Subgroup G)
    (hH : IsTorsionFree H) : Group.LocallyIndicable H := by
  rcases RootPresentation.exists_rootPresentation_of_oneRelator hG with ⟨P, hu⟩ | htf
  · exact torsionFree_subgroup_locallyIndicable_of_fksStructure hG
      (fksStructure_of_kernelStructure P C (FKSKernel.fksKernelStructure P hu)) H hH
  · exact torsionFree_subgroup_locallyIndicable_of_torsionFree hG htf H hH

/-- The form in which the paper uses the two theorems: a one-relator group is virtually locally
indicable. -/
theorem virtuallyLocallyIndicable_of_oneRelator {G : Type u} [Group G] (hG : Group.OneRelator G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) :
    VirtuallyLocallyIndicable G := by
  obtain ⟨G', hN, hfi, htf⟩ := oneRelator_virtually_torsionFree hG C
  exact ⟨G', hN, hfi, torsionFree_subgroup_locallyIndicable hG C G' htf⟩

/-- The output of node N4 in the form consumed by the later nodes: a one-relator group has a
normal, finite-index, torsion-free, locally indicable subgroup. -/
theorem exists_normal_finiteIndex_torsionFree_locallyIndicable {G : Type u} [Group G]
    (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u}) :
    ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G' ∧
      Group.LocallyIndicable G' :=
  virtuallyLocallyIndicable_iff_exists.mp
    (virtuallyLocallyIndicable_of_oneRelator hG C)

/-- The `FKSStructure`-conditional form of `virtuallyLocallyIndicable_of_oneRelator`, kept for
callers that already have an `FKSStructure` for `G`. -/
theorem virtuallyLocallyIndicable_of_oneRelator_of_fksStructure {G : Type u} [Group G]
    (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (S : FKSStructure G) : VirtuallyLocallyIndicable G := by
  obtain ⟨G', hN, hfi, htf⟩ := oneRelator_virtually_torsionFree hG C
  exact ⟨G', hN, hfi, torsionFree_subgroup_locallyIndicable_of_fksStructure hG S G' htf⟩

/-- The `FKSStructure`-conditional form of
`exists_normal_finiteIndex_torsionFree_locallyIndicable`. -/
theorem exists_normal_finiteIndex_torsionFree_locallyIndicable_of_fksStructure {G : Type u}
    [Group G] (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (S : FKSStructure G) :
    ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G' ∧
      Group.LocallyIndicable G' :=
  virtuallyLocallyIndicable_iff_exists.mp
    (virtuallyLocallyIndicable_of_oneRelator_of_fksStructure hG C S)

/-! ## 7. Node N4 against the *named* FKS structure input

The theorem that supplies `FKSStructure G` for a one-relator group `G` is the FKS/Kurosh structure
theorem, stated in `Submission.Work.ORLocInd.FKSKernelTree`:

* `FKSKernelStructure P` (algebraic form): for the root presentation `P` of `G` and
  `Q = FKSQuotient P = ⟨X | u⟩`, the kernel of `⟨X | u ^ l⟩ →* ⟨X | u⟩` is the free product of the
  conjugates of `⟨u⟩ ≅ ℤ/l`, indexed by `Q`;
* `FKSKernelTreeData P` (geometric form): the Bass--Serre tree of that free-product decomposition.

`fksStructure_of_kernelTree` proves the geometric form implies `FKSStructure G` using only
`FKSTree.fksKernelCondition_of_tree`.  The variants below are the two theorems restated against that
single named input. -/

set_option linter.unusedVariables false in
/-- **Howie 2000, Corollary 3.2**, from the geometric form of the FKS structure theorem. -/
theorem torsionFree_subgroup_locallyIndicable_of_kernelTree {G : Type u} [Group G]
    (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (P : RootPresentation G) (d : FKSKernelTreeData P) (H : Subgroup G)
    (hH : IsTorsionFree H) : Group.LocallyIndicable H :=
  _root_.Work.ORLocInd.Brodskii.torsionFree_subgroup_locallyIndicable
    Work.ORLocInd.brodskiiTorsionFreeOneRelator (fksStructure_of_kernelTree P C d) H hH

/-- A one-relator group is virtually locally indicable, from the geometric form of the FKS
structure theorem. -/
theorem virtuallyLocallyIndicable_of_oneRelator_of_kernelTree {G : Type u} [Group G]
    (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (P : RootPresentation G) (d : FKSKernelTreeData P) : VirtuallyLocallyIndicable G := by
  obtain ⟨G', hN, hfi, htf⟩ := oneRelator_virtually_torsionFree hG C
  exact ⟨G', hN, hfi,
    torsionFree_subgroup_locallyIndicable_of_kernelTree hG C P d G' htf⟩

/-- The output of node N4 in the form consumed by the later nodes, from the geometric form of the
FKS structure theorem. -/
theorem exists_normal_finiteIndex_torsionFree_locallyIndicable_of_kernelTree {G : Type u}
    [Group G] (hG : Group.OneRelator G) (C : Work.OROneRel.OneRelatorCombinatorics.{u})
    (P : RootPresentation G) (d : FKSKernelTreeData P) :
    ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G' ∧
      Group.LocallyIndicable G' :=
  virtuallyLocallyIndicable_iff_exists.mp
    (virtuallyLocallyIndicable_of_oneRelator_of_kernelTree hG C P d)

end Work.ORLocInd
