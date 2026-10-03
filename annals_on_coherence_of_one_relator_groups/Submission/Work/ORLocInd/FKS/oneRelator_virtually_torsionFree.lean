/-
# Fischer--Karrass--Solitar 1972: one-relator groups are virtually torsion-free

**Theorem.** Every one-relator group has a normal torsion-free subgroup of finite index.

This module proves it from

* the *free-group* form of Fischer--Karrass--Solitar, Theorem 2
  (`Work.ORLocInd.FKS.hasFKSTorsionQuotient_of_freeGroup`, whose only external input is P. Hall's
  theorem that the free group on a finite set is residually a finite `p`-group); and
* the Karrass--Magnus--Solitar torsion theorem, which node N2 exports as the bundled structure
  `Work.OROneRel.OneRelatorCombinatorics`.

The route (FKS 1972) is:

* a one-relator group `G` with presentation `⟨X | r⟩` and `r = 1` is free, hence torsion-free;
* otherwise `r = u ^ l` with `l ≥ 1`, `u` not a proper power and `u ≠ 1` (the Karrass--Magnus--Solitar
  root of `r`), and it suffices to find a finite quotient of `⟨X | u ^ l⟩` in which the image of `u`
  has order exactly `l`; then the kernel of that quotient is torsion-free by KMS, since every
  torsion element of `⟨X | u ^ l⟩` is conjugate to a power of `u`, and `u` has order exactly `l`;
* the finite quotient exists by FKS Theorem 2, applied to the free group on `X`.

Note that this route does *not* go through the Magnus--Moldavanskii hierarchy, and in particular it
does not use the HNN extension step (`Work.ORLocInd.HNNVirtualTorsionFree`), which is in fact a
**false** statement about general HNN extensions.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Core
import Submission.Work.ORLocInd.Bridge.N2
import Submission.Work.ORLocInd.FKS.hasFKSTorsionQuotient_of_freeGroup
import Submission.Work.OROneRel.exists_root
import Submission.Work.OROneRel.presentedGroup_one_iso_freeGroup

set_option autoImplicit false

universe u

namespace Work.ORLocInd.FKS

open Work.ORLocInd

/-- **Fischer--Karrass--Solitar 1972**: every one-relator group is virtually torsion-free, i.e. has a
normal torsion-free subgroup of finite index.

The only inputs are the definition of `Group.OneRelator`, the Karrass--Magnus--Solitar torsion
theorem (node N2's `OneRelatorCombinatorics`) and P. Hall's residual `p`-finiteness of finite rank
free groups. -/
theorem oneRelator_virtually_torsionFree {G : Type u} [Group G] (hG : Group.OneRelator G)
    (C : Work.OROneRel.OneRelatorCombinatorics.{u}) : VirtuallyTorsionFree G := by
  obtain ⟨α, rel, ⟨e⟩⟩ := hG
  by_cases hrel : rel = 1
  · -- the trivial relator presents the free group on `α`, which is torsion-free
    have hfree : VirtuallyTorsionFree (PresentedGroup ({rel} : Set (FreeGroup α))) := by
      rw [hrel]
      exact virtuallyTorsionFree_presentedGroup_one
    exact VirtuallyTorsionFree.of_mulEquiv e hfree
  · -- nontrivial relator: take its root
    obtain ⟨u, l, hl, hul, hu⟩ := Work.OROneRel.exists_root rel hrel
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, one_pow] at hul
      exact hrel hul
    have hpp : ¬ IsProperPower u := fun h => hu (orOneRel_isProperPower_of_isProperPower h)
    let P : RootPresentation G :=
      { α := α, u := u, l := l, one_le_l := hl, not_properPower := hpp, equiv := hul ▸ e }
    exact virtuallyTorsionFree_of_kms_of_fks_rootPresentation C P
      (hasFKSTorsionQuotient_of_freeGroup P hu1)

end Work.ORLocInd.FKS
