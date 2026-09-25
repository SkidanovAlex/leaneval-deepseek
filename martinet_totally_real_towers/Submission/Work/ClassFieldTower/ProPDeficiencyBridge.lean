import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ProPDeficiency.Arithmetic

/-!
# `Work.ClassFieldTower.ProPDeficiencyBridge` -- the wall in the `Work.ProPDeficiency` vocabulary

The group-theoretic chapter `Submission/Work/ProPDeficiency/` (`Namespace Work.ProPDeficiency`)
packages the Golod--Shafarevich criterion as
`Work.ProPDeficiency.infinite_and_unbounded_two_pow_quotients_of_deficiency`, whose hypotheses are

* a finitely generated, residually finite group `G` **all of whose finite quotients are
  `2`-groups** (`hquot`), rather than "residually a finite `2`-group";
* a presentation `IsPresentation α rel G` with **deficiency at least `-1`**
  (`Deficiency (Fintype.card α) rel.card (-1)`, i.e. `rel.card ≤ Fintype.card α + 1`), minimality
  of `α`, and `5 ≤ Fintype.card α`.

This module translates that interface into the one consumed by this chapter
(`Work.ClassFieldTower.KcShrunkInput`, see `WallShrunk.lean`), so that a prover who supplies the
Shafarevich--Koch relation count in the `Work.ProPDeficiency` vocabulary can run the class-field
tower of this chapter unchanged:

* `residuallyFiniteTwoGroup_of_residuallyFinite` -- "residually finite + all finite quotients are
  `2`-groups" is `ResiduallyFiniteTwoGroup` (a general group-theoretic fact, useful on its own);
* `KcProPDeficiencyInput` -- the arithmetic input for `Kc = ℚ(√-30030)` in the
  `Work.ProPDeficiency` vocabulary;
* `kcShrunkInput_of_proPDeficiencyInput` -- it implies `KcShrunkInput`;
* `infiniteProTwoExtension_of_proPDeficiencyInput` -- hence the conclusion
  `InfiniteProTwoExtension Kc` (`F_∅` infinite).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **"Residually finite + all finite quotients are `2`-groups" is `ResiduallyFiniteTwoGroup`.**

If every nontrivial `g` survives a finite-index normal subgroup (`Group.ResiduallyFinite`) and
every finite quotient of `G` is a `2`-group, then every nontrivial `g` survives in a finite
`2`-group quotient: combine the residual finiteness with the quotient hypothesis. -/
theorem residuallyFiniteTwoGroup_of_residuallyFinite {G : Type*} [Group G]
    [Group.ResiduallyFinite G]
    (hquot : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) :
    ResiduallyFiniteTwoGroup G := by
  intro g hg
  obtain ⟨H, hH⟩ := Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp
    (inferInstance : Group.ResiduallyFinite G) g hg
  haveI : H.toSubgroup.Normal := H.isNormal'
  haveI : H.toSubgroup.FiniteIndex := H.isFiniteIndex'
  refine ⟨H.toSubgroup, H.isNormal', inferInstance, hquot H.toSubgroup inferInstance, ?_⟩
  intro h
  refine hH ?_
  have h2 : g ∈ H.toSubgroup :=
    (QuotientGroup.eq_one_iff (N := H.toSubgroup) g).mp
      (by simpa [QuotientGroup.mk'_apply] using h)
  simpa only [FiniteIndexNormalSubgroup.mem_toSubgroup_iff] using h2

/-- **The arithmetic input for `Kc = ℚ(√-30030)`, in the `Work.ProPDeficiency` vocabulary.**

There is a finitely generated, residually finite group `G` all of whose finite quotients are
`2`-groups, whose finite `2`-quotients are realized by unramified extensions of `Kc`
(`RealizedByUnramifiedExtensions`), which has a minimal presentation by `α` with
`5 ≤ #α` generators and `rel.card ≤ #α + 1` relators (the Shafarevich--Koch deficiency bound
`df ≥ -1`).

This is `KcShrunkInput` (`WallShrunk.lean`) with the residual condition and the presentation
spelled in the vocabulary of `Work.ProPDeficiency`; a version of the Shafarevich--Koch relation
count formalised in that vocabulary feeds this chapter through
`kcShrunkInput_of_proPDeficiencyInput`. -/
def KcProPDeficiencyInput : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Group.FG G) (_ : Group.ResiduallyFinite G)
    (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    Work.ProPDeficiency.IsPresentation α rel G ∧
    Work.ProPDeficiency.Deficiency (Fintype.card α) rel.card (-1) ∧
    (∀ S : Finset G, Work.ProPDeficiency.IsGeneratingSet S → Fintype.card α ≤ S.card) ∧
    5 ≤ Fintype.card α ∧
    (∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N)) ∧
    RealizedByUnramifiedExtensions Kc G

/-- **The `Work.ProPDeficiency`-form of the input implies the form consumed by this chapter.** -/
theorem kcShrunkInput_of_proPDeficiencyInput (h : KcProPDeficiencyInput) : KcShrunkInput := by
  obtain ⟨G, iG, hfg, hresfin, α, iα, iDα, rel, hpres, hdef, hmin, h5, hquot, hreal⟩ := h
  have hres2 : ResiduallyFiniteTwoGroup G :=
    residuallyFiniteTwoGroup_of_residuallyFinite (G := G) hquot
  have hdef' : rel.card ≤ Fintype.card α + 1 :=
    Work.ProPDeficiency.Deficiency.neg_one_iff.mp hdef
  exact ⟨G, iG, α, iα, iDα, rel, hpres, hdef', hmin, hres2, hreal, h5⟩

/-- **The conclusion from the `Work.ProPDeficiency`-form of the input**: the maximal unramified
pro-`2` extension of `Kc` is infinite. -/
theorem infiniteProTwoExtension_of_proPDeficiencyInput (h : KcProPDeficiencyInput) :
    InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_of_kcShrunkInput (kcShrunkInput_of_proPDeficiencyInput h)

end Work.ClassFieldTower
