import Mathlib
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.FiniteModelDefs
import Submission.Work.ClassFieldTower.finiteModel_GF
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.realizedByUnramifiedExtensions_f2five_of_genusLevel
import Submission.Work.ClassFieldTower.realizedByUnramifiedExtensions_of_mulEquiv
import Submission.Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv
import Submission.Work.ClassFieldTower.residuallyFiniteTwoGroup_f2five
import Submission.Work.ClassFieldTower.infinite_of_hasMinimalPresentation
import Submission.Work.ClassFieldTower.isPGroup_two_of_residuallyFiniteTwo_of_finite
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five

/-!
# `Work.ClassFieldTower.RefuteRelationBound` -- the universally quantified deficiency bound is FALSE

`Work.ClassFieldTower.KcRelationBound` (`WallShrunk.lean`) is the **universally quantified** form of
the Shafarevich--Koch deficiency bound: for *every* finite presentation whose finite `2`-quotients
look like unramified extensions of `Kc = ℚ(√-30030)`, there is a re-presentation by a minimal
generating set `β` with at most `#β + 1` relators.

**This module proves that statement FALSE**, with a machine-checked refutation in the style of
`Vacuity.lean` (which did the same for the earlier unsound certificate).  The reason is
group-theoretic and has nothing to do with class field theory:

* the *structural* hypotheses of the model are cheap: the explicit **finite** group
  `GF = FreeGroup (Fin 5) ⧸ normalClosure relF` (`FiniteModelDefs.lean`) is isomorphic to
  `(𝔽₂)^5 = F2five` (`finiteModel_GF`), is residually a finite `2`-group, maps onto `F2five`, and
  *all of its finite `2`-quotients are realized by unramified extensions of `Kc`*: they are the
  quotients `(𝔽₂)^k` of the genus group, realized by the subfields of the genus level of `Kc`
  (`hasGenusLevel_witness`, `realizedByUnramifiedExtensions_f2five_of_genusLevel`);
* but **no finite `2`-group can satisfy the conclusion** with `#β ≥ 5`: the finite `p`-group
  Golod--Shafarevich inequality (Chapter B,
  `Commons.GroupTheory.ProPGroup.golod_shafarevich_presentation_card_lt`, bridged in
  `Submission.GroupTheory.GolodShafarevichCriterion`) says every presentation of a finite
  `2`-group by `d` minimal generators and `r` relators has `4 r > d²`, whereas
  `r ≤ d + 1` and `d ≥ 5` give `4 r ≤ d²`.  Hence `KcRelationBound` would imply
  `Infinite GF` for a finite group.

Consequently the deficiency bound cannot be formulated as a statement about *all* models: it is
intrinsically about the **canonical** profinite model of `G_∅`.  The sound form is the existential
`Work.ClassFieldTower.KcShrunkInput` (equivalently `KcWall`, `KcPresentationWall`), which *forces*
its witness group to be infinite and is therefore not refutable this way -- see the discussion in
the `README`.

## Main results

* `realizedByUnramifiedExtensions_f2five` : every finite `2`-quotient of `(𝔽₂)^5` is the Galois
  group of a finite unramified extension of `Kc` (unconditional, from the genus level);
* `residuallyFiniteTwoGroup_GF`, `realizedByUnramifiedExtensions_GF` : the two structural
  hypotheses for the explicit finite model `GF`;
* `kcModelData` : **`Work.ClassFieldTower.KcModelData` is a THEOREM** (it is satisfied by the finite
  genus model, so it carries no arithmetic content -- the content of the wall is entirely in the
  relation count);
* `not_kcRelationBound` : `¬ Work.ClassFieldTower.KcRelationBound`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **Every finite `2`-quotient of `(𝔽₂)^5` is realized by an unramified extension of `Kc`.**

Unconditional: the genus level of `Kc` (`hasGenusLevel_witness`) has Galois group `(𝔽₂)^5` and is
unramified, so all of its subfields are unramified extensions of `Kc`
(`realizedByUnramifiedExtensions_f2five_of_genusLevel`). -/
theorem realizedByUnramifiedExtensions_f2five : RealizedByUnramifiedExtensions Kc F2five :=
  realizedByUnramifiedExtensions_f2five_of_genusLevel hasGenusLevel_witness

/-- The explicit finite model `GF` is residually a finite `2`-group (it is isomorphic to
`F2five`). -/
theorem residuallyFiniteTwoGroup_GF : ResiduallyFiniteTwoGroup GF :=
  residuallyFiniteTwoGroup_of_mulEquiv (Classical.choice finiteModel_GF.2.1)
    residuallyFiniteTwoGroup_f2five

/-- All finite `2`-quotients of the explicit finite model `GF` are realized by unramified
extensions of `Kc` (transport of `realizedByUnramifiedExtensions_f2five` along `GF ≃* F2five`). -/
theorem realizedByUnramifiedExtensions_GF : RealizedByUnramifiedExtensions Kc GF :=
  realizedByUnramifiedExtensions_of_mulEquiv (Classical.choice finiteModel_GF.2.1)
    realizedByUnramifiedExtensions_f2five

/-- **`KcModelData` is a theorem, not an input.**  The explicit finite genus model `GF` (the
elementary abelian group of order `32`, presented by five minimal generators) satisfies every
clause of `Work.ClassFieldTower.KcModelData`: minimality of the five generators
(`finiteModel_GF`), residual `2`-finiteness, realization of all finite `2`-quotients by unramified
extensions of `Kc`, and the surjection `GF ↠ (𝔽₂)^5`.

So the "model half" of the wall carries **no** arithmetic content; the whole content of the
Shafarevich--Koch input is the relation count, isolated as `KcShrunkInput` (see the `README`). -/
theorem kcModelData : KcModelData :=
  ⟨Fin 5, inferInstance, inferInstance, relF, by simpa using finiteModel_GF.2.2,
    residuallyFiniteTwoGroup_GF, realizedByUnramifiedExtensions_GF,
    ⟨(Classical.choice finiteModel_GF.2.1).toMonoidHom,
      (Classical.choice finiteModel_GF.2.1).surjective⟩⟩

/-- **THE UNIVERSALLY QUANTIFIED DEFICIENCY BOUND IS FALSE.**

`KcRelationBound` (`WallShrunk.lean`) demands a re-presentation with `rel'.card ≤ #β + 1` for
*every* model of the finite `2`-quotients of `G_∅`.  The explicit finite model
`GF = FreeGroup (Fin 5) ⧸ normalClosure relF` satisfies all of its hypotheses (minimality of the
five generators, residual `2`-finiteness, realization of the finite `2`-quotients by unramified
extensions of `Kc`, and the genus surjection), while the demanded conclusion is impossible for a
*finite* group with `#β ≥ 5` generators by the finite `p`-group Golod--Shafarevich inequality
(Chapter B): `rel'.card ≤ #β + 1` and `5 ≤ #β` give `4 · rel'.card ≤ #β²`, and Golod--Shafarevich
gives `4 · rel'.card > #β²`.

The sound form of the arithmetic input is the existential `KcShrunkInput` (equivalently `KcWall` /
`KcPresentationWall`), which forces an infinite witness and hence is not refutable by this
argument. -/
theorem not_kcRelationBound : ¬ KcRelationBound := by
  intro h₂
  obtain ⟨hfin, ⟨e⟩, hmin⟩ := finiteModel_GF
  have hres : ResiduallyFiniteTwoGroup GF := residuallyFiniteTwoGroup_of_mulEquiv e
    residuallyFiniteTwoGroup_f2five
  have hreal : RealizedByUnramifiedExtensions Kc GF :=
    realizedByUnramifiedExtensions_of_mulEquiv e realizedByUnramifiedExtensions_f2five
  have hsurj : ∃ φ : GF →* F2five, Function.Surjective φ := ⟨e.toMonoidHom, e.surjective⟩
  obtain ⟨β, iβ, iDβ, rel', hiso, hminβ, hbound⟩ :=
    h₂ (Fin 5) inferInstance inferInstance relF (by simpa using hmin) hres hreal hsurj
  -- the re-presentation gives a *minimal* presentation of the finite group `GF`
  have hpresβ : HasMinimalPresentation GF (Fintype.card β) rel'.card :=
    ⟨β, iβ, iDβ, rel', rfl, rfl, hiso, hminβ⟩
  -- `#β ≥ 5`, because `GF` maps onto `(𝔽₂)^5`
  have h5 : 5 ≤ Fintype.card β :=
    five_le_of_surjective_zmodTwo_five hpresβ e.toMonoidHom e.surjective
  -- hence the Golod--Shafarevich inequality would hold for the *finite* group `GF`
  have hineq : 4 * rel'.card ≤ Fintype.card β * Fintype.card β :=
    Work.ProPDeficiency.four_mul_le_sq_of_le_add_one hbound h5
  have hinf : Infinite GF :=
    infinite_of_hasMinimalPresentation (p := 2)
      (fun hf => isPGroup_two_of_residuallyFiniteTwo_of_finite hres hf) (by omega) hpresβ hineq
  exact (not_finite_iff_infinite.mpr hinf) hfin

end Work.ClassFieldTower
