import Mathlib
import Submission.Work.ShafarevichKoch.Gaschutz.RelModule
import Submission.Work.ShafarevichKoch.Crux
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.KcRealization

/-!
# `Work.ShafarevichKoch.Gaschutz.Kc` -- the relation-module form of the crux for `Kc`

The deliverable's arithmetic crux for `Kc = ℚ(√-30030)` is the classical Shafarevich--Koch
relation bound for the maximal unramified pro-`2` extension: `df(G_∅) = r - d ≤ d₂(O_Kc^×) = 1`.
`Work.ShafarevichKoch.KcProTwoPresentationInput` states it as `HasProTwoPresentation Kc 5 6` -- a
*presentation* of `G_∅` with `5 = rank₂ Cl(Kc)` generators and at most
`6 = rank₂ Cl(Kc) + d₂(O_Kc^×)` relators.

This module records the two statements as **equivalent** and exports the consequences (the walls of
the benchmark route) in the relation-module form as well:

* `Work.ShafarevichKoch.KcRelModuleBound` : the relation module `K/(K²[K,F])` of `G_∅` is generated
  by `6` elements, where `K = ker (FreeGroup.lift g)` for a topological generating family
  `g : Fin 5 → G_∅`;
* `kcRelModuleBound_iff_input` : it is *equivalent* to `KcProTwoPresentationInput`;
* `infiniteProTwoExtension_Kc_of_relModuleBound`,
  `unramifiedPro2TowerWall_of_relModuleBound`, `boundedRdTowerWall_of_relModuleBound`,
  `exists_unramifiedLevel_rootDiscr_of_relModuleBound` : the walls;
* `proTwoShafarevichKochInput_Kc_of_relModuleBound_and_realization` : item (3) of the deliverable
  from the relation-module form plus the realization clause.

The reformulation matters because the classical theorem (Koch, *Galois theory of `p`-extensions*,
Ch. 11 Thm 11.3; Shafarevich 1963; Hajir--Maire--Ramakrishna arXiv:2103.09508) is *proved* by
exhibiting the relations of `G_∅`, i.e. in the relation-module form, while the workspace's
Golod--Shafarevich engine consumes the presentation form.  Either can now be used.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The Shafarevich--Koch relation bound for `Kc`, in relation-module form.**

There is a topological generating family `g : Fin 5 → G_∅` of `G_∅ = Gal(Kc_∅/Kc)` and a set of
`6` words in the kernel of the presentation map `FreeGroup (Fin 5) →* G_∅` which generates the
kernel modulo the relation-Frattini subgroup `K²[K,F]`; the presented abstract group is residually a
finite `2`-group.

This is the classical deficiency bound `df(G_∅) ≤ d₂(O_Kc^×) = 1` in the form in which its proof
produces it.  By `kcRelModuleBound_iff_input` it is equivalent to the presentation form
`Work.ShafarevichKoch.KcProTwoPresentationInput`. -/
def KcRelModuleBound : Prop := HasRelModulePresentation Kc 5 6

/-- **The two forms of the crux for `Kc` are equivalent.** -/
theorem kcRelModuleBound_iff_input : KcRelModuleBound ↔ KcProTwoPresentationInput := by
  rw [KcRelModuleBound, ← hasProTwoPresentation_iff_hasRelModulePresentation,
    ← kcProTwoPresentationInput_iff_five_six]

/-- **The relation-module form of the crux gives the presentation form.** -/
theorem kcProTwoPresentationInput_of_relModuleBound (h : KcRelModuleBound) :
    KcProTwoPresentationInput :=
  kcRelModuleBound_iff_input.mp h

/-- **The concrete conclusion: `Kc` has an infinite Hilbert `2`-class field tower.** -/
theorem infiniteProTwoExtension_Kc_of_relModuleBound (h : KcRelModuleBound) :
    Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_Kc_of_input (kcProTwoPresentationInput_of_relModuleBound h)

/-- **The conclusion in the caller's wall form.** -/
theorem unramifiedPro2TowerWall_of_relModuleBound (h : KcRelModuleBound) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_input (kcProTwoPresentationInput_of_relModuleBound h)

/-- **The root-discriminant tower wall for `Kc`.** -/
theorem boundedRdTowerWall_of_relModuleBound (h : KcRelModuleBound) :
    Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input (kcProTwoPresentationInput_of_relModuleBound h)

/-- **Unramified levels of every prescribed degree with constant root discriminant.** -/
theorem exists_unramifiedLevel_rootDiscr_of_relModuleBound (h : KcRelModuleBound) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  obtain ⟨M, g, w, hker, hdense⟩ := hasProTwoPresentation_six_of_input
    (kcProTwoPresentationInput_of_relModuleBound h)
  exact exists_unramifiedLevel_rootDiscr_of_hasProTwoPresentation
    ⟨M, g, w, hker, hdense⟩ (by norm_num) N

/-- **Item (3) of the deliverable, from the relation-module form and the realization clause.**

`Work.ShafarevichKoch.KcRelModuleBound` (item (2), the Shafarevich--Koch relation bound in
relation-module form) together with the realization clause `RealizationClauseKc` gives the sound
interface `Work.ClassFieldTower.ProTwoShafarevichKochInput Kc`. -/
theorem proTwoShafarevichKochInput_Kc_of_relModuleBound_and_realization
    (h : KcRelModuleBound) (hreal : RealizationClauseKc) :
    ProTwoShafarevichKochInput Kc :=
  proTwoShafarevichKochInput_Kc_of_input_and_realization
    (kcProTwoPresentationInput_of_relModuleBound h) hreal

end Work.ShafarevichKoch
