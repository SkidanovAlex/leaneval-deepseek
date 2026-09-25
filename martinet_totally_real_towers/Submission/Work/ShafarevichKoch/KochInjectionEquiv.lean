import Mathlib
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.kochInjection_of_contH2DimLe

/-!
# `Work.ShafarevichKoch.KochInjectionEquiv` -- the crux is Gaschütz plus the classical injection

This module records the two equivalences that pin down *what is missing* in this chapter.

* `Work.ShafarevichKoch.kochInjection_iff_contH2DimLe` : the classical Shafarevich--Koch
  injection `KochInjection M` (`H²_cont(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨`, Koch Ch. 11 Thm. 11.3) is
  **equivalent** to the numerical relation bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6`
  (`Work.RelatorRank.ContH2DimLe (G_∅) 6`).  So the injection is not a weakening of the bound: it
  is the same arithmetic statement.
* `Work.ShafarevichKoch.kcProTwoPresentationInput_iff_kochInjection_and_gaschutz` : the chapter's
  crux `KcProTwoPresentationInput` is **equivalent** to the conjunction of
  * the classical injection (`∃ M, KochInjection M`), the *arithmetic* input, and
  * `Work.RelatorRank.GaschutzCohomologicalValue` for `G_∅`, the *group-theoretic* input, which is
    the very proposition the top-level `Submission.lean` consumes as
    `Submission.gaschutzCohomologicalValue`.

So no arithmetic is hidden in this chapter any more: item (2) of the deliverable *is* `KochInjection`
(or equivalently the bound `dim H² ≤ 6`), and everything else is proved.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **The classical injection and the numerical bound are equivalent.**

`→` is the dimension count (`contH2DimLe_six_of_kochInjection`, with the proved
`#((V_∅/Kc^{×2}) →* 𝔽₂) = 2^6`); `←` is the finite-dimensional cardinality fact that an
`𝔽₂`-vector space with at most `2^6` elements embeds into the `64`-element dual
(`kochInjection_of_contH2DimLe`). -/
theorem kochInjection_iff_contH2DimLe
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) :
    KochInjection M ↔ Work.RelatorRank.ContH2DimLe (galoisGroup M) 6 :=
  ⟨contH2DimLe_six_of_kochInjection M, kochInjection_of_contH2DimLe M⟩

/-- **The crux *is* the classical injection plus Gaschütz's value theorem.**

Given `Work.RelatorRank.GaschutzCohomologicalValue` for `G_∅` -- the group-theoretic value theorem
`r(Γ) = dim_{𝔽₂}H²(Γ,𝔽₂)` for finitely generated pro-`2` groups, shared with the benchmark's own
wall in `Submission.lean` -- the chapter's crux `KcProTwoPresentationInput` is *equivalent* to the
classical Shafarevich--Koch injection `∃ M, KochInjection M` (`H²_cont(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨`),
i.e. to the arithmetic relation bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6`. -/
theorem kcProTwoPresentationInput_iff_kochInjection_and_gaschutz
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (galoisGroup M)) :
    KcProTwoPresentationInput ↔
      ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2, KochInjection M := by
  constructor
  · intro h
    obtain ⟨M, g, w, hker, hdense⟩ := hasProTwoPresentation_six_of_input h
    have hrr : Work.RelatorRank.RelatorRankLe (galoisGroup M) 6 := by
      show Work.RelatorRank.HasProP2Presentation (galoisGroup M)
        (Work.RelatorRank.GeneratorRank (galoisGroup M)) 6
      rw [generatorRank_galoisGroup_Kc M]
      exact hasProP2Presentation_of_relators M g w hker hdense
    exact ⟨M, (kochInjection_iff_contH2DimLe M).mpr
      (Work.RelatorRank.contH2DimLe_of_relatorRankLe (hdict M) hrr)⟩
  · intro h
    exact kcProTwoPresentationInput_of_kochInjection hdict h

end Work.ShafarevichKoch
