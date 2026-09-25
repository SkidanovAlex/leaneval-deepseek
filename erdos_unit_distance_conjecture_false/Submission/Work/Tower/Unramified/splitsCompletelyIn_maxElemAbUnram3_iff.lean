import Mathlib
import Submission.Work.Tower.Unramified.MaxElemAb
import Submission.Work.Tower.Unramified.maxElemAbUnram3_isUnramified
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

/-!
# Complete splitting in `maxElemAbUnram3 F` as a universal property

Assuming `maxElemAbUnram3 F` (the maximal finite everywhere-unramified elementary abelian
`3`-extension of `F`, inside `AlgebraicClosure F`) is finite dimensional over `F`, a prime
`𝔭` of `𝓞 F` splits completely in `maxElemAbUnram3 F` if and only if it splits completely
in **every** finite everywhere-unramified elementary abelian `3`-extension of `F`.

* The forward direction is descent along the inclusion `E ≤ maxElemAbUnram3 F`
  (`Work.Tower.le_maxElemAbUnram3`), via
  `Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom`.
* The backward direction applies the universal hypothesis to `maxElemAbUnram3 F` itself,
  which is a finite everywhere-unramified elementary abelian `3`-extension of `F` by
  `maxElemAbUnram3_isUnramified` and `maxElemAbUnram3_isElementaryAbelianThreeExtension`.
-/

open NumberField

namespace Work.Tower.Unramified

theorem splitsCompletelyIn_maxElemAbUnram3_iff (F : Type*) [Field F] [NumberField F]
    (hfin : FiniteDimensional F ↥(Work.Tower.maxElemAbUnram3 F))
    (𝔭 : Ideal (NumberField.RingOfIntegers F)) :
    Work.Tower.SplitsCompletelyIn F ↥(Work.Tower.maxElemAbUnram3 F) 𝔭 ↔
      ∀ (E : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F E],
        Work.Tower.IsUnramifiedExtension F E → Work.Tower.IsElementaryAbelianThreeExtension F E →
        Work.Tower.SplitsCompletelyIn F ↥E 𝔭 := by
  haveI := hfin
  haveI : NumberField ↥(Work.Tower.maxElemAbUnram3 F) :=
    NumberField.of_module_finite F ↥(Work.Tower.maxElemAbUnram3 F)
  constructor
  · intro h E _hE hunram helem
    haveI : NumberField ↥E := NumberField.of_module_finite F ↥E
    exact FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭
      (IntermediateField.inclusion (Work.Tower.le_maxElemAbUnram3 hunram helem)) h
  · intro h
    exact h (Work.Tower.maxElemAbUnram3 F)
      (maxElemAbUnram3_isUnramified F hfin)
      (maxElemAbUnram3_isElementaryAbelianThreeExtension F hfin)

end Work.Tower.Unramified
