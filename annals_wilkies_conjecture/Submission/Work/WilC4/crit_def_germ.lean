import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.monoDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.critAux
import Submission.Work.WilC4.paramDom_definable
import Submission.Work.WilC4.pmGerms_definable
import Submission.Work.WilC4.pmLAHA_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- The eight parametric loci attached to a `∅`-definable family `Y ⊆ ℝ^{k+2}` are all
`∅`-definable.

The sets `PMonoDom`, `PMonoW`, … are, by definition (`CritDefs.lean`), the fibres of the
corresponding `Mono*` loci of `Cfib Y (·)`, and `Cfib Y c = Pfibre Y c` definitionally, so the
statements about `PDom`, `PW`, `PLm`, …, `PHp` (`ParamMonoDefs.lean`) transfer verbatim.  For the
two loci of pairs `MonoLA`, `MonoHA` there is no `ParamMonoDefs` analogue; they are handled
directly in `pmLAHA_definable`.

* `PMonoDom = PDom` : projection of the extended relation `PExt Y` along the value coordinate.
* `PMonoW = PW`, `PMonoLm = PLm`, …, `PMonoHp = PHp` : first-order formulas over `Y` with real
  quantifiers; see `critAux.lean` (`PS`/`pw_definable`) for the reindexing-and-quantifier
  bookkeeping.
* `PMonoLA`, `PMonoHA` : two pullbacks of `Y` under reindexings intersected with the comparison of
  the two value coordinates, then existentially quantified. -/
theorem crit_def_germ {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoDom Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoW Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHm Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLp Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHp Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLA Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHA Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact paramDom_definable hY
  · exact pw_definable hY
  · exact (pmGerms_definable hY).1
  · exact (pmGerms_definable hY).2.1
  · exact (pmGerms_definable hY).2.2.1
  · exact (pmGerms_definable hY).2.2.2
  · exact (pmLAHA_definable hY).1
  · exact (pmLAHA_definable hY).2

end Work.WilC4
