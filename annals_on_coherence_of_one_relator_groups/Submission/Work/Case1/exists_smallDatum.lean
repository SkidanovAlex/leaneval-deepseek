/-
# The datum of the small model exists

This file assembles the properties of the transported datum of `Submission/Work/Case1/SmallDatum.lean`
into the statement that the datum of a presentation transfers to a *faithful small model*: a
presentation and a datum on a graph whose vertices and arrows are indexed by `Fin`'s, with the same
words, the same measure, using every arrow and every relator, connected, and such that the vanishing
of the transported datum implies the vanishing of the original one.

The individual properties are proved in the companion files
`Submission/Work/Case1/smallDatum_measure.lean` (the measure) and
`Submission/Work/Case1/smallDatum_used.lean` (every arrow and relator is used).
-/
import Mathlib
import Submission.Work.Case1.SmallDatum
import Submission.Work.Case1.smallDatum_measure
import Submission.Work.Case1.smallDatum_usesEverything
import Submission.Work.Case1.SmallTransfer

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

namespace SmallDatum

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u}

/-- **The datum of the small model exists.**  A datum in a presentation over `V` has a faithful
combinatorial copy over the small graph `S.Vx` of a skeleton `S` (which is a type in the universe
of `S`), with the same words, the same measure, using every arrow and every relator of the small
presentation, and such that the vanishing of the transported datum implies that of the original. -/
theorem exists_smallDatum (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i)
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList)
    (hconn : ∀ x : V, Nonempty (Quiver.Path v x)) :
    ∃ D' : Datum (SmallPres.smallPresentation S P D hrel) (S.encObj v) n,
      D'.W = D.W ∧ D'.measure = D.measure ∧
      (∀ e : Quiver.Total S.Vx, e ∈ D'.usedArrowsList) ∧
      (∀ i : (SmallPres.smallPresentation S P D hrel).ι, UsedRelator D' i) ∧
      (∀ x : S.Vx, Nonempty (Quiver.Path (S.encObj v) x)) ∧
      (∀ j, SmallTransfer.decode S v (D'.γ j) = D.γ j) := by
  have hmeas := smallDatum_measure S P D hrel
  have hused := smallDatum_usesEverything S P D hrel hpair
  refine ⟨smallDatum S P D hrel, rfl, ?_, hused.1, hused.2, SmallDatum.smallDatum_reachable S hconn,
    fun j => SmallDatum.smallDatum_decode_gamma S P D hrel j⟩
  rw [Datum.measure, Datum.measure, hmeas.1, hmeas.2]

end SmallDatum

end Work.Case1
