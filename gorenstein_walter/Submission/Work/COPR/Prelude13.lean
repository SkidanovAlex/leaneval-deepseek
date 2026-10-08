/-
Shared import prelude for area COPR, deliverable 1.3 (`Work.GW2.Coprime13Prop`).

It merely collects the two library modules that the 1.3 development needs:

* `Submission.Work.COPR.Glue` — the conjugation-action bridges
  (`conjAct`, `coprime_card_of_isPGroup`, `isSolvable_of_isPGroup`, …);
* `Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03` — Isaacs Cor. 3.28 in the
  coprime-normal form `coprime_fixedPoints_quotient_of_coprime_normal`.

Nothing is proved here.
-/
import Submission.Work.COPR.Glue
import Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
