import Mathlib
import Submission.Work.EKLC7.CommutatorStepRaw
import Submission.Work.EKLC7.RootPropsC7
import Submission.Work.EKLC7.PeriodSmallIter

/-!
# C7 from the existence half of C5

`Work.EKLC7.commutator_step_raw` needs only the *existence* half of the frozen component C5
(`Work.EKLC7.P_LeafwiseEx`), the clauses (U3)–(U8) for the one-dimensional root groups
(`Work.EKLC7.P_RootProps`, proved as `Work.EKLC7.RootPropsC7`), the product structure
(`P_Product`) and `Work.EKLC7.PeriodSmallIter`.  This file performs that instantiation, leaving
exactly `P_LeafwiseEx` and `P_Product` as hypotheses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

namespace Work.EKLC7

/-- **C7 from the existence half of C5 and the product structure.** -/
theorem commutator_of_existence (hEx : P_LeafwiseEx) (hProd : P_Product) :
    P_Commutator :=
  commutator_step_raw hEx RootPropsC7 hProd
    (fun {i j k} hij hjk hik νij νjk νik c h1 h2 h3 h4 hsmall hnonzero =>
      PeriodSmallIter hij hjk hik νij νjk νik c h1 h2 h3 h4 hsmall hnonzero)

end Work.EKLC7
