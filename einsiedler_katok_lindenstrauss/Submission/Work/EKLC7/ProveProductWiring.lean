import Mathlib
import Submission.Work.EKLC7.LeafwiseComponentFull
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLComp.prove_Birkhoff
import Submission.Work.EKLComp.prove_Product

/-!
# `P_Product`, wired against the proved C5 assembly

`Work.EKLComp.prove_Product_aux : P_X3 → P_Leafwise → P_Birkhoff → P_Product` is the refreed
component statement of C5b (Pisa Prop. 8.5 / Cor. 8.8); `Submission/Work/EKLComp/prove_Product.lean`
wires the frozen `prove_Product` as `prove_Product_aux prove_X3 prove_Leafwise prove_Birkhoff`,
which needs the component file `Work.EKLComp.prove_Leafwise` (still a stub).

Since C5 is proved here (`Work.EKLC7.P_Leafwise_proved : P_X3 → P_Leafwise`, axiom-clean) and both
`prove_X3` and `prove_Birkhoff` are sorry-free, the only missing input of C5b is its own
mathematical content: once `prove_Product_aux` is sorry-free,

  `Work.EKLC7.prove_Product_c7 : P_Product`

is the frozen C5b component, without any dependence on the stubbed `prove_Leafwise` /
`prove_Product` wiring.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

/-- **C5b**, from its component statement and the proved C5 assembly. -/
theorem prove_Product_of (hB : P_Birkhoff) : P_Product :=
  Work.EKLComp.prove_Product_aux Work.EKLComp.prove_X3
    (Work.EKLC7.P_Leafwise_proved Work.EKLComp.prove_X3) hB

/-- **C5b (frozen)**, using `prove_Birkhoff`. -/
theorem prove_Product_c7 : P_Product := prove_Product_of Work.EKLComp.prove_Birkhoff

end Work.EKLC7
