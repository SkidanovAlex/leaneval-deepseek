import Submission.Work.ThomBordism.concreteLastMileConnBase
import Submission.Work.PTGeometric.SourceWiring
import Submission.Work.PTGeometric.OrientationFree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the last mile in the CONNECTED-FAMILY form — the producer-facing half

`Submission/Work/ThomBordism/NOTE_SESSION64.md` sections 8-14.  This module connects the
connected-family orientation producer `Work.PTGeometric.OrientationProducerConn` to the
connected-family last mile `Work.ThomBordism.ConcreteLastMileConn`; the `SourceWiring`-free base of the
chain (and the consumer `Work.ThomBordism.transversalityCoreFamilyConn_of_concreteLastMileConn`) is in
`Submission/Work/ThomBordism/concreteLastMileConnBase.lean`.

## Main results

* `Work.ThomBordism.nullBordismFamily_of_orientationProducerConn`;
* `Work.ThomBordism.ConcreteLastMileConn.of_orientationProducerConn`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism

open Work.PTGeometric

noncomputable section

/-- **The fixed-family null bordism from the connected-family orientation producer.** -/
theorem nullBordismFamily_of_orientationProducerConn {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Man8} [T2Space D.T]
    (hO : OrientationProducerConn) (hk : 11 ≤ k) (hne : ∀ i, Nonempty (Fam i).pt)
    (hconn : ∀ i, ConnectedSpace (Fam i).pt) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hm : 0 < m) (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) :
    Nonempty (NullBordismFamily (Fin m × ι) (fun a => Fam a.2)) :=
  exists_nullBordismFamily_of_ambientOrientationDataFree
    (hO k D ι Fam hk hne hconn G m hm hpow)

/-- **`ConcreteLastMileConn` from the connected-family orientation producer.** -/
theorem ConcreteLastMileConn.of_orientationProducerConn {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} [T2Space D.T]
    (hO : OrientationProducerConn) (hk : 11 ≤ k) : ConcreteLastMileConn k D := by
  intro ι _ Fam hconn G m hm hpow
  exact ⟨m, hm, nullBordismFamily_of_orientationProducerConn (D := D) (Fam := Fam) hO hk
    (fun i => by haveI := hconn i; exact inferInstance) hconn G m hm hpow⟩

end

end Work.ThomBordism
