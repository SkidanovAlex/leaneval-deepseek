import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Disk
import Submission.Work.Smooth.Plane.All
import Submission.Work.BoxShrink.PinchOff.IB.Main

namespace Work.BoxShrink.PinchOff

/-- The winding span of a region of the torus whose boundary consists of pairwise disjoint simple
inessential closed curves, split into two open pieces, is `⊥` or `⊤`. -/
theorem windingSpan_bot_or_top_of_inessential_boundary {P : Work.CoreTopology.ParamTorus} {X Y : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {n : ℕ} {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hY : Work.SurgeryInvariance.IsOpenInCarrier P Y)
    (hXY : Disjoint X Y)
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = X ∪ Y) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ∨ Work.SurgeryInvariance.WindingSpan P X = ⊤ :=
  windingSpan_bot_or_top_aux hsimple hess hdisj hX hY hXY hcover

end Work.BoxShrink.PinchOff
