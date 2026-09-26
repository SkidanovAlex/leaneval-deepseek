import Submission.Work.SurgeryInvariance.Core
import Submission.Work.CoreTopology.EssentialLoop
import Submission.Work.CoreTopology.WindingSpanLink

/-!
# Pardon's `spherefamily` and `doublebubble` for the standard torus

The results of `Work.SurgeryInvariance.Core` are stated for an arbitrary parametrised torus `P`.
This file specialises them to `P = Work.CoreTopology.standard` and phrases them with the predicate
`Work.CoreTopology.ContainsEssentialLoop` of the sibling subproject, so that they can be used
directly alongside `Work.CoreTopology.sphere_family` and `Work.CoreTopology.double_bubble`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance.Standard

noncomputable section

/-- **Pardon's `spherefamily` for the standard torus.**  If `F ∩ int(S_0)` contains an essential
loop then so does `F ∩ int(S_1)`. -/
theorem spherefamily (S : Sweep Work.CoreTopology.standard)
    (h : Work.CoreTopology.ContainsEssentialLoop (S.region 0)) :
    Work.CoreTopology.ContainsEssentialLoop (S.region 1) :=
  Work.SurgeryInvariance.Sweep.spherefamily S h

/-- The essential-piece invariant is constant along the whole sweep. -/
theorem containsEssentialLoop_iff (S : Sweep Work.CoreTopology.standard) (t : ℝ) :
    Work.CoreTopology.ContainsEssentialLoop (S.region t) ↔
      Work.CoreTopology.ContainsEssentialLoop (S.region 0) :=
  Work.SurgeryInvariance.Sweep.containsEssentialLoop_iff S t

/-- **Pardon's `doublebubble` for the standard torus.** -/
theorem double_bubble_persistence {A H₁ H₂ : Set R3}
    {D : DiscRegion Work.CoreTopology.standard}
    (hopen₁ : IsOpenInCarrier Work.CoreTopology.standard H₁)
    (hopen₂ : IsOpenInCarrier Work.CoreTopology.standard H₂) (hdisj : Disjoint H₁ H₂)
    (hdisjZ : Disjoint (H₁ ∪ H₂) D.interior)
    (hcover : A = (H₁ ∪ H₂) ∪ D.interior)
    (h0 : Work.CoreTopology.ContainsEssentialLoop A) :
    Work.CoreTopology.ContainsEssentialLoop H₁ ∨ Work.CoreTopology.ContainsEssentialLoop H₂ :=
  Work.SurgeryInvariance.double_bubble_persistence hopen₁ hopen₂ hdisj hdisjZ hcover h0

end

end Work.SurgeryInvariance.Standard
