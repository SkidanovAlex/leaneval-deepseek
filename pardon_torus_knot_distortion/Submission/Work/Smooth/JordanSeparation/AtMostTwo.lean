import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.exists_transverse_lipschitz_field
import Submission.Work.Smooth.JordanSeparation.offset_injective
import Submission.Work.Smooth.JordanSeparation.atMostTwo_connectedComponentIn_of_offset

/-!
# At most two components: the complement of a simple immersed closed curve is sliced by a product
neighbourhood

Combining the existence of a Lipschitz transverse unit field (`exists_transverse_lipschitz_field`),
the injectivity of its offset map on a strip (`offset_injective`) and the resulting slicing of the
complement into the two sides of the offset annulus
(`atMostTwo_connectedComponentIn_of_offset`), we obtain the **at most two components** half of the
Jordan curve theorem:

* `atMostTwo_connectedComponentIn` — of any three points off a simple immersed closed curve, two
  lie in the same connected component of the complement of its trace.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **At most two components.**  For a `C¹` immersed *simple* closed plane curve, of any three
points off the curve two lie in the same connected component of the complement of its trace. -/
theorem atMostTwo_connectedComponentIn (c : SmoothPlaneCurve) (himm : c.IsImmersion)
    (hs : c.toPlaneCurve.IsSimple) {x y z : ℂ} (hx : x ∉ c.trace) (hy : y ∉ c.trace)
    (hz : z ∉ c.trace) :
    connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z := by
  obtain ⟨v, κ, L, hκ, hL, hper, hcont, htrans, hlip⟩ :=
    exists_transverse_lipschitz_field c himm
  obtain ⟨δ, hδ, hinj⟩ := offset_injective c himm hs hκ hL hper htrans hlip
  exact atMostTwo_connectedComponentIn_of_offset c hcont.continuous hδ hper
    (trace_subset_annulus c v hδ)
    (fun t t' u u' hu hu' heq => (hinj t t' u u' hu hu' heq).1) hx hy hz

end

end Work.Smooth.JordanSeparation
