import Submission.Work.Topology.Classical.Defs

/-!
# The cut-and-paste from its two classical ingredients

`Work.Topology.Classical.PushThroughInnermost` is the output of Pardon's cut-and-paste.  This file
shows that it is the conjunction of the two more primitive classical inputs into which the
argument decomposes:

* `Work.Topology.Classical.InnermostCurveExists` — *innermost in the surface*: among the finitely
  many pairwise disjoint intersection curves of a slice disc there is one bounding a sub-disc
  whose interior misses `F` and which no other curve meets (Jordan separation inside the disc);
* `Work.Topology.Classical.CutsAlongSubdisc` — the surgery: given such an innermost sub-disc,
  eliminate exactly that intersection curve (Alexander's theorem plus isotopy extension).

So a caller who wants to work with the primitive classical facts can use
`classicalTopology_of_decomposed` and everything else in the chapter unchanged. -/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **The cut-and-paste from its two classical ingredients.** -/
theorem pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc
    {P : ParamTorus}
    (h1 : InnermostCurveExists P) (h2 : CutsAlongSubdisc P) :
    PushThroughInnermost P := by
  intro D hD
  obtain ⟨j, f, hfinj, hfbd, hfint, hfsub, hfdisj⟩ := h1 D hD
  obtain ⟨e', he'inj, he'bd, he'sub, he'cov⟩ := h2 D j f hfinj hfbd hfint hfsub hfdisj
  exact ⟨j, e', he'inj, he'bd, he'sub, he'cov⟩

/-- **The packaged classical input, from the primitive classical facts**: Jordan–Schoenflies on the
round sphere, the existence of an innermost intersection curve (Jordan separation in the disc), and
the surgery along the sub-disc it bounds (Alexander's theorem plus isotopy extension). -/
theorem classicalTopology_of_decomposed (h₁ : JordanSchoenfliesSphere)
    (h₂ : InnermostCurveExists standard) (h₃ : CutsAlongSubdisc standard) :
    ClassicalTopology :=
  ⟨h₁, pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc h₂ h₃⟩

end

end Work.Topology.Classical
