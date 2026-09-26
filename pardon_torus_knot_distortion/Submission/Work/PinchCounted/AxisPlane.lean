import Submission.Work.PinchCounted.TraceCover
import Submission.Work.PinchCounted.exists_traceCircleFamily_z

/-!
# The slice inessentiality at a plane normal to the axis of the standard torus

`TraceCover.lean` shows that the slice inessentiality follows from the plane count as soon as the
trace of the cutting plane is covered by pairwise disjoint simple closed curves each of which is
inessential or meets the knot in at least `min p q = I(F,β)` points.  This module supplies that
covering hypothesis in one concrete configuration: the **standard torus of revolution** with the
cutting plane **normal to its axis**, `{z = c 2 + u}`.  There the trace is one or two *longitude*
circles (`exists_traceCircleFamily_z`), which are simple, pairwise disjoint, essential, and meet the
standard `(p,q)`-curve in `q ≥ min p q` points
(`Work.CoreTopology.encard_longitude_inter_standardCurve`).

Consequently, at such a plane, **the slice inessentiality needs no planar innermost input**: it is a
consequence of the count alone.  This is the concrete instance of the mechanism that distinguishes
the counted form of Pardon's Lemma 3 (`Work.BoxShrink.Pinch.CountingHalf`) from the abstract
`Work.BoxShrink.Pinch.SmoothHalfS` — the latter has to carry the planar input, the former does not.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-- **The slice is inessential at a plane normal to the axis of the standard torus**, from the plane
count alone: the trace of the plane is a union of longitude circles, and the intersection bound
`Work.CoreTopology.encard_longitude_inter_standardCurve` makes each of them meet the knot in at least
`min p q` points. -/
theorem not_containsEssentialLoop_sliceRegion_standard_axisPlane
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range (Work.CoreTopology.standardCurve p q).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {c : R3} {σ : Equiv.Perm (Fin 3)} (hσ : σ 2 = 2) {s u : ℝ}
    (hcount : (↑(Work.BoxShrink.planeCount K c σ s u) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion Work.CoreTopology.standard s c σ u) := by
  obtain ⟨ι, hι, C, hdisj, hsimple, hdich, hcover⟩ :=
    exists_traceCircleFamily_z p q hp hq hc (c 2 + u)
  refine not_containsEssentialLoop_sliceRegion_of_traceCircles
    (Work.CoreTopology.standardCurve p q) p q hp hq
    (le_of_eq (Work.CoreTopology.pardonsI_standard p q hp hq hc).symm)
    K hd himg hsmall hcount C hdisj hsimple ?_ hdich
  intro y hy
  obtain ⟨hmem, hplane⟩ := Work.BoxShrink.Pinch.mem_planeTrace.mp hy
  refine hcover ⟨?_, hmem⟩
  rw [hσ] at hplane
  exact hplane

end

end Work.PinchCounted
