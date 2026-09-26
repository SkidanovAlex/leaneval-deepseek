import Mathlib
import Submission.Work.Smooth.Plane.Defs
import Submission.Work.BoxShrink.counting
import Submission.Work.BoxBubble.mustbeinessentialBox
import Submission.Work.CoreTopology.All

namespace Work.Smooth.Plane

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The counting step of the planar slice.**

Let `ψ` be a diffeomorphism of `ℝ³`, `F = ψ(F_standard)` the image torus
(`Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph`), `β` the image of the standard
`(p,q)`-curve on it, so that `I(F,β) = min p q`
(`Work.CoreTopology.pardonsI_standard_mapHomeomorph`), and let `K` be a knot whose image is the
image of `β` (`himg`).  Let `D = Work.Smooth.Plane.PardonSlice s c σ u` be the slice of Pardon's
box `PBox s c σ` by the cutting plane `{y | y (σ 2) = c (σ 2) + u}`, and assume that the number of
*parameters* in the fundamental period `[0, 2π)` at which the knot meets that slice is at most
`5(1+ε)/ε·d` (`hcount`) with `countConst·d = 150·d < min p q` (`hsmall`).

Then the slice `D` meets `β` in fewer than `I(F,β) = min p q` points.

This is the planar analogue of the counting step of `Work.BoxBubble.mustbeinessentialBox`: the
number of intersection *points* of `β` with `D` is at most the number of intersection *parameters*
(`Work.BoxBubble.encard_range_inter_le_param`, applied to `β` viewed as the knot curve via `himg`),
which is at most `5(1+ε)/ε·d = 37.5·d < 150·d < min p q` by `hsmall` and `five_const`, using
`ENNReal.ofReal_lt_natCast` and `Work.CoreTopology.pardonsI_standard_mapHomeomorph`. -/
theorem encard_pardonSlice_inter_lt_pardonsI (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩
        Work.Smooth.Plane.PardonSlice s c σ u)
      < Work.CoreTopology.pardonsI (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)) := by
  classical
  -- The knot `K`, regarded as a closed curve of the image torus: it lies on the image torus
  -- because its image is the image of the image of the standard `(p,q)`-curve.
  let γK : Work.CoreTopology.ClosedCurve
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) :=
    { γ := K.curve
      cont := K.smooth.continuous
      periodic := K.periodic
      mem := fun t => by
        have ht : K.curve t ∈ Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph
            ψ.toHomeomorph (Work.CoreTopology.standardCurve p q)).γ := by
          rw [← himg]
          exact Set.mem_range_self t
        obtain ⟨u, hu⟩ := ht
        rw [← hu]
        exact (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
          (Work.CoreTopology.standardCurve p q)).mem u }
  -- The parameter bound on the plane count, in the form consumed by `planeCount_lt`.
  have hcount' : (Work.BoxShrink.planeCount K c σ s u : ENNReal) ≤
      ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d) := by
    simpa only [Work.BoxShrink.planeCount] using hcount
  have hlt : Work.BoxShrink.planeCount K c σ s u < (Nat.min p q : ℕ∞) :=
    Work.BoxShrink.planeCount_lt (p := p) (q := q) (lt_min hp hq) hd hsmall hcount'
  -- The counting step: points `≤` parameters, and the parameters are the plane count.
  have hle : Set.encard (Set.range K.curve ∩ PardonSlice s c σ u) ≤
      Work.BoxShrink.planeCount K c σ s u := by
    have h := Work.BoxBubble.encard_range_inter_le_param γK (PardonSlice s c σ u)
    change Set.encard (Set.range K.curve ∩ PardonSlice s c σ u) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ PardonSlice s c σ u} at h
    rw [Work.BoxShrink.planeCount]
    refine le_trans h ?_
    apply le_of_eq
    congr 1
  -- `I(F,β) = min p q`.
  rw [Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph, ← himg]
  exact lt_of_le_of_lt hle hlt

end Work.Smooth.Plane
