import Submission.Work.OddEnvelope.Profile
import Submission.Work.OddEnvelope.NonDegenerate.sq_gt_sq_of_concaveOn_of_ends

/-!
# Non-degeneracy of the profile

For every slope `s > 0` the line `t ↦ s t + h s` meets the boundary of the planar section
`{(t,z) : |z| ≤ f t}` exactly at `t = -(x s)` (below) and `t = y s` (above), and lies strictly
inside the section in between.  This is the *non-degeneracy* condition that makes the cap
integrals non-vacuous: it says that the radicand `f t ^ 2 - (s t + h s) ^ 2` is strictly positive
on `(-(x s), y s)`.

It is a formal consequence of concavity and the two root conditions: the functions
`f ± (s t + h s)` are concave, vanish at the appropriate end and are positive at the other end,
so the concavity chord bound makes them positive throughout the interval.
-/

namespace Work.OddEnvelope

noncomputable section

open Set Filter
open scoped Topology ContDiff

variable {h x y : ℝ → ℝ}

/-- **Non-degeneracy of the envelope profile.**  For every `s > 0` and every `t` strictly between
the two intersection points, the profile is strictly above the cutting line in absolute value. -/
theorem envelopeProfile_sq_gt_sq (H : IsEnvelopeCurve h x y)
    (hf : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (envelopeProfile h x y)) {s : ℝ} (hs : 0 < s) :
    ∀ t ∈ Set.Ioo (-(x s)) (y s),
      (s * t + h s) ^ 2 < (envelopeProfile h x y t) ^ 2 := by
  have hx1 : x s < 1 := H.toChordCurve_x.lt_one hs
  have hx0 : 0 < x s := H.toChordCurve_x.pos hs
  have hy1 : y s < 1 := H.toChordCurve_y.lt_one hs
  have hy0 : 0 < y s := H.toChordCurve_y.pos hs
  have hab : -(x s) < y s := by linarith
  have hsub : Set.Icc (-(x s)) (y s) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro u hu
    exact ⟨by linarith [hu.1, hx1], by linarith [hu.2, hy1]⟩
  have hconc : ConcaveOn ℝ (Set.Icc (-(x s)) (y s)) (envelopeProfile h x y) :=
    hf.subset hsub (convex_Icc _ _)
  have hroot_a : envelopeProfile h x y (-(x s)) = -(s * (-(x s)) + h s) :=
    envelopeProfile_root_left H hs
  have hroot_b : envelopeProfile h x y (y s) = s * y s + h s :=
    envelopeProfile_root_right H hs
  have hmem := envelopeProfile_mem_Ioo H hs
  refine Work.OddEnvelope.NonDegenerate.sq_gt_sq_of_concaveOn_of_ends hab hconc
    hroot_a hroot_b ?_ ?_
  · have hpa : 0 < envelopeProfile h x y (-(x s)) := envelopeProfile_pos H hmem.1
    linarith [hroot_a, hpa]
  · have hpb : 0 < envelopeProfile h x y (y s) := envelopeProfile_pos H hmem.2
    linarith [hroot_b, hpb]

/-- The non-degeneracy condition in the form `f t ^ 2 - (s t + h s) ^ 2 > 0`. -/
theorem envelopeProfile_sub_sq_pos (H : IsEnvelopeCurve h x y)
    (hf : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (envelopeProfile h x y)) {s : ℝ} (hs : 0 < s) :
    ∀ t ∈ Set.Ioo (-(x s)) (y s),
      0 < (envelopeProfile h x y t) ^ 2 - (s * t + h s) ^ 2 := by
  intro t ht
  linarith [envelopeProfile_sq_gt_sq H hf hs t ht]

end

end Work.OddEnvelope
