import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.LengthInBall.arclengthIn_le_of_diam

/-!
# The length bound for balls (Deliverable 1)

This file states the headline consequence of
`Submission.Work.Sweep.LengthInBall.arclengthIn_le_of_diam`: the arclength of the
part of a knot inside a ball of radius `R` is at most `2 d` times its diameter,
i.e. at most `4 d R`, where `d` is any distortion bound for the knot.

We also record the translation between the half-open parameter interval `[0, 2π)`
(used by the distortion hypothesis and by `paramSetInIco`) and the closed interval
`[0, 2π]` (used by the coarea formula), which differ by a single parameter and
hence by a set of arclength zero.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- The arclength over a subset is monotone in the subset. -/
lemma arclengthIn_mono (K : Knot) {E F : Set ℝ} (h : E ⊆ F) :
    arclengthIn K E ≤ arclengthIn K F :=
  lintegral_mono_set h

/-- The arclength over a single parameter is zero. -/
lemma arclengthIn_singleton (K : Knot) (c : ℝ) : arclengthIn K {c} = 0 := by
  rw [arclengthIn]
  refine setLIntegral_measure_zero _ _ ?_
  rw [show ({c} : Set ℝ) = {c} from rfl]
  simp

/-- The two fundamental parameter sets `[0, 2π)` and `[0, 2π]` have the same
arclength: they differ by the single parameter `2π`. -/
lemma arclengthIn_paramSetInIco_eq_paramSetIn (K : Knot) (B : Set R3) :
    arclengthIn K (paramSetInIco K B) = arclengthIn K (paramSetIn K B) := by
  refine le_antisymm (arclengthIn_mono K ?_) ?_
  · exact Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self
  · have hsub : paramSetIn K B ⊆ paramSetInIco K B ∪ {2 * Real.pi} := by
      rintro t ⟨htB, htIcc⟩
      rcases eq_or_lt_of_le htIcc.2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨htB, ⟨htIcc.1, h⟩⟩
    calc arclengthIn K (paramSetIn K B)
        ≤ arclengthIn K (paramSetInIco K B ∪ {2 * Real.pi}) := arclengthIn_mono K hsub
      _ ≤ arclengthIn K (paramSetInIco K B) + arclengthIn K {2 * Real.pi} :=
          lintegral_union_le _ _ _
      _ = arclengthIn K (paramSetInIco K B) := by rw [arclengthIn_singleton, add_zero]

/-- **Length of the part of a knot in a set of diameter `D`.**

Version of `LengthInBall.arclengthIn_le_of_diam` for the closed fundamental
interval `[0, 2π]`, which is the form consumed by the coarea estimates. -/
theorem arclengthIn_paramSetIn_le_of_diam {K : Knot} {d D : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) {B : Set R3} (hBmeas : MeasurableSet B)
    (hD : ∀ y ∈ B, ∀ z ∈ B, dist y z ≤ D)
    (hne : (K.curve '' Set.Ico (0 : ℝ) (2 * Real.pi) ∩ B).Nonempty) :
    arclengthIn K (paramSetIn K B) ≤ ENNReal.ofReal (2 * d * D) := by
  rw [← arclengthIn_paramSetInIco_eq_paramSetIn]
  exact LengthInBall.arclengthIn_le_of_diam hd hbound hBmeas hD hne

/-- **Deliverable 1: the arclength of the part of the knot inside a ball.**

If `d` is a distortion bound for `K`, then the arclength of the portion of `K`
inside the closed ball of radius `R` about any point `x` is at most
`4 * d * R` (twice `d` times the diameter `2R` of the ball). -/
theorem arclengthIn_closedBall_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} :
    arclengthIn K (paramSetIn K (Metric.closedBall x R)) ≤ ENNReal.ofReal (4 * d * R) := by
  by_cases hne : (K.curve '' Set.Ico (0 : ℝ) (2 * Real.pi) ∩ Metric.closedBall x R).Nonempty
  · have hdiam : ∀ y ∈ Metric.closedBall x R, ∀ z ∈ Metric.closedBall x R, dist y z ≤ 2 * R := by
      intro y hy z hz
      rw [Metric.mem_closedBall] at hy hz
      calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
        _ ≤ 2 * R := by linarith [hy, hz, dist_comm x z]
    have h := arclengthIn_paramSetIn_le_of_diam hd hbound measurableSet_closedBall hdiam hne
    have : 2 * d * (2 * R) = 4 * d * R := by ring
    rwa [this] at h
  · have hsub : paramSetIn K (Metric.closedBall x R) ⊆ {2 * Real.pi} := by
      rintro t ⟨htB, htIcc⟩
      by_contra ht
      have htlt : t < 2 * Real.pi := lt_of_le_of_ne htIcc.2 (by simpa [eq_comm] using ht)
      exact hne ⟨K.curve t, ⟨t, ⟨htIcc.1, htlt⟩, rfl⟩, htB⟩
    calc arclengthIn K (paramSetIn K (Metric.closedBall x R))
        ≤ arclengthIn K {2 * Real.pi} := arclengthIn_mono K hsub
      _ ≤ ENNReal.ofReal (4 * d * R) := by rw [arclengthIn_singleton]; exact bot_le

/-- **Deliverable 1, open ball form.**  The same bound holds for the open ball,
which is contained in the closed ball. -/
theorem arclengthIn_ball_le {K : Knot} {d : ℝ} (hd : 0 ≤ d) (hbound : IsDistortionBound K d)
    (x : R3) {R : ℝ} :
    arclengthIn K (paramSetIn K (Metric.ball x R)) ≤ ENNReal.ofReal (4 * d * R) :=
  (arclengthIn_mono K fun t ht => show t ∈ paramSetIn K (Metric.closedBall x R) from
    ⟨Metric.ball_subset_closedBall ht.1, ht.2⟩).trans
    (arclengthIn_closedBall_le hd hbound x)

/-- **Deliverable 1, real-valued form.**  The arclength of the part of the knot
inside the ball is at most `4 d R` as a real number. -/
theorem arclengthIn_ball_toReal_le {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (hbound : IsDistortionBound K d) (x : R3) {R : ℝ} (hR : 0 ≤ R) :
    (arclengthIn K (paramSetIn K (Metric.ball x R))).toReal ≤ 4 * d * R := by
  have h := arclengthIn_ball_le hd hbound x (R := R)
  have hfin : arclengthIn K (paramSetIn K (Metric.ball x R)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  rw [← ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 4 * d * R)]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end Work.Sweep
