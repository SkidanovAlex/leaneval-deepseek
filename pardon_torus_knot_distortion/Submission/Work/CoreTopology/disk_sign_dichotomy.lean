import Mathlib

namespace Work.CoreTopology

/-- **Sign dichotomy on the disc.**  A continuous real-valued function on the closed unit disc
which never takes the value `1` on the open unit disc is either everywhere `> 1` or everywhere
`< 1` on the open disc. -/
theorem disk_sign_dichotomy (H : Metric.closedBall (0 : ℂ) 1 → ℝ) (hH : Continuous H)
    (hne : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → H z ≠ 1) :
    (∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → 1 < H z) ∨
      (∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → H z < 1) := by
  -- The open unit disc is convex, hence (pre)connected.
  have hpre : PreconnectedSpace (Metric.ball (0 : ℂ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : ℂ) 1).isPreconnected
  -- The norm of a point of the open ball is `< 1`.
  have hnorm : ∀ w : Metric.ball (0 : ℂ) 1, ‖((w : ℂ))‖ < 1 := by
    intro w
    have h := Metric.mem_ball.mp w.2
    rwa [dist_eq_norm, sub_zero] at h
  -- Inclusion of the open ball into the closed ball.
  let inc : Metric.ball (0 : ℂ) 1 → Metric.closedBall (0 : ℂ) 1 :=
    fun w => ⟨(w : ℂ), Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp w.2))⟩
  have hinc : Continuous inc :=
    continuous_subtype_val.subtype_mk _
  have hg : Continuous fun w : Metric.ball (0 : ℂ) 1 => H (inc w) := hH.comp hinc
  have hne' : ∀ w : Metric.ball (0 : ℂ) 1, H (inc w) ≠ 1 := by
    intro w h
    exact hne (inc w) (by simpa [inc] using hnorm w) h
  have hAopen : IsOpen {w : Metric.ball (0 : ℂ) 1 | 1 < H (inc w)} :=
    isOpen_Ioi.preimage hg
  have hBopen : IsOpen {w : Metric.ball (0 : ℂ) 1 | H (inc w) < 1} :=
    isOpen_Iio.preimage hg
  have hdisj : Disjoint {w : Metric.ball (0 : ℂ) 1 | 1 < H (inc w)}
      {w : Metric.ball (0 : ℂ) 1 | H (inc w) < 1} := by
    rw [Set.disjoint_left]
    intro w h1
    rw [Set.mem_ofPred_eq] at h1 ⊢
    exact not_lt.mpr (le_of_lt h1)
  have hcover : (Set.univ : Set (Metric.ball (0 : ℂ) 1)) ⊆
      {w : Metric.ball (0 : ℂ) 1 | 1 < H (inc w)} ∪
        {w : Metric.ball (0 : ℂ) 1 | H (inc w) < 1} := by
    intro w _
    rcases lt_or_gt_of_ne (hne' w) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hsub := IsPreconnected.subset_or_subset hAopen hBopen hdisj hcover
    (isPreconnected_univ : IsPreconnected (Set.univ : Set (Metric.ball (0 : ℂ) 1)))
  rcases hsub with hA | hB
  · left
    intro z hz
    have hzb : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hz
    let w : Metric.ball (0 : ℂ) 1 := ⟨(z : ℂ), hzb⟩
    have hw : 1 < H (inc w) := hA (Set.mem_univ w)
    have hincw : inc w = z := Subtype.ext rfl
    rwa [hincw] at hw
  · right
    intro z hz
    have hzb : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hz
    let w : Metric.ball (0 : ℂ) 1 := ⟨(z : ℂ), hzb⟩
    have hw : H (inc w) < 1 := hB (Set.mem_univ w)
    have hincw : inc w = z := Subtype.ext rfl
    rwa [hincw] at hw

end Work.CoreTopology
