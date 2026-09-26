import Mathlib
import Submission.Work.Radial.Basic

namespace Work.Radial

open scoped ContDiff in
theorem gaussian_profile_schwartz (n : ℕ) [NeZero n] (y : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) :
    ∃ F : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ∀ x, F x = Work.Radial.gaussianTimesProfile y h x := by
  -- The function `gaussianTimesProfile y h` is smooth and compactly supported:
  -- smoothness comes from the smoothness of `h` and of `x ↦ ‖x‖ ^ 2`, and the
  -- support is contained in the ball of radius `sqrt (max R 0)`, because `h`
  -- vanishes on `[R, ∞)`.
  have hcs : HasCompactSupport (gaussianTimesProfile (n := n) y h) := by
    obtain ⟨R, hR⟩ := hsupp
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (max R 0))) ?_
    intro x hx
    simp only [Function.mem_support] at hx
    have hx' : h (‖x‖ ^ 2) ≠ 0 := by
      intro h0
      apply hx
      unfold gaussianTimesProfile
      rw [h0, mul_zero]
    have hlt : ‖x‖ ^ 2 < R := by
      by_contra hc
      apply hx'
      apply hR
      rw [abs_of_nonneg (sq_nonneg _)]
      exact not_lt.mp hc
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖x‖ ^ 2 ≤ max R 0 := le_trans (le_of_lt hlt) (le_max_left _ _)
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ Real.sqrt (max R 0) := Real.sqrt_le_sqrt h2
  have hsmooth : ContDiff ℝ ∞ (gaussianTimesProfile (n := n) y h) := by
    unfold gaussianTimesProfile gaussianWeight
    have hnorm : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (‖x‖ ^ 2 : ℝ)) :=
      contDiff_norm_sq ℝ
    have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (↑(‖x‖ ^ 2) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hnorm
    have h2 : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin n) => (↑Real.pi * ↑y : ℂ) * ↑(‖x‖ ^ 2)) :=
      (contDiff_const (c := (↑Real.pi * ↑y : ℂ))).mul h1
    have hexp : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin n) =>
          Complex.exp (-((↑Real.pi * ↑y : ℂ) * ↑(‖x‖ ^ 2)))) :=
      Complex.contDiff_exp.comp h2.neg
    have hprof : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => h (‖x‖ ^ 2)) :=
      hh.comp (contDiff_norm_sq ℝ)
    exact hexp.mul hprof
  exact ⟨hcs.toSchwartzMap hsmooth, fun x => rfl⟩

end Work.Radial
