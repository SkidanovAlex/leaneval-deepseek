import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Holder

open Set Metric
open scoped Topology

/-- Elementary real inequality: for `d ∈ [0, D]` and `0 ≤ α ≤ 1`, the identity map is bounded by
`max D 1 · d^α` on `[0, D]`.  (On a *bounded* interval every Lipschitz bound is an `α`-Hölder
bound, for every `α ≤ 1`.) -/
theorem self_le_max_mul_rpow {d D α : ℝ} (hd : 0 ≤ d) (hdD : d ≤ D) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) : d ≤ max D 1 * d ^ α := by
  have hD1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have hD0 : (0 : ℝ) ≤ max D 1 := le_trans zero_le_one hD1
  rcases eq_or_lt_of_le hα0 with hα | hα
  · rw [← hα, Real.rpow_zero, mul_one]
    exact le_trans hdD (le_max_left _ _)
  · rcases eq_or_lt_of_le hd with hd0 | hdpos
    · rw [← hd0, Real.zero_rpow (ne_of_gt hα), mul_zero]
    · rcases le_or_gt d 1 with hd1 | hd1
      · have hle : d ≤ d ^ α := by
          have h := Real.rpow_le_rpow_of_exponent_ge hdpos hd1 hα1
          rwa [Real.rpow_one] at h
        calc d ≤ d ^ α := hle
          _ ≤ max D 1 * d ^ α :=
              le_mul_of_one_le_left (Real.rpow_nonneg (le_of_lt hdpos) α) hD1
      · have hle : (1 : ℝ) ≤ d ^ α := Real.one_le_rpow (le_of_lt hd1) hα0
        calc d ≤ D := hdD
          _ ≤ max D 1 := le_max_left _ _
          _ = max D 1 * 1 := (mul_one _).symm
          _ ≤ max D 1 * d ^ α := mul_le_mul_of_nonneg_left hle hD0

theorem timeHolderOnBall_of_isContDiffHolderOn {α : NNReal}
    {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3} {ρ R T : ℝ}
    (hρ : R < ρ) (hα1 : (α : ℝ) ≤ 1)
    (hcore : IsContDiffHolderOn ℝ α ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T)) :
    ∃ H : ℝ, 0 ≤ H ∧ Work.StabilityFar.TimeHolderOnBall (α : ℝ) ω R T H := by
  obtain ⟨hcd, hbdd, _⟩ := hcore
  set s : Set (Work.SolutionDelivery.R3 × ℝ) :=
    Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T with hsdef
  -- a uniform bound for the derivative on `s`
  obtain ⟨B, hB⟩ : ∃ B : ℝ,
      ∀ x ∈ s, ‖fderivWithin ℝ ω.uncurry s x‖ ≤ B := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : (Work.SolutionDelivery.R3 × ℝ) →L[ℝ] Work.SolutionDelivery.R3)).1 hbdd
    refine ⟨max r 0, fun x hx => le_trans ?_ (le_max_left _ _)⟩
    have hx' : fderivWithin ℝ ω.uncurry s x ∈
        fderivWithin ℝ ω.uncurry s '' s := ⟨x, hx, rfl⟩
    have := hr hx'
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  -- differentiability and convexity of `s`
  have hdiff : DifferentiableOn ℝ ω.uncurry s := hcd.differentiableOn (by norm_num)
  have hconv : Convex ℝ s := by
    rw [hsdef]
    refine Convex.prod ?_ (Work.SolutionDelivery.convex_extWindow T)
    have hball : Work.StabilityFar.coreRegion ρ
        = Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ := by
      ext x
      simp [Work.StabilityFar.mem_coreRegion, dist_eq_norm]
    rw [hball]
    exact convex_closedBall _ _
  refine ⟨max B 0 * max (T + 2) 1, ?_, ?_⟩
  · exact mul_nonneg (le_max_right _ _) (le_trans zero_le_one (le_max_right _ _))
  · intro z hz t ht τ hτ
    have hzρ : z ∈ Work.StabilityFar.coreRegion ρ := by
      rw [Work.StabilityFar.mem_coreRegion]
      exact le_trans (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz) (le_of_lt hρ)
    have hwt : t ∈ Work.SolutionDelivery.extWindow T :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hwτ : τ ∈ Work.SolutionDelivery.extWindow T :=
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hzt : (z, t) ∈ s := by rw [hsdef]; exact ⟨hzρ, hwt⟩
    have hzτ : (z, τ) ∈ s := by rw [hsdef]; exact ⟨hzρ, hwτ⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_fderivWithin_le hdiff hB hconv hzτ hzt
    have hnorm : ‖((z, t) : Work.SolutionDelivery.R3 × ℝ) - (z, τ)‖ = |t - τ| := by simp
    have hstep : ‖ω z t - ω z τ‖ ≤ max B 0 * |t - τ| :=
      calc ‖ω z t - ω z τ‖
          = ‖ω.uncurry (z, t) - ω.uncurry (z, τ)‖ := rfl
        _ ≤ B * ‖(z, t) - (z, τ)‖ := hmvt
        _ = B * |t - τ| := by rw [hnorm]
        _ ≤ max B 0 * |t - τ| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    have hdt : |t - τ| ≤ T + 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [ht.2, hτ.1], by linarith [hτ.2, ht.1]⟩
    have hkey : |t - τ| ≤ max (T + 2) 1 * |t - τ| ^ (α : ℝ) :=
      self_le_max_mul_rpow (abs_nonneg _) hdt (by positivity) hα1
    calc ‖ω z t - ω z τ‖ ≤ max B 0 * |t - τ| := hstep
      _ ≤ max B 0 * (max (T + 2) 1 * |t - τ| ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left hkey (le_max_right _ _)
      _ = max B 0 * max (T + 2) 1 * |t - τ| ^ (α : ℝ) := by ring

end Work.SolutionDelivery.Holder
