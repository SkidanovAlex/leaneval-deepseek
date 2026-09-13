import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.Calculus.LocalMax

open Metric Filter

theorem exists_max_perturb_ball_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {u : ℕ → E → ℝ} {g φ : E → ℝ} {x₀ : E} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R)
    (hcont : ∀ k, ContinuousOn (u k) (Metric.closedBall x₀ R))
    (hφ : ContinuousOn φ (Metric.closedBall x₀ R))
    (hconv : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ y ∈ Metric.closedBall x₀ R,
        |u k y - g y| < δ)
    (hmax : ∀ y ∈ Metric.closedBall x₀ R, g y - φ y ≤ g x₀ - φ x₀) :
    ∀ᶠ k in Filter.atTop, ∃ x ∈ Metric.ball x₀ (ε / 2),
      ∀ y ∈ Metric.closedBall x₀ ε,
        u k y - φ y - ε * ‖y - x₀‖ ^ 2 ≤ u k x - φ x - ε * ‖x - x₀‖ ^ 2 := by
  set δ : ℝ := ε ^ 3 / 16 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hsub : Metric.closedBall x₀ ε ⊆ Metric.closedBall x₀ R :=
    Metric.closedBall_subset_closedBall (le_of_lt hεR)
  filter_upwards [hconv δ hδpos] with k hk
  let F : E → ℝ := fun y => u k y - φ y - ε * ‖y - x₀‖ ^ 2
  have hcontF : ContinuousOn F (Metric.closedBall x₀ ε) := by
    change ContinuousOn (fun y : E => u k y - φ y - ε * ‖y - x₀‖ ^ 2)
      (Metric.closedBall x₀ ε)
    have h1 : ContinuousOn (u k) (Metric.closedBall x₀ ε) := (hcont k).mono hsub
    have h2 : ContinuousOn φ (Metric.closedBall x₀ ε) := hφ.mono hsub
    have h3 : ContinuousOn (fun y : E => ε * ‖y - x₀‖ ^ 2)
        (Metric.closedBall x₀ ε) :=
      (continuous_const.mul
        ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)).continuousOn
    exact (h1.sub h2).sub h3
  have hne : (Metric.closedBall x₀ ε).Nonempty := by
    refine ⟨x₀, ?_⟩
    rw [Metric.mem_closedBall, dist_self]
    exact hε.le
  obtain ⟨x, hxmem, hxmax⟩ := (isCompact_closedBall x₀ ε).exists_isMaxOn hne hcontF
  rw [isMaxOn_iff] at hxmax
  have hx0mem : x₀ ∈ Metric.closedBall x₀ ε := by
    rw [Metric.mem_closedBall, dist_self]
    exact hε.le
  have hx0memR : x₀ ∈ Metric.closedBall x₀ R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR.le
  -- key inequality: F x - F x₀ < 2δ - ε‖x-x₀‖²
  have hkey : F x - F x₀ < 2 * δ - ε * ‖x - x₀‖ ^ 2 := by
    have hxR : x ∈ Metric.closedBall x₀ R := hsub hxmem
    have hxk : |u k x - g x| < δ := hk x hxR
    have hx0k : |u k x₀ - g x₀| < δ := hk x₀ hx0memR
    have hA : (u k x - g x) - (u k x₀ - g x₀) < 2 * δ := by
      have h1 := (abs_lt.mp hxk).2
      have h2 := (abs_lt.mp hx0k).1
      linarith
    have hB : (g x - φ x) - (g x₀ - φ x₀) ≤ 0 := by
      have := hmax x hxR
      linarith
    have hFy : F x = u k x - φ x - ε * ‖x - x₀‖ ^ 2 := rfl
    have hF0 : F x₀ = u k x₀ - φ x₀ := by simp [F]
    have hdec : F x - F x₀
        = ((u k x - g x) - (u k x₀ - g x₀)) + ((g x - φ x) - (g x₀ - φ x₀))
          - ε * ‖x - x₀‖ ^ 2 := by
      rw [hFy, hF0]; ring
    rw [hdec]; linarith
  have hx0le : F x₀ ≤ F x := hxmax x₀ hx0mem
  have hquad : ε * ‖x - x₀‖ ^ 2 < 2 * δ := by linarith
  have hmid : 2 * δ < ε * (ε / 2) ^ 2 := by
    rw [hδdef]; nlinarith [hε]
  have hlt : ε * ‖x - x₀‖ ^ 2 < ε * (ε / 2) ^ 2 := by linarith
  have hsq : ‖x - x₀‖ ^ 2 < (ε / 2) ^ 2 := lt_of_mul_lt_mul_left hlt hε.le
  have hfin : ‖x - x₀‖ < ε / 2 := by
    by_contra h
    have hle : ε / 2 ≤ ‖x - x₀‖ := not_lt.mp h
    have h2 : (ε / 2) ^ 2 ≤ ‖x - x₀‖ ^ 2 := by
      nlinarith [hle, norm_nonneg (x - x₀), hε]
    linarith
  refine ⟨x, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    exact hfin
  · intro y hy
    exact hxmax y hy

end Commons.Analysis.Calculus.LocalMax