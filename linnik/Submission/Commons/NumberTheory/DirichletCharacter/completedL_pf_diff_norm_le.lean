import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le

open Complex DirichletCharacter Metric Filter Function MeromorphicOn Topology
open scoped Real BigOperators

namespace Commons.NumberTheory.DirichletCharacter

theorem completedL_pf_diff_norm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s s₀ : ℂ)
    (hs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hs₀ : DirichletCharacter.completedLFunction χ s₀ ≠ 0) (C : ℝ)
    (hC : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℝ) * ‖1 / (s - u) - 1 / (s₀ - u)‖) ≤ C) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) s₀‖ ≤ C := by
  classical
  -- Analyticity of the completed L-function on every closed ball.
  have hAnal : ∀ R : ℝ, AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) R) := by
    intro R z _
    exact (differentiable_completedLFunction hχ).analyticAt z
  -- The partial-fraction sums (with the `+1/u` kernel) converge to the log-derivative
  -- differences against `s = 0`.
  let A : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
  let B : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u)
  let H : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))
  have hA : Tendsto A atTop (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s /
      DirichletCharacter.completedLFunction χ s -
      deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0)) := by
    simpa [A] using Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hs
  have hB : Tendsto B atTop (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s₀ /
      DirichletCharacter.completedLFunction χ s₀ -
      deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0)) := by
    simpa [B] using Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s₀ hs₀
  -- Pointwise identity: `A R - B R = H R`.
  have hHR : ∀ R : ℝ, A R - B R = H R := by
    intro R
    have hsupp : (Function.support (fun u : ℂ =>
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u)).Finite :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
    have hfinA : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) :=
      hsupp.subset (fun u hu hd0 => hu (by simp [hd0]))
    have hfinB : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u)) :=
      hsupp.subset (fun u hu hd0 => hu (by simp [hd0]))
    simp only [A, B, H]
    rw [← finsum_sub_distrib hfinA hfinB]
    apply finsum_congr
    intro u
    ring
  -- Convergence of `H` to the desired log-derivative difference.
  have hHlim : Tendsto H atTop (𝓝 (logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) s₀)) := by
    have hAB : Tendsto (fun R => A R - B R) atTop (𝓝 (
        (deriv (DirichletCharacter.completedLFunction χ) s /
            DirichletCharacter.completedLFunction χ s -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0) -
        (deriv (DirichletCharacter.completedLFunction χ) s₀ /
            DirichletCharacter.completedLFunction χ s₀ -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0))) := hA.sub hB
    have hcongr : (fun R => A R - B R) =ᶠ[atTop] H :=
      Filter.Eventually.of_forall (fun R => hHR R)
    have h1 : Tendsto H atTop (𝓝 (
        (deriv (DirichletCharacter.completedLFunction χ) s /
            DirichletCharacter.completedLFunction χ s -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0) -
        (deriv (DirichletCharacter.completedLFunction χ) s₀ /
            DirichletCharacter.completedLFunction χ s₀ -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0))) := hAB.congr' hcongr
    have heq : ((deriv (DirichletCharacter.completedLFunction χ) s /
            DirichletCharacter.completedLFunction χ s -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0) -
        (deriv (DirichletCharacter.completedLFunction χ) s₀ /
            DirichletCharacter.completedLFunction χ s₀ -
          deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0)) =
        (logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) s₀) := by
      rw [logDeriv_apply, logDeriv_apply]
      ring
    rw [heq] at h1
    exact h1
  -- Norm bound from the hypothesis `hC`.
  have hbound : ∀ R : ℝ, 2 ≤ R → ‖H R‖ ≤ C := by
    intro R hR
    let d : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R)
    let W : ℂ → ℂ := fun u => 1 / (s - u) - 1 / (s₀ - u)
    have hsupp : (Function.support d).Finite := by
      dsimp [d]
      exact (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
    have hg_fin : Function.HasFiniteSupport (fun u : ℂ => ((d u : ℤ) : ℝ) * ‖W u‖) :=
      hsupp.subset (fun u hu hd0 => hu (by simp [hd0]))
    have hfg : ∀ u : ℂ, ‖((d u : ℤ) : ℂ) * W u‖ ≤ ((d u : ℤ) : ℝ) * ‖W u‖ := by
      intro u
      have hdnn : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := by
        dsimp [d]
        exact Commons.Analysis.Complex.divisor_nonneg_on_closedBall (hAnal R) u
      rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    have h1 := Commons.Algebra.BigOperators.norm_finsum_le_of_norm_le
      (f := fun u : ℂ => ((d u : ℤ) : ℂ) * W u)
      (g := fun u : ℂ => ((d u : ℤ) : ℝ) * ‖W u‖) hg_fin hfg
    have h2 : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * ‖W u‖) ≤ C := by
      simpa only [d, W] using hC R hR
    calc ‖H R‖ = ‖∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * W u‖ := by simp only [H, d, W]
      _ ≤ ∑ᶠ u : ℂ, ((d u : ℤ) : ℝ) * ‖W u‖ := h1
      _ ≤ C := h2
  -- Conclude by taking limits.
  have hnorm : Tendsto (fun R => ‖H R‖) atTop (𝓝 ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) s₀‖) := hHlim.norm
  have hev : ∀ᶠ R in atTop, ‖H R‖ ≤ C :=
    Filter.eventually_atTop.mpr ⟨2, fun R hR => hbound R hR⟩
  exact le_of_tendsto hnorm hev

end Commons.NumberTheory.DirichletCharacter
