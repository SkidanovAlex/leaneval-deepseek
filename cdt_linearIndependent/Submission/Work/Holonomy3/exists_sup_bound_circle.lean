import Mathlib
import Submission.Work.Holonomy3.comp_defs

open scoped BigOperators

namespace Work.Holonomy3

/-- A finite family of functions, each analytic (hence continuous) on a disc of radius `ρ > 1`
and multiplied by polynomials, is uniformly bounded on the unit circle. -/
theorem exists_sup_bound_circle {d m : ℕ} (ψ : Fin d → ℂ → ℂ) (N : Fin m → Fin d → ℂ → ℂ)
    (P : Fin m → Fin d → Polynomial ℂ) (ρ : ℝ) (hρ : 1 < ρ)
    (hψ : ∀ s, AnalyticOnNhd ℂ (ψ s) (Metric.ball 0 ρ))
    (hN : ∀ i s, AnalyticOnNhd ℂ (N i s) (Metric.ball 0 ρ)) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i s z, ‖z‖ = 1 →
      ‖N i s z * ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z‖ ≤ M := by
  classical
  -- Per-index bound: the unit sphere is compact, the function is continuous there.
  have hEx : ∀ i s, ∃ B : ℝ, ∀ z, ‖z‖ = 1 →
      ‖N i s z * ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z‖ ≤ B := by
    intro i s
    have hsub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) ρ := by
      intro z hz
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball, hz]
      exact hρ
    have hcontN : ContinuousOn (N i s) (Metric.sphere (0 : ℂ) 1) :=
      (hN i s).continuousOn.mono hsub
    have hcontP : ContinuousOn (fun z => ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z)
        (Metric.sphere (0 : ℂ) 1) :=
      (continuous_finsetProd _ (fun i' _ => (P i' s).continuous)).continuousOn
    obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn
      (hcontN.mul hcontP)
    refine ⟨C, ?_⟩
    intro z hz
    exact hC z (by rw [Metric.mem_sphere, dist_eq_norm]; simpa using hz)
  by_cases hne : Nonempty (Fin m × Fin d)
  · -- finitely many indices: take the max of the per-index bounds.
    haveI := hne
    choose B hB using hEx
    refine ⟨max 1 (Finset.univ.sup' Finset.univ_nonempty (fun p : Fin m × Fin d => B p.1 p.2)),
      le_max_left _ _, ?_⟩
    intro i s z hz
    have h1 : ‖N i s z * ∏ i' ∈ Finset.univ.erase i, (P i' s).eval z‖ ≤ B i s := hB i s z hz
    have h2 : B i s ≤
        Finset.univ.sup' Finset.univ_nonempty (fun p : Fin m × Fin d => B p.1 p.2) :=
      Finset.le_sup' (fun p : Fin m × Fin d => B p.1 p.2) (Finset.mem_univ (i, s))
    exact le_trans h1 (le_trans h2 (le_max_right _ _))
  · -- no indices at all: the statement is vacuous.
    exact ⟨1, le_refl 1, fun i s z hz => (hne ⟨(i, s)⟩).elim⟩

end Work.Holonomy3
