import Mathlib
import Submission.Work.RPA3.periodic_mem_Icc

open scoped ContDiff

namespace Work.RPB.B5

/-- If `rho τ t 0 = 0`, `rho` is `C¹` on `[0,1] × ℝ × (-ε,ε)` and `rho` is `2π`-periodic in
`t`, then `rho τ t σ` is uniformly bounded by `ε/2` for `σ` small enough, uniformly in
`τ ∈ [0,1]` and `t ∈ ℝ`. -/
theorem uniform_small_rho {rho : ℝ → ℝ → ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hrhoc : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε))
    (hrho0 : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, rho τ t 0 = 0)
    (hrhop : ∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ → ∀ t : ℝ, |rho τ t σ| < ε / 2 := by
  have hFcont : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) := hrhoc.continuousOn
  -- the compact box on which uniform continuity will be applied
  have hKcomp : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (-(ε / 2)) (ε / 2)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKsub : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
        Set.Icc (-(ε / 2)) (ε / 2)) ⊆ (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) := by
    rintro ⟨τ, t, σ⟩ ⟨hτ, ht, hσ⟩
    exact ⟨hτ, trivial, Set.Icc_subset_Ioo (by linarith) (by linarith) hσ⟩
  have hUC : UniformContinuousOn (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) :=
    hKcomp.uniformContinuousOn_of_continuous (hFcont.mono hKsub)
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨ρ, hρpos, hρ⟩ := hUC (ε / 2) (by linarith)
  refine ⟨min (ε / 2) (ρ / 2), lt_min (by linarith) (by linarith),
    le_trans (min_le_left _ _) (by linarith), ?_⟩
  intro τ hτ σ hσ t
  -- reduce `t` modulo `2π`
  have hper : Function.Periodic (fun u : ℝ => fun s : ℝ => rho τ u s) (2 * Real.pi) := by
    intro u
    funext s
    exact hrhop τ u s
  obtain ⟨t₀, ht₀, heq⟩ :=
    Work.RPA3.periodic_mem_Icc Real.two_pi_pos (fun u : ℝ => fun s : ℝ => rho τ u s) hper t
  have hval : rho τ t σ = rho τ t₀ σ := congrFun heq σ
  rw [hval]
  have hδ2 : |σ| ≤ ε / 2 := le_trans hσ (min_le_left _ _)
  have hδρ : |σ| < ρ := lt_of_le_of_lt (le_trans hσ (min_le_right _ _)) (by linarith)
  have hσmem : σ ∈ Set.Icc (-(ε / 2)) (ε / 2) := by
    rw [Set.mem_Icc]
    exact abs_le.mp hδ2
  have hmem1 : (τ, (t₀, σ)) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (-(ε / 2)) (ε / 2) := ⟨hτ, ht₀, hσmem⟩
  have hmem0 : (τ, (t₀, 0)) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (-(ε / 2)) (ε / 2) := ⟨hτ, ht₀, ⟨by linarith, by linarith⟩⟩
  have hdist : dist (τ, (t₀, σ)) (τ, (t₀, 0)) < ρ := by
    rw [show dist (τ, (t₀, σ)) (τ, (t₀, 0)) = |σ| by simp [Prod.dist_eq]]
    exact hδρ
  have hres := hρ (τ, (t₀, σ)) hmem1 (τ, (t₀, 0)) hmem0 hdist
  rw [Real.dist_eq] at hres
  have h0 : rho τ t₀ 0 = 0 := hrho0 τ hτ t₀
  rw [h0, sub_zero] at hres
  exact hres

end Work.RPB.B5
