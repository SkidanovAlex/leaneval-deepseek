import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kappa_shape_geom_small

namespace Work.RPB.B5

theorem karS_pos_of_nonneg (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 0 ≤ σ →
        0 < Work.RPB.B5.karS CI W ρh δ k τ σ := by
  -- The `σ`-range splits at `σ = δ`: on `[0, δ]` the shape is a small perturbation of the
  -- reference family, and for `σ ≥ δ` it *is* the far rescaled family, whose signed area is
  -- `2π(1+σ) > 0`.
  obtain ⟨δ₀, hδ₀pos, hδ₀κ, hsmall⟩ :=
    kappa_shape_geom_small CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hWper hρh hρh0 hρhv hρhl
      hρhper k
  refine ⟨δ₀, hδ₀pos, hδ₀κ, ?_⟩
  intro δ hδ τ hτ σ hσ
  rw [Set.mem_Ioo] at hδ
  by_cases hσδ : σ ≤ δ
  · exact (hsmall δ hδ τ hτ σ ⟨hσ, hσδ⟩).1
  · rw [ksb_karS_far CI W ρh hδ.1 k hτ (le_of_lt (not_le.mp hσδ))]
    nlinarith [Real.pi_pos]

end Work.RPB.B5
