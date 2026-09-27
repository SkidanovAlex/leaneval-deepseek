import Mathlib
import Submission.Work.Drive.uniform_band_of_periodic

namespace Work.Drive

/-- **A uniform collar around the axis for the seam data.**  Given `C^∞` maps `M W : ℝ → ℝ → ℂ`
which are `2π`-periodic in their first variable and non-vanishing on the axis `τ = 0`, all three
open conditions

`W θ τ ≠ 0`,  `0 < ‖M θ τ‖² + 4 τ ‖W θ τ‖²`,  `‖M θ τ‖² < 2 (‖M θ τ‖² + 4 τ ‖W θ τ‖²)`

hold simultaneously on a *uniform* band `|τ| ≤ c`, `c > 0`, independent of `θ`.  Each of the three
functions is continuous and `2π`-periodic in `θ` and positive on the axis, so the tube lemma
`Work.Drive.uniform_band_of_periodic` gives a band for each; take the smallest. -/
theorem exists_collar_ne_pos (M W : ℝ → ℝ → ℂ)
    (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry M))
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry W))
    (hMper : ∀ θ τ, M (θ + 2 * Real.pi) τ = M θ τ)
    (hWper : ∀ θ τ, W (θ + 2 * Real.pi) τ = W θ τ)
    (hM0 : ∀ θ, M θ 0 ≠ 0) (hW0 : ∀ θ, W θ 0 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ τ : ℝ, |τ| ≤ c →
      W θ τ ≠ 0 ∧ 0 < ‖M θ τ‖ ^ 2 + 4 * τ * ‖W θ τ‖ ^ 2 ∧
        ‖M θ τ‖ ^ 2 < 2 * (‖M θ τ‖ ^ 2 + 4 * τ * ‖W θ τ‖ ^ 2) := by
  have hMc : Continuous (fun p : ℝ × ℝ => M p.1 p.2) := hM.continuous
  have hWc : Continuous (fun p : ℝ × ℝ => W p.1 p.2) := hW.continuous
  -- First condition: `0 < ‖M‖² + 4 τ ‖W‖²`.
  have hcont₁ : Continuous (fun p : ℝ × ℝ => ‖M p.1 p.2‖ ^ 2 + 4 * p.2 * ‖W p.1 p.2‖ ^ 2) :=
    ((hMc.norm).pow 2).add ((continuous_const.mul continuous_snd).mul ((hWc.norm).pow 2))
  have hper₁ : ∀ σ τ : ℝ, ‖M (σ + 2 * Real.pi) τ‖ ^ 2 + 4 * τ * ‖W (σ + 2 * Real.pi) τ‖ ^ 2
      = ‖M σ τ‖ ^ 2 + 4 * τ * ‖W σ τ‖ ^ 2 := by
    intro σ τ; rw [hMper, hWper]
  have hpos₁ : ∀ σ : ℝ, 0 < ‖M σ 0‖ ^ 2 + 4 * 0 * ‖W σ 0‖ ^ 2 := by
    intro σ
    simp only [mul_zero, zero_mul, add_zero]
    exact pow_pos (norm_pos_iff.mpr (hM0 σ)) 2
  -- Second condition: `0 < ‖M‖² + 8 τ ‖W‖²`, equivalent to the strict inequality.
  have hcont₂ : Continuous (fun p : ℝ × ℝ => ‖M p.1 p.2‖ ^ 2 + 8 * p.2 * ‖W p.1 p.2‖ ^ 2) :=
    ((hMc.norm).pow 2).add ((continuous_const.mul continuous_snd).mul ((hWc.norm).pow 2))
  have hper₂ : ∀ σ τ : ℝ, ‖M (σ + 2 * Real.pi) τ‖ ^ 2 + 8 * τ * ‖W (σ + 2 * Real.pi) τ‖ ^ 2
      = ‖M σ τ‖ ^ 2 + 8 * τ * ‖W σ τ‖ ^ 2 := by
    intro σ τ; rw [hMper, hWper]
  have hpos₂ : ∀ σ : ℝ, 0 < ‖M σ 0‖ ^ 2 + 8 * 0 * ‖W σ 0‖ ^ 2 := by
    intro σ
    simp only [mul_zero, zero_mul, add_zero]
    exact pow_pos (norm_pos_iff.mpr (hM0 σ)) 2
  -- Third condition: `W ≠ 0`, expressed as `0 < ‖W‖`.
  have hcont₃ : Continuous (fun p : ℝ × ℝ => ‖W p.1 p.2‖) := hWc.norm
  have hper₃ : ∀ σ τ : ℝ, ‖W (σ + 2 * Real.pi) τ‖ = ‖W σ τ‖ := by
    intro σ τ; rw [hWper]
  have hpos₃ : ∀ σ : ℝ, 0 < ‖W σ 0‖ := by
    intro σ; exact norm_pos_iff.mpr (hW0 σ)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := uniform_band_of_periodic hcont₁ hper₁ hpos₁
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := uniform_band_of_periodic hcont₂ hper₂ hpos₂
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := uniform_band_of_periodic hcont₃ hper₃ hpos₃
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁pos (lt_min hδ₂pos hδ₃pos), ?_⟩
  intro θ τ hτ
  have h1 := hδ₁ θ τ (le_trans hτ (min_le_left _ _))
  have h2 := hδ₂ θ τ (le_trans hτ (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h3 := hδ₃ θ τ (le_trans hτ (le_trans (min_le_right _ _) (min_le_right _ _)))
  exact ⟨norm_pos_iff.mp h3, h1, by linarith⟩

end Work.Drive
