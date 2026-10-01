import Mathlib

namespace Work.ZeroFreeTables.XY

/-- For real `a b δ` with `δ > 0`, the norm of the complex number `a + b·i` is at most
`δ` exactly when `a² + b² ≤ δ²`. -/
lemma norm_le_iff {a b δ : ℝ} (hδ : 0 < δ) :
    ‖(a:ℂ) + (b:ℂ)*Complex.I‖ ≤ δ ↔ a^2 + b^2 ≤ δ^2 := by
  have hsq : ‖(a:ℂ) + (b:ℂ)*Complex.I‖^2 = a^2 + b^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  rw [← hsq, sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_pos hδ]

theorem NearNorm {L lam γ δ : ℝ} (hδ : 0 < δ) {ρ : ℂ} (hre : ρ.re = 1 - lam/L) (him : ρ.im = γ) :
    ((‖(1:ℂ) + (γ:ℂ)*Complex.I - ρ‖ ≤ δ) ↔ ((lam/L)^2 ≤ δ^2))
  ∧ ((‖(1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - ρ‖ ≤ δ) ↔ ((lam/L)^2 + (2*γ)^2 ≤ δ^2))
  ∧ ((‖(1:ℂ) + (γ:ℂ)*Complex.I - starRingEnd ℂ ρ‖ ≤ δ) ↔ ((lam/L)^2 + (2*γ)^2 ≤ δ^2))
  ∧ ((‖(1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - starRingEnd ℂ ρ‖ ≤ δ) ↔ ((lam/L)^2 + (4*γ)^2 ≤ δ^2)) := by
  have hρ : ρ = ((1 - lam/L : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre, him]
  have hρc : starRingEnd ℂ ρ = ((1 - lam/L : ℝ) : ℂ) - (γ : ℂ) * Complex.I := by
    rw [hρ]; apply Complex.ext <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz : (1:ℂ) + (γ:ℂ)*Complex.I - ρ = ((lam/L:ℝ):ℂ) + ((0:ℝ):ℂ)*Complex.I := by
      rw [hρ]
      apply Complex.ext <;> simp
    rw [hz, norm_le_iff hδ]; norm_num
  · have hz : (1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - ρ = ((lam/L:ℝ):ℂ) + ((2*γ:ℝ):ℂ)*Complex.I := by
      rw [hρ]
      apply Complex.ext <;> simp
      all_goals ring_nf
    rw [hz, norm_le_iff hδ]
  · have hz : (1:ℂ) + (γ:ℂ)*Complex.I - starRingEnd ℂ ρ = ((lam/L:ℝ):ℂ) + ((2*γ:ℝ):ℂ)*Complex.I := by
      rw [hρc]
      apply Complex.ext <;> simp
      all_goals ring_nf
    rw [hz, norm_le_iff hδ]
  · have hz : (1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - starRingEnd ℂ ρ = ((lam/L:ℝ):ℂ) + ((4*γ:ℝ):ℂ)*Complex.I := by
      rw [hρc]
      apply Complex.ext <;> simp
      all_goals ring_nf
    rw [hz, norm_le_iff hδ]

end Work.ZeroFreeTables.XY
