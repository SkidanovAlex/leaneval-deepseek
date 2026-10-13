import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

theorem Vth_lip_slice {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {K S : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith ⟨K, hK⟩
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)))
    {z τ θ₁ θ₂ : ℝ} (hz : 0 < z) (hτ : τ ∈ Set.Icc 0 S)
    (h₁ : θ₁ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) (h₂ : θ₂ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    |Vθ z θ₁ τ - Vθ z θ₂ τ| ≤ K * |θ₁ - θ₂| := by
  -- Both points `(z, θ₁)` and `(z, θ₂)` lie in the domain `Ioi 0 ×ˢ Ioo 0 (π/2)` of the
  -- Lipschitz map, so the Lipschitz bound applies to them.
  have hp₁ : ((z, θ₁) : ℝ × ℝ) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hz, h₁⟩
  have hp₂ : ((z, θ₂) : ℝ × ℝ) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hz, h₂⟩
  have hd := (hlip τ hτ).dist_le_mul (z, θ₁) hp₁ (z, θ₂) hp₂
  -- The second coordinate of the product metric is dominated by the product metric.
  have hle : dist (Vθ z θ₁ τ) (Vθ z θ₂ τ)
      ≤ dist ((Vz z θ₁ τ, Vθ z θ₁ τ) : ℝ × ℝ) (Vz z θ₂ τ, Vθ z θ₂ τ) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  -- The two base points share their first coordinate, so their distance is `|θ₁ - θ₂|`.
  have hdist : dist ((z, θ₁) : ℝ × ℝ) (z, θ₂) = |θ₁ - θ₂| := by
    simp [Prod.dist_eq, Real.dist_eq]
  calc |Vθ z θ₁ τ - Vθ z θ₂ τ| = dist (Vθ z θ₁ τ) (Vθ z θ₂ τ) := (Real.dist_eq _ _).symm
    _ ≤ dist ((Vz z θ₁ τ, Vθ z θ₁ τ) : ℝ × ℝ) (Vz z θ₂ τ, Vθ z θ₂ τ) := hle
    _ ≤ K * dist ((z, θ₁) : ℝ × ℝ) (z, θ₂) := hd
    _ = K * |θ₁ - θ₂| := by rw [hdist]

end Work.FTS.RegPkgGal.R7d
