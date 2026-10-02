import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Classical Filter Set
open scoped Topology

theorem rayPt_injOn {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {θ₁ θ₂ t₁ t₂ : ℝ}
    (hθ₁₀ : 0 ≤ θ₁) (hθ₁₁ : θ₁ < 1) (hθ₂₀ : 0 ≤ θ₂) (hθ₂₁ : θ₂ < 1) (ht₁ : 1 < t₁) (ht₂ : 1 < t₂)
    (h : Work.Top.NakaneData.rayPt hN θ₁ t₁ = Work.Top.NakaneData.rayPt hN θ₂ t₂) :
    θ₁ = θ₂ ∧ t₁ = t₂ := by
  -- The Böttcher coordinate of a ray point is the underlying point of the exterior.
  have hp : Work.Top.NakaneData.rayPoint θ₁ t₁ = Work.Top.NakaneData.rayPoint θ₂ t₂ := by
    rw [← Work.Top.NakaneData.Phi_rayPt hN ht₁, ← Work.Top.NakaneData.Phi_rayPt hN ht₂, h]
  -- Taking norms recovers the modulus.
  have ht : t₁ = t₂ := by
    have h1 := congrArg norm hp
    rw [Work.Top.NakaneData.norm_rayPoint, Work.Top.NakaneData.norm_rayPoint,
      abs_of_pos (by linarith : (0:ℝ) < t₁), abs_of_pos (by linarith : (0:ℝ) < t₂)] at h1
    exact h1
  -- Hence the directions agree.
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * (θ₁ : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * (θ₂ : ℂ) * Complex.I) := by
    have h1 : t₁ * Complex.exp (2 * (Real.pi : ℂ) * (θ₁ : ℂ) * Complex.I)
        = t₁ * Complex.exp (2 * (Real.pi : ℂ) * (θ₂ : ℂ) * Complex.I) := by
      rw [← ht] at hp
      exact hp
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (by linarith)) h1
  -- Equal exponentials differ by an integer multiple of the period.
  have hreal : ∃ n : ℤ, (θ₁ : ℂ) = (θ₂ : ℂ) + (n : ℂ) := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨n, ?_⟩
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.ext_iff, Real.pi_ne_zero]
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (θ₁ : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((θ₂ : ℂ) + (n : ℂ)) := by
      ring_nf at hn ⊢
      exact hn
    exact mul_left_cancel₀ hne h2
  obtain ⟨n, hn⟩ := hreal
  have hn_eq : θ₁ = θ₂ + (n : ℝ) := by
    have := congrArg Complex.re hn
    simpa using this
  -- Both angles lie in `[0,1)`, so the integer must vanish.
  have hn0 : n = 0 := by
    have h1 : ((n : ℤ) : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < ((n : ℤ) : ℝ) := by linarith
    have h3 : n < 1 := by exact_mod_cast h1
    have h4 : -1 < n := by exact_mod_cast h2
    omega
  exact ⟨by rw [hn_eq, hn0]; simp, ht⟩

end Work.Top
