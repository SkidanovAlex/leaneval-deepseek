import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STHardSlot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- Pointwise bound for a single slot of the *easy* part of the hard integration by parts:
`sin(2θ)^{-q}·f·∂_θv·v` is controlled by `K·C'·C·sin(2θ)^{p-q}`, using
`|f| ≤ K sin 2θ`, `|v| ≤ C sin(2θ)^p` and `|sin(2θ)·∂_θv| ≤ C'`.

The exponent algebra is `sin(2θ)^{-q}·sin(2θ)·sin(2θ)^{-1}·sin(2θ)^p = sin(2θ)^{p-q}`
on `sin(2θ) > 0`; at the endpoints `sin(2θ) = 0` the left-hand side vanishes because
`f = 0` there (from `|f| ≤ K sin 2θ`) while the right-hand side is `≥ 0`. -/
theorem HardSlotABound {q K C C' p : ℝ} {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hC' : 0 ≤ C') (hp0 : 0 ≤ p)
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p)
    (hv2 : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ) * Work.Spaces.pth v z θ| ≤ C') :
    ∀ θ ∈ Work.Spaces.Iθ,
      |(Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ|
        ≤ K * C' * C * (Real.sin (2 * θ)) ^ (p - q) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- endpoint case: `sin (2θ) = 0`
    have hf0 : f z θ = 0 := by
      have h : |f z θ| ≤ 0 := by
        have h1 := hf1 θ hθ
        rwa [← hs, mul_zero] at h1
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    have hz : (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ = 0 := by
      rw [hf0]; ring
    rw [hz, abs_zero, ← hs]
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hC') hC) (Real.rpow_nonneg le_rfl _)
  · -- interior case: `sin (2θ) > 0`
    have hL : |(Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ|
        = (Real.sin (2 * θ)) ^ (-q) * |f z θ| * |Work.Spaces.pth v z θ| * |v z θ| := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 (-q))]
    have hpv : |Work.Spaces.pth v z θ| ≤ C' / Real.sin (2 * θ) := by
      rw [le_div_iff₀ hs]
      calc |Work.Spaces.pth v z θ| * Real.sin (2 * θ)
          = |Real.sin (2 * θ) * Work.Spaces.pth v z θ| := by
            rw [abs_mul, abs_of_pos hs]; ring
        _ ≤ C' := hv2 θ hθ
    have hmain : (Real.sin (2 * θ)) ^ (-q) * Real.sin (2 * θ) * (Real.sin (2 * θ))⁻¹
        * (Real.sin (2 * θ)) ^ p = (Real.sin (2 * θ)) ^ (p - q) := by
      have e1 : (Real.sin (2 * θ)) ^ (-q) * Real.sin (2 * θ)
          = (Real.sin (2 * θ)) ^ (1 - q) := by
        calc (Real.sin (2 * θ)) ^ (-q) * Real.sin (2 * θ)
            = (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
          _ = (Real.sin (2 * θ)) ^ (1 - q) := by
              rw [← Real.rpow_add hs]; ring_nf
      have e2 : (Real.sin (2 * θ)) ^ (1 - q) * (Real.sin (2 * θ))⁻¹
          = (Real.sin (2 * θ)) ^ (-q) := by
        calc (Real.sin (2 * θ)) ^ (1 - q) * (Real.sin (2 * θ))⁻¹
            = (Real.sin (2 * θ)) ^ (1 - q) * (Real.sin (2 * θ)) ^ (-1 : ℝ) := by
              rw [Real.rpow_neg_one]
          _ = (Real.sin (2 * θ)) ^ (-q) := by
              rw [← Real.rpow_add hs]; ring_nf
      have e3 : (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ p
          = (Real.sin (2 * θ)) ^ (p - q) := by
        rw [← Real.rpow_add hs]; ring_nf
      rw [e1, e2, e3]
    calc |(Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ|
        = (Real.sin (2 * θ)) ^ (-q) * |f z θ| * |Work.Spaces.pth v z θ| * |v z θ| := hL
      _ ≤ (Real.sin (2 * θ)) ^ (-q) * (K * Real.sin (2 * θ))
            * (C' / Real.sin (2 * θ)) * (C * (Real.sin (2 * θ)) ^ p) := by
          gcongr
          · exact hf1 θ hθ
          · exact hv1 θ hθ
      _ = K * C' * C * (Real.sin (2 * θ)) ^ (p - q) := by
          rw [div_eq_mul_inv]
          have hfac : (Real.sin (2 * θ)) ^ (-q) * (K * Real.sin (2 * θ))
              * (C' * (Real.sin (2 * θ))⁻¹) * (C * (Real.sin (2 * θ)) ^ p)
              = K * C' * C * ((Real.sin (2 * θ)) ^ (-q) * Real.sin (2 * θ)
                * (Real.sin (2 * θ))⁻¹ * (Real.sin (2 * θ)) ^ p) := by ring
          rw [hfac, hmain]

end Work.FTS.H2
