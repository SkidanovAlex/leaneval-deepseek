import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# FATOU continuity (`Work.FatouCH`): the derivative approximation `Φ' ≈ 1/(F z - z)`

This discharges the local form of Shishikura's Lemma A.2.4(i) (`MandelDim.FatouDerivEstimate`)
needed by the Cauchy–Heine route to `MandelDim.FatouStatement`.

Given `hD : MandelDim.FatouDerivEstimate` we produce universal constants `R₁, C₂, L > 0` with the
following property: for an admissible pair `b₁, b₂`, a near-translation `F` on `𝒬 = Qreg b₁ b₂`, a
Fatou coordinate `Φ` of `F` on `𝒬`, and a point `z` whose ball of radius `R₁` lies in `𝒬`, one has

* `‖deriv Φ z - 1 / (F z - z)‖ ≤ C₂ / R₁`, and
* `‖deriv Φ z‖ ≤ L`.

The first is `MandelDim.FatouDerivEstimate` applied with the moving point `v w = F w - w`, which is
holomorphic, satisfies `‖v w - 1‖ ≤ 1/32 < 1/4`, and for which the Abel relation
`Φ (w + v w) = Φ w + 1` is exactly `IsFatouCoordOn`'s orbit relation.  The second follows because
`‖F z - z‖ ≥ 1 - 1/32 = 31/32`, so `‖1/(F z - z)‖ ≤ 32/31`.
-/

namespace Work.FatouCH.Cont

open Set Metric Complex
open scoped Topology

theorem DerivApprox (hD : MandelDim.FatouDerivEstimate) :
    ∃ R₁ C₂ L : ℝ, 0 < R₁ ∧ 0 < C₂ ∧ 0 < L ∧
      (∀ (F Φ : ℂ → ℂ) (b₁ b₂ : Option ℂ) (z : ℂ), MandelDim.QAdm b₁ b₂ →
        MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂) →
        MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) →
        Metric.ball z R₁ ⊆ MandelDim.Qreg b₁ b₂ →
        ‖deriv Φ z - 1 / (F z - z)‖ ≤ C₂ / R₁ ∧ ‖deriv Φ z‖ ≤ L) := by
  obtain ⟨R₀, C₁, C₂, hR₀, hC₁, hC₂, hmain⟩ := hD
  refine ⟨R₀, C₂, C₂ / R₀ + 32 / 31, hR₀, hC₂, ?_, ?_⟩
  · positivity
  · intro F Φ b₁ b₂ z hAdm hNT hFC hball
    -- `z` lies in the region, so the near-translation estimates apply at `z`.
    have hz_ball : z ∈ ball z R₀ := Metric.mem_ball_self hR₀
    have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := hball hz_ball
    -- Restrict the hypotheses to the ball `ball z R₀`.
    have hΦdiff : DifferentiableOn ℂ Φ (ball z R₀) := hFC.1.mono hball
    have hΦinj : Set.InjOn Φ (ball z R₀) := hFC.2.1.mono hball
    -- The moving point `v w = F w - w` is holomorphic on the ball.
    have hvdiff : DifferentiableOn ℂ (fun w => F w - w) (ball z R₀) :=
      (hNT.1.mono hball).sub differentiableOn_id
    -- `‖v w - 1‖ ≤ 1/32 < 1/4` on the ball.
    have hv1 : ∀ w ∈ ball z R₀, ‖(F w - w) - 1‖ < 1 / 4 := by
      intro w hw
      have h := (hNT.2 w (hball hw)).1
      have h2 : ‖(F w - w) - 1‖ ≤ 1 / 32 := by
        convert h using 2
        ring
      linarith
    -- The Abel relation for `v`: `Φ (w + v w) = Φ w + 1`.
    have hAbel : ∀ w ∈ ball z R₀, w + (F w - w) ∈ ball z R₀ →
        Φ (w + (F w - w)) = Φ w + 1 := by
      intro w hw hw'
      have hwF : F w ∈ ball z R₀ := by
        convert hw' using 1
        ring
      have := hFC.2.2 w (hball hw) (hball hwF)
      convert this using 2
      ring
    obtain ⟨-, hderiv⟩ :=
      hmain Φ (fun w => F w - w) z R₀ le_rfl hΦdiff hΦinj hvdiff hv1 hAbel
    refine ⟨hderiv, ?_⟩
    -- `‖F z - z‖ ≥ 1 - 1/32 = 31/32`, hence `‖1/(F z - z)‖ ≤ 32/31`.
    have hFz_ge : (31 : ℝ) / 32 ≤ ‖F z - z‖ := by
      have h := (hNT.2 z hzQ).1
      have h2 : ‖(F z - z) - 1‖ ≤ 1 / 32 := by
        convert h using 2
        ring
      have h3 : |‖F z - z‖ - 1| ≤ 1 / 32 := by
        have := abs_norm_sub_norm_le (F z - z) (1 : ℂ)
        simpa using le_trans this h2
      have := (abs_le.mp h3).1
      linarith
    have hInv : ‖1 / (F z - z)‖ ≤ 32 / 31 := by
      rw [one_div, norm_inv]
      have hpos : (0 : ℝ) < 31 / 32 := by norm_num
      have h32 : ((31 : ℝ) / 32)⁻¹ = 32 / 31 := by norm_num
      have h := inv_anti₀ hpos hFz_ge
      rwa [h32] at h
    calc ‖deriv Φ z‖ = ‖(deriv Φ z - 1 / (F z - z)) + 1 / (F z - z)‖ := by ring_nf
      _ ≤ ‖deriv Φ z - 1 / (F z - z)‖ + ‖1 / (F z - z)‖ := norm_add_le _ _
      _ ≤ C₂ / R₀ + 32 / 31 := add_le_add hderiv hInv

end Work.FatouCH.Cont
