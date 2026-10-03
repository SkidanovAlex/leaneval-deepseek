import Mathlib
import Submission.Work.Pert.PinLogDev.u_sub_hF_le

/-!
# `Work.Pert.PinLogDev.u_sub_hF_le_rho`

Same content as `u_sub_hF_le`, but with the two hypotheses weakened in the direction the caller
needs: `L` need only contain `closedBall 0 ρ` (not `closedBall 0 rr`), and no differentiability
of `f₀` is required.  The proof is the same algebra: for `z` with `ρ/2 ≤ ‖z‖ < ρ`,

`z (z - σ) (u z - hF z) = (f z - f₀ z) + σ z hF z`

with `‖f z - f₀ z‖ < δ` on `L ⊇ closedBall 0 ρ`, `‖hF z‖ ≤ 2`, `‖z‖ ≤ ρ` and
`‖z - σ‖ ≥ ρ/2 - ρ/4 = ρ/4`; hence `‖u z - hF z‖ ≤ 8δ/ρ² + 16‖σ‖/ρ`, absorbed into
`C (δ/(ρ rr) + ‖σ‖)` with `C = 16 (rr+1)/ρ`.
-/

namespace Work.Pert.PinLogDev

open MandelDim Complex Metric

noncomputable section

theorem u_sub_hF_le_rho (rr ρ : ℝ) (hrr : 0 < rr) (hρ : 0 < ρ) (hρrr : ρ ≤ rr) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f₀ f : ℂ → ℂ} {Df L : Set ℂ} {δ : ℝ} {σ : ℂ} {u hF : ℂ → ℂ},
      MandelDim.NearOn f₀ f Df L δ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖hF z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z) →
      (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
      f₀ 0 = 0 → ‖σ‖ < ρ / 4 →
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, ρ / 2 ≤ ‖z‖ →
        ‖u z - hF z‖ ≤ C * (δ / (ρ * rr) + ‖σ‖) := by
  refine ⟨16 * (rr + 1) / ρ, by positivity, ?_⟩
  intro f₀ f Df L δ σ u hF hnear hL hhF hf0 hf _hf00 hσ z hz hz2
  set C : ℝ := 16 * (rr + 1) / ρ with hCdef
  -- `0 ∈ L`, so `δ > 0`
  have h0L : (0 : ℂ) ∈ L := hL (Metric.mem_closedBall.mpr (by simpa using hρ.le))
  have hδpos : 0 < δ := by
    have h := hnear.2.2.2 0 h0L
    linarith [norm_nonneg (f 0 - f₀ 0)]
  -- `z` lies inside the ball of radius `ρ`, hence inside that of radius `rr`
  have hzlt : ‖z‖ < ρ := by
    have h := Metric.mem_ball.mp hz
    simpa using h
  have hzrr : z ∈ Metric.ball (0 : ℂ) rr :=
    Metric.mem_ball.mpr (by simpa using lt_of_lt_of_le hzlt hρrr)
  have hzL : z ∈ L := hL (Metric.mem_closedBall.mpr (by simpa using hzlt.le))
  have hclose : ‖f z - f₀ z‖ < δ := hnear.2.2.2 z hzL
  have hhFz : ‖hF z‖ ≤ 2 := hhF z hz
  -- the algebraic identity relating the defect to `u - hF`
  have hVeq : z * (z - σ) * (u z - hF z) = (f z - f₀ z) + σ * z * hF z := by
    rw [hf z hzrr, hf0 z hz]; ring
  have hnorm1 : ‖z‖ * ‖z - σ‖ * ‖u z - hF z‖ = ‖(f z - f₀ z) + σ * z * hF z‖ := by
    rw [← hVeq, norm_mul, norm_mul]
  -- the upper bound `‖z‖ ‖z - σ‖ ‖u z - hF z‖ ≤ δ + 2 ‖σ‖ ρ`
  have hbound : ‖z‖ * ‖z - σ‖ * ‖u z - hF z‖ ≤ δ + 2 * ‖σ‖ * ρ := by
    rw [hnorm1]
    have hzle : ‖z‖ ≤ ρ := hzlt.le
    have hszle : ‖σ * z * hF z‖ ≤ ‖σ‖ * ρ * 2 := by
      rw [norm_mul, norm_mul]
      calc ‖σ‖ * ‖z‖ * ‖hF z‖
          ≤ ‖σ‖ * ρ * ‖hF z‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzle (norm_nonneg σ))
              (norm_nonneg (hF z))
        _ ≤ ‖σ‖ * ρ * 2 :=
            mul_le_mul_of_nonneg_left hhFz (by positivity)
    calc ‖(f z - f₀ z) + σ * z * hF z‖
        ≤ ‖f z - f₀ z‖ + ‖σ * z * hF z‖ := norm_add_le _ _
      _ ≤ δ + ‖σ‖ * ρ * 2 := add_le_add (le_of_lt hclose) hszle
      _ = δ + 2 * ‖σ‖ * ρ := by ring
  -- the lower bound `ρ²/8 ≤ ‖z‖ ‖z - σ‖`
  have hden : ρ ^ 2 / 8 ≤ ‖z‖ * ‖z - σ‖ := by
    have h1 : ρ / 2 ≤ ‖z‖ := hz2
    have h2 : ρ / 4 ≤ ‖z - σ‖ := by
      have hns : ‖z‖ - ‖σ‖ ≤ ‖z - σ‖ := norm_sub_norm_le z σ
      linarith
    calc ρ ^ 2 / 8 = (ρ / 2) * (ρ / 4) := by ring
      _ ≤ ‖z‖ * ‖z - σ‖ := mul_le_mul h1 h2 (by linarith) (by positivity)
  have hfin : ‖u z - hF z‖ ≤ 8 * δ / ρ ^ 2 + 16 * ‖σ‖ / ρ := by
    have hρ8 : 0 < ρ ^ 2 / 8 := by positivity
    have h1 : ρ ^ 2 / 8 * ‖u z - hF z‖ ≤ δ + 2 * ‖σ‖ * ρ :=
      le_trans (mul_le_mul_of_nonneg_right hden (norm_nonneg _)) hbound
    have h2 : ‖u z - hF z‖ ≤ (δ + 2 * ‖σ‖ * ρ) / (ρ ^ 2 / 8) := by
      rw [le_div_iff₀ hρ8, mul_comm ‖u z - hF z‖ (ρ ^ 2 / 8)]
      exact h1
    calc ‖u z - hF z‖ ≤ (δ + 2 * ‖σ‖ * ρ) / (ρ ^ 2 / 8) := h2
      _ = 8 * δ / ρ ^ 2 + 16 * ‖σ‖ / ρ := by field_simp; ring
  -- absorb the two terms into `C * (δ/(ρ rr) + ‖σ‖)`
  have hC1 : 8 * δ / ρ ^ 2 ≤ C * (δ / (ρ * rr)) := by
    rw [hCdef]
    have hcoef : (8 : ℝ) / ρ ^ 2 ≤ 16 * (rr + 1) / ρ * (1 / (ρ * rr)) := by
      have e : 16 * (rr + 1) / ρ * (1 / (ρ * rr)) = 16 * (rr + 1) / (ρ ^ 2 * rr) := by
        field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hrr, hρ]
    calc 8 * δ / ρ ^ 2 = δ * (8 / ρ ^ 2) := by ring
      _ ≤ δ * (16 * (rr + 1) / ρ * (1 / (ρ * rr))) :=
          mul_le_mul_of_nonneg_left hcoef (le_of_lt hδpos)
      _ = 16 * (rr + 1) / ρ * (δ / (ρ * rr)) := by ring
  have hC2 : 16 * ‖σ‖ / ρ ≤ C * ‖σ‖ := by
    rw [hCdef]
    have hcoef : (16 : ℝ) / ρ ≤ 16 * (rr + 1) / ρ := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hρ)
      nlinarith [hrr]
    calc 16 * ‖σ‖ / ρ = ‖σ‖ * (16 / ρ) := by ring
      _ ≤ ‖σ‖ * (16 * (rr + 1) / ρ) := mul_le_mul_of_nonneg_left hcoef (norm_nonneg σ)
      _ = 16 * (rr + 1) / ρ * ‖σ‖ := by ring
  calc ‖u z - hF z‖ ≤ 8 * δ / ρ ^ 2 + 16 * ‖σ‖ / ρ := hfin
    _ ≤ C * (δ / (ρ * rr)) + C * ‖σ‖ := add_le_add hC1 hC2
    _ = C * (δ / (ρ * rr) + ‖σ‖) := by ring

end

end Work.Pert.PinLogDev
