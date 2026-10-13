import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

/-! ## The boundary behaviour of the weight `ρ`

`ρ θ = sin θ cos θ sin(2θ)^{-η}` equals `(1/2) sin(2θ)^{1-η}` on the open quadrant, so it
vanishes at both endpoints like `sin(2θ)^{1-η}` with `1 - η > 0`. -/

/-- On the open angular interval `ρ θ = (1/2) sin (2θ)^{1-η}`. -/
theorem wrho_eq_half_sin_rpow (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    wrho η θ = (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_Ioo hθ
  have hsin : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]; ring
  have hrs : (Real.sin (2 * θ)) ^ (1 - η)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-η) := by
    rw [show (1 : ℝ) - η = 1 + (-η) by ring, Real.rpow_add hs, Real.rpow_one]
  unfold wrho
  rw [hsin, hrs]
  ring

/-- `ρ` agrees with `(1/2) sin (2θ)^{1-η}` near `0` from the right. -/
theorem wrho_eventuallyEq_right (η : ℝ) :
    (fun θ : ℝ => wrho η θ) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η)) := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  exact wrho_eq_half_sin_rpow η hθ

/-- `ρ` agrees with `(1/2) sin (2θ)^{1-η}` near `π/2` from the left. -/
theorem wrho_eventuallyEq_left (η : ℝ) :
    (fun θ : ℝ => wrho η θ) =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η)) := by
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
    with θ hθ
  exact wrho_eq_half_sin_rpow η hθ

/-- `ρ θ → 0` as `θ → 0⁺`, for `η < 1`. -/
theorem wrho_tendsto_zero_right (η : ℝ) (hp : 0 < 1 - η) :
    Tendsto (wrho η) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have h : Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_right (1 - η) hp).const_mul (1 / 2 : ℝ)
  exact h.congr' (wrho_eventuallyEq_right η).symm

/-- `ρ θ → 0` as `θ → π/2⁻`, for `η < 1`. -/
theorem wrho_tendsto_zero_left (η : ℝ) (hp : 0 < 1 - η) :
    Tendsto (wrho η) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
  have h : Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - η))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    simpa using (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hp).const_mul (1 / 2 : ℝ)
  exact h.congr' (wrho_eventuallyEq_left η).symm

/-- Squeezing `ρ · f²` against `K² · ρ`, where `f` is eventually bounded by `K` and `ρ → 0`
along the same filter. (No sign restriction on `K` is needed: `‖f θ‖² ≤ K²` follows from
`‖f θ‖ ≤ K` alone, since `‖f θ‖ ≥ 0`.) -/
theorem tendsto_wrho_mul_sq_zero {η K : ℝ} {f : ℝ → ℝ} {L : Filter ℝ}
    (hf : ∀ᶠ θ in L, ‖f θ‖ ≤ K) (hw : Tendsto (wrho η) L (𝓝 0)) :
    Tendsto (fun θ => wrho η θ * (f θ) ^ 2) L (𝓝 0) := by
  have hb : ∀ᶠ θ in L, ‖wrho η θ * (f θ) ^ 2‖ ≤ ‖wrho η θ‖ * K ^ 2 := by
    filter_upwards [hf] with θ hθ
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hθ 2) (norm_nonneg _)
  have hlim : Tendsto (fun θ => ‖wrho η θ‖ * K ^ 2) L (𝓝 0) := by
    simpa using hw.norm.mul_const (K ^ 2)
  exact squeeze_zero_norm' hb hlim

/-- The boundary terms of the two integrations by parts vanish:
`ρ θ · ψ θ ² → 0` and `ρ θ · ψ' θ ² → 0` as `θ → 0⁺` and as `θ → π/2⁻`, where
`ρ θ = sin θ cos θ sin(2θ)^{-η}`, `η ∈ [0,1)`.

Route: first prove `Filter.Tendsto (wrho η) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)` and the
analogue at `π/2` from the left: on a right-neighbourhood of `0` and a left-neighbourhood of
`π/2`, `sin θ cos θ = sin(2θ)/2` and `Real.rpow_add` gives `wrho η θ = (1/2) sin(2θ)^{1-η}`
with `1 - η > 0`, so the claim follows from
`Work.FTS.H2.tendsto_sin_rpow_zero_right (1-η) _` and
`Work.FTS.H2.tendsto_sin_rpow_zero_left (1-η) _` (both in `Submission/Work/FTS/H2/STBasic.lean`)
by `Filter.Tendsto.congr'` (`nhdsWithin` is definitionally `𝓝[·]`, so `congr'`/`mono_left`
suffices; note `Real.pi * 0 = 0`).
Then multiply by the bounded factors `ψ²`, `ψ'²` using `squeeze_zero_norm` with the eventually
valid bound `‖wrho η θ * ψ θ ^ 2‖ ≤ C^2 * ‖wrho η θ‖` (obtained from `hC`, after showing
`0 ≤ C`). -/
theorem wrho_mul_sq_tendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ) (C D : ℝ)
    (hC : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖Work.FTS.EllipticEst.TanTheta.psi u θ‖ ≤ C)
    (hD : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ‖deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ‖ ≤ D) :
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
        * (Work.FTS.EllipticEst.TanTheta.psi u θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
          * (Work.FTS.EllipticEst.TanTheta.psi u θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
      ∧ Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
          * (deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho η θ
          * (deriv (Work.FTS.EllipticEst.TanTheta.psi u) θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp : 0 < 1 - η := by linarith [hη1, hη0]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hψR : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖psi u θ‖ ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hC θ hθ
  have hψL : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)), ‖psi u θ‖ ≤ C := by
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hC θ hθ
  have hdR : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖deriv (psi u) θ‖ ≤ D := by
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact hD θ hθ
  have hdL : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      ‖deriv (psi u) θ‖ ≤ D := by
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    exact hD θ hθ
  exact ⟨tendsto_wrho_mul_sq_zero hψR (wrho_tendsto_zero_right η hp),
    tendsto_wrho_mul_sq_zero hψL (wrho_tendsto_zero_left η hp),
    tendsto_wrho_mul_sq_zero hdR (wrho_tendsto_zero_right η hp),
    tendsto_wrho_mul_sq_zero hdL (wrho_tendsto_zero_left η hp)⟩

end Work.FTS.EllipticEst.TanTheta
