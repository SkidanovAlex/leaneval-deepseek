/-
Copyright: work module for the Elgindi finite-time singularity project.

# The flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` vanishes at both endpoints

This file proves that the primitive of the Hardy argument

  `hardyFtsFlux η f θ = f θ² · cos(2θ) · sin(2θ)^{-(1+η)}`

(documented in `Submission/Work/FTS/EllipticEst/AngAWeakFts/Defs.lean`) tends to `0` at `0⁺`
and at `(π/2)⁻`, under the only hypothesis

  `|f θ| ≤ M sin(2θ)` on `(0, π/2)`

and `η < 1`.  Indeed `|f θ|² ≤ M² sin(2θ)²`, `|cos(2θ)| ≤ 1`, so

  `|Φ θ| ≤ M² sin(2θ)^{1-η}`,

and `1 - η > 0` makes the right hand side tend to `0` at both endpoints (the `rpow` factor is
the only content: `sin(2θ) → 0` through positive values, and `x ↦ x^p` is continuous at `0`
with value `0` for `p > 0`).

The two endpoint statements `tendsto_sin_two_rpow_zero_right` / `_left` are proved here from
Mathlib directly (they are also available, in the same namespace `Work.FTS.H2`, in
`Submission/Work/FTS/H2/STBasic.lean`), so that this file depends on `Defs.lean` alone.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeakFts

open Work.FTS.EllipticEst.AngAWeak

/-! ## The two elementary endpoint limits -/

/-- `θ ↦ sin(2θ)^p → 0` as `θ → 0⁺`, for `p > 0`.  The proof composes the two facts that
`sin(2θ) → 0` through *positive* values and that `x ↦ x^p` is continuous at `0` with value
`0`. -/
theorem tendsto_sin_two_rpow_zero_right (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsin : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h2 : Tendsto (fun θ : ℝ => 2 * θ) (𝓝 (0 : ℝ)) (𝓝 (2 * (0 : ℝ))) :=
        tendsto_const_nhds.mul tendsto_id
      have h3 : Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (𝓝 (0 : ℝ))
          (𝓝 (Real.sin (2 * (0 : ℝ)))) :=
        Real.continuous_sin.continuousAt.tendsto.comp h2
      simpa using h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi / 4 by positivity)] with θ hθ
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hr : Tendsto (fun x : ℝ => x ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ p) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ p)) :=
      (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow (ne_of_gt hp)] using h
  exact hr.comp hsin

/-- `θ ↦ sin(2θ)^p → 0` as `θ → (π/2)⁻`, for `p > 0`, by transport along `θ ↦ π/2 - θ`
and `sin(π - x) = sin x`. -/
theorem tendsto_sin_two_rpow_zero_left (p : ℝ) (hp : 0 < p) :
    Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hcomp : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝[<] (Real.pi / 2))
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h3 : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
      simpa using h3.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      show (0 : ℝ) < Real.pi / 2 - θ
      have := Set.mem_Iio.mp hθ
      linarith
  refine ((tendsto_sin_two_rpow_zero_right p hp).comp hcomp).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ _
  simp only [Function.comp_apply]
  rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-! ## The pointwise bound -/

/-- The pointwise estimate behind the flux vanishing: `|Φ θ| ≤ M² sin(2θ)^{1-η}` on the open
angular interval.  Only `|f θ| ≤ M sin(2θ)` and `|cos| ≤ 1` are used, together with the `rpow`
addition rule `sin(2θ)² · sin(2θ)^{-(1+η)} = sin(2θ)^{1-η}`. -/
theorem hardyFtsFlux_abs_le {η M : ℝ} (_hM : 0 ≤ M) {f : ℝ → ℝ}
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |hardyFtsFlux η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (1 - η) := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  have hspos : 0 ≤ Real.sin (2 * θ) := hs.le
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hf : |f θ| ≤ M * Real.sin (2 * θ) := hMf θ hθ
  have hf2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hf 2
    rwa [sq_abs] at h
  have hrpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + η)) := Real.rpow_nonneg hspos _
  have hkey : (Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(1 + η))
      = (Real.sin (2 * θ)) ^ (1 - η) := by
    rw [← Real.rpow_add hs, show (2 : ℝ) + (-(1 + η)) = 1 - η by ring]
  calc |hardyFtsFlux η f θ|
      = (f θ) ^ 2 * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η)) := by
        rw [hardyFtsFlux, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
          abs_of_nonneg hrpow_nn]
    _ ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hf2 hcos (abs_nonneg _) (sq_nonneg _)) hrpow_nn
    _ = M ^ 2 * ((Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(1 + η))) := by
        rw [mul_pow, Real.rpow_two]; ring
    _ = M ^ 2 * (Real.sin (2 * θ)) ^ (1 - η) := by rw [hkey]

/-- The flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}` tends to `0` at `0⁺` and at `(π/2)⁻`,
for `η < 1` and `|f θ| ≤ M sin(2θ)` on the open angular interval. -/
theorem fluxTendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp : 0 < 1 - η := by linarith
  have hhalf : (0 : ℝ) < Real.pi / 2 := by positivity
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun t => M ^ 2 * (Real.sin (2 * t)) ^ (1 - η))
      (Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hhalf] with θ hθ
      rw [Real.norm_eq_abs]
      exact hardyFtsFlux_abs_le hM hMf θ hθ
    · simpa using ((tendsto_sin_two_rpow_zero_right (1 - η) hp).const_mul (M ^ 2))
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun t => M ^ 2 * (Real.sin (2 * t)) ^ (1 - η))
      (Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hhalf] with θ hθ
      rw [Real.norm_eq_abs]
      exact hardyFtsFlux_abs_le hM hMf θ hθ
    · simpa using ((tendsto_sin_two_rpow_zero_left (1 - η) hp).const_mul (M ^ 2))

end Work.FTS.EllipticEst.AngAWeakFts

end
