/-
Copyright: work module for the Elgindi finite-time singularity project (Annals 194(3) 2021).

# `L¹ ⊂ H^{-2}` on a space of dimension at most three

The Bessel potential `besselPotential E ℂ (-2)` is the Fourier multiplier with symbol
`ξ ↦ (1 + ‖ξ‖²)^{-1}` (this is `(1 - (2π)^{-2}Δ)^{-1}` in the paper's convention).  If `f` is an
*integrable* function on `E` then the Fourier transform `𝓕 f` is bounded by `‖f‖_{L¹}`, so
`(1 + ‖ξ‖²)^{-1} · 𝓕 f` is dominated by `‖f‖_{L¹} (1 + ‖ξ‖²)^{-1}`; the latter is square
integrable exactly when `finrank ℝ E < 4`, i.e. `finrank ℝ E ≤ 3`.  Since the inverse Fourier
transform is an isometry of `L²`, the distribution `Lp.toTemperedDistribution f` lies in `H^{-2}`.

The two analytic ingredients are, in order:

* `integral_fourier_smul_eq_of_integrable`, self-adjointness of the Fourier transform against a
  merely integrable function (Mathlib's `VectorFourier.integral_bilin_fourierIntegral_eq_flip`);
* `integrable_inv_one_add_norm_sq_sq`, the integrability of `(1+‖x‖²)^{-2}`, which is
  `integrable_rpow_neg_one_add_norm_sq` at `r = 4`.

Everything is `sorry`-free and rests only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap BesselPotentialSpace ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In dimension `≤ 3` the function `(1 + ‖x‖²)^{-2}` is integrable. -/
theorem integrable_inv_one_add_norm_sq_sq (hrank : Module.finrank ℝ E ≤ 3) :
    Integrable (fun x : E => ((1 + ‖x‖ ^ 2) ^ 2 : ℝ)⁻¹) (volume : Measure E) := by
  have hrank4 : ((Module.finrank ℝ E : ℕ) : ℝ) < 4 := by
    have h : ((Module.finrank ℝ E : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hrank
    linarith
  have h := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E)) (r := 4) hrank4
  refine h.congr ?_
  filter_upwards with x
  rw [show (-(4:ℝ)/2) = -2 by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

/-- In dimension `≤ 3` the Bessel weight `ξ ↦ (1 + ‖ξ‖²)^{-1}` (as a complex valued function)
is square integrable. -/
theorem memLp_inv_one_add_norm_sq_sq (hrank : Module.finrank ℝ E ≤ 3) :
    MemLp (fun ξ : E => (((1 + ‖ξ‖ ^ 2 : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ)) 2 (volume : Measure E) := by
  have hnorm : ∀ x : E, ‖(((1 + ‖x‖ ^ 2 : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ)‖ ^ 2
      = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ)⁻¹ := by
    intro x
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [show ((1 + ‖x‖ ^ 2 : ℝ) ^ (-1:ℝ)) = ((1 + ‖x‖ ^ 2 : ℝ))⁻¹ by
      rw [Real.rpow_neg (by positivity), Real.rpow_one]]
    rw [inv_pow]
  have hmeas : AEStronglyMeasurable
      (fun ξ : E => (((1 + ‖ξ‖ ^ 2 : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ)) (volume : Measure E) := by
    refine (show Measurable (fun ξ : E => (((1 + ‖ξ‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) from by
      fun_prop).aestronglyMeasurable.congr ?_
    filter_upwards with ξ
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (integrable_inv_one_add_norm_sq_sq (E := E) hrank).congr ?_
  filter_upwards with x
  exact (hnorm x).symm

/-- **Self-adjointness of the Fourier transform**: for a Schwartz function `ψ` and a merely
integrable function `f`, `∫ 𝓕ψ · f = ∫ ψ · 𝓕f`. -/
theorem integral_fourier_smul_eq_of_integrable {f : E → ℂ} (hf : Integrable f (volume : Measure E))
    (ψ : 𝓢(E, ℂ)) :
    ∫ x, (𝓕 (ψ : E → ℂ)) x • f x = ∫ x, (ψ : E → ℂ) x • 𝓕 f x := by
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext a b; simp [innerₗ_apply_apply]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (𝕜 := ℝ) (V := E) (W := E)
    (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ E)
    (ContinuousLinearMap.lsmul ℂ ℂ) Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (SchwartzMap.integrable ψ) hf
  simp only [ContinuousLinearMap.lsmul_apply] at h
  rw [hflip] at h
  exact h

/-- The Fourier transform of an `L¹` function is bounded, hence an `L^∞` (and in particular
temperate) function. -/
theorem memLp_fourier_of_memLp_one {f : E → ℂ} (hf : MemLp f 1 (volume : Measure E)) :
    MemLp (fun x : E => 𝓕 f x) ⊤ (volume : Measure E) := by
  have h := BoundedContinuousFunction.memLp_top (μ := (volume : Measure E))
    (Real.Lp.fourierTransform (hf.toLp))
  rwa [Real.fourierTransform_toLp hf] at h

/-- **`L¹ ⊆ H^{-2}` in dimension at most three**: the tempered distribution associated with an
integrable function `f` on `E`, `finrank ℝ E ≤ 3`, belongs to the Sobolev space `H^{-2,2}`.

The witness is `𝓕⁻ (g · 𝓕f) ∈ L²`, where `g ξ = (1 + ‖ξ‖²)^{-1}` is the symbol of the Bessel
potential of order `-2`. -/
theorem memSobolev_neg_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hrank : Module.finrank ℝ E ≤ 3)
    {f : E → ℂ} (hf : MeasureTheory.MemLp f 1 (volume : Measure E)) :
    TemperedDistribution.MemSobolev (-2) 2
      (MeasureTheory.Lp.toTemperedDistribution (MeasureTheory.MemLp.toLp f hf)) := by
  have hf_int : Integrable f (volume : Measure E) := memLp_one_iff_integrable.mp hf
  set g : E → ℂ := fun ξ => (((1 + ‖ξ‖ ^ 2 : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ) with hgdef
  have hgt : g.HasTemperateGrowth := by rw [hgdef]; fun_prop
  have hg2 : MemLp g 2 (volume : Measure E) := by
    rw [hgdef]
    exact memLp_inv_one_add_norm_sq_sq (E := E) hrank
  have hFtop : MemLp (fun x : E => 𝓕 (f : E → ℂ) x) ⊤ (volume : Measure E) :=
    memLp_fourier_of_memLp_one hf
  set Φ : E → ℂ := fun x => g x * 𝓕 (f : E → ℂ) x with hΦdef
  have hΦ : MemLp Φ 2 (volume : Measure E) := by
    rw [hΦdef]; exact hg2.mul hFtop
  refine ⟨𝓕⁻ (hΦ.toLp), ?_⟩
  have hkey : smulLeftCLM ℂ g (𝓕 (Lp.toTemperedDistribution (hf.toLp))) = (hΦ.toLp : 𝓢'(E, ℂ)) := by
    ext ψ
    rw [TemperedDistribution.smulLeftCLM_apply_apply, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    simp only [SchwartzMap.fourier_coe]
    have h1 : ∫ x, (𝓕 (SchwartzMap.smulLeftCLM ℂ g ψ : E → ℂ)) x • (↑↑(hf.toLp) : E → ℂ) x
        = ∫ x, (𝓕 (SchwartzMap.smulLeftCLM ℂ g ψ : E → ℂ)) x • f x := by
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with x hx; rw [hx]
    have h2 : ∫ x, (𝓕 (SchwartzMap.smulLeftCLM ℂ g ψ : E → ℂ)) x • f x
        = ∫ x, (SchwartzMap.smulLeftCLM ℂ g ψ : E → ℂ) x • 𝓕 (f : E → ℂ) x :=
      integral_fourier_smul_eq_of_integrable hf_int _
    have h3 : ∫ x, (SchwartzMap.smulLeftCLM ℂ g ψ : E → ℂ) x • 𝓕 (f : E → ℂ) x
        = ∫ x, (ψ : E → ℂ) x • Φ x := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [SchwartzMap.smulLeftCLM_apply_apply hgt ψ x, hΦdef]
      simp only [smul_eq_mul]
      ring
    have h4 : ∫ x, (ψ : E → ℂ) x • (↑↑(hΦ.toLp) : E → ℂ) x = ∫ x, (ψ : E → ℂ) x • Φ x := by
      refine integral_congr_ae ?_
      filter_upwards [hΦ.coeFn_toLp] with x hx; rw [hx]
    rw [h1, h2, h3]
    exact h4.symm
  have hb : besselPotential E ℂ (-2) (Lp.toTemperedDistribution (hf.toLp))
      = 𝓕⁻ (smulLeftCLM ℂ g (𝓕 (Lp.toTemperedDistribution (hf.toLp)))) := by
    have hfun : (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ ((-2:ℝ)/2) : ℝ) : ℂ)) = g := by
      rw [hgdef]; funext ξ
      rw [show ((-2:ℝ)/2) = -1 by norm_num]
    show fourierMultiplierCLM ℂ (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ ((-2:ℝ)/2) : ℝ) : ℂ))
        (Lp.toTemperedDistribution (hf.toLp)) =
      𝓕⁻ (smulLeftCLM ℂ g (𝓕 (Lp.toTemperedDistribution (hf.toLp))))
    rw [hfun]
    rfl
  rw [hb, hkey]
  exact Lp.fourierInv_toTemperedDistribution_eq hΦ.toLp

end Work.EllipticEst.InteriorRegularity
