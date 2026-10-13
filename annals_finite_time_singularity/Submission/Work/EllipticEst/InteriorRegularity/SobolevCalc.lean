/-
Copyright: work module for the Elgindi finite-time singularity project.

# Fourier--Sobolev calculus for the interior-regularity development

This module collects the *generic* (project-independent) analytic facts about Mathlib's
Sobolev spaces `TemperedDistribution.MemSobolev` (Bessel potential spaces) that the
interior-smoothness proof of `bslOp_interiorSmooth` needs.  Everything here is stated for a
finite-dimensional real inner product space `E`; the applications take `E = ℝ × ℝ`.

The main result of this file is the **gain-two lemma for the Laplacian**:

`u ∈ H^s` and `Δ u ∈ H^s` imply `u ∈ H^{s+2}`,

proved purely by manipulating the Fourier multipliers `besselPotential` and the explicit
identity `besselPotential (-2) (Δ u) = -(2π)² • (‖x‖²/(1+‖x‖²)) • u` up to the elementary
decomposition `(1+‖x‖²)^{(s+2)/2} = (1+‖x‖²)^{s/2} + (1+‖x‖²)^{s/2}·‖x‖²`.

Everything is `sorry`-free and rests only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Laplacian LineDeriv
open scoped SchwartzMap BesselPotentialSpace ENNReal Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.EllipticEst.InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `w s x = (1 + ‖x‖^2)^(s/2)` as a complex valued function: the symbol of the Bessel
potential of order `s`. -/
def w (s : ℝ) : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)

/-- The multiplier `x ↦ ‖x‖^2` (the symbol of `-Δ/(2π)^2`). -/
def tt : E → ℂ := fun x => ((‖x‖ ^ 2 : ℝ) : ℂ)

theorem w_temperate (s : ℝ) : (w (E := E) s).HasTemperateGrowth := by
  unfold w; fun_prop

theorem tt_temperate : (tt (E := E)).HasTemperateGrowth := by
  unfold tt; fun_prop

theorem w_mul_tt_temperate (s : ℝ) : (w (E := E) s * tt).HasTemperateGrowth := by
  unfold w tt; fun_prop

/-- The elementary decomposition `(1+t)^{(s+2)/2} = (1+t)^{s/2} + (1+t)^{s/2}·t`. -/
theorem w_add_two (s : ℝ) : w (E := E) (s+2) = w (E := E) s + w (E := E) s * tt := by
  funext x
  unfold w tt
  simp only [Pi.add_apply, Pi.mul_apply]
  have h1 : (0:ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rw [show (s+2)/2 = s/2 + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  push_cast
  ring

/-- The Fourier transform commutes with Fourier multipliers, on the Fourier side. -/
theorem fourier_mult (g : E → ℂ) (u : 𝓢'(E, ℂ)) :
    𝓕 (fourierMultiplierCLM ℂ g u) = smulLeftCLM ℂ g (𝓕 u) := by
  rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq]

/-- `besselPotential` is the Fourier multiplier with the symbol `w s`. -/
theorem bessel_eq (s : ℝ) (u : 𝓢'(E, ℂ)) :
    besselPotential E ℂ s u = fourierMultiplierCLM ℂ (w (E := E) s) u := rfl

/-- The Fourier transform of the Laplacian as a multiplier. -/
theorem fourier_laplacian (u : 𝓢'(E, ℂ)) :
    𝓕 (Δ u) = (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) • smulLeftCLM ℂ (tt (E := E)) (𝓕 u) := by
  have hlap : Δ u = (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) • fourierMultiplierCLM ℂ (tt (E := E)) u := by
    rw [laplacian_eq_fourierMultiplierCLM, ← Complex.coe_smul]
    rfl
  rw [hlap, fourier_smul, fourier_mult]

/-- **Gain-two lemma for the Laplacian.**  If `u ∈ H^s` and `Δ u ∈ H^s` then `u ∈ H^{s+2}`.

This is the constant-coefficient elliptic estimate, in the Bessel-potential (Fourier)
formulation; it is proved by splitting the symbol of the Bessel potential of order `s+2`. -/
theorem gain_two (s : ℝ) (u : 𝓢'(E, ℂ))
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) :
    MemSobolev (s+2) 2 u := by
  obtain ⟨v, hv⟩ := (memSobolev_iff_exists_smulLeftCLM_fourier (F := ℂ)).mp hu
  obtain ⟨v', hv'⟩ := (memSobolev_iff_exists_smulLeftCLM_fourier (F := ℂ)).mp hΔ
  have hv2 : smulLeftCLM ℂ (w (E := E) s) (𝓕 u) = Lp.toTemperedDistribution v := hv
  have hv2' : smulLeftCLM ℂ (w (E := E) s) (𝓕 (Δ u)) = Lp.toTemperedDistribution v' := hv'
  set c : ℂ := (((-(2 * π : ℝ) ^ 2 : ℝ)) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]; push_cast; simp [Real.pi_ne_zero]
  have h3 : 𝓕 (Δ u) = c • smulLeftCLM ℂ (tt (E := E)) (𝓕 u) := fourier_laplacian u
  have h4 : smulLeftCLM ℂ (w (E := E) s * tt) (𝓕 u) = c⁻¹ • Lp.toTemperedDistribution v' := by
    have h2' := hv2'
    rw [h3, ContinuousLinearMap.map_smul,
      smulLeftCLM_smulLeftCLM_apply (tt_temperate) (w_temperate s)] at h2'
    rw [mul_comm (tt (E := E)) (w (E := E) s)] at h2'
    rw [← h2', smul_smul, inv_mul_cancel₀ hcne, one_smul]
  refine ⟨𝓕⁻ v + c⁻¹ • 𝓕⁻ v', ?_⟩
  show fourierMultiplierCLM ℂ (w (E := E) (s+2)) u = Lp.toTemperedDistribution _
  rw [fourierMultiplierCLM_apply, w_add_two s,
    smulLeftCLM_add (w_temperate s) (w_mul_tt_temperate s), add_apply, hv2, h4]
  rw [fourierInv_add, fourierInv_smul,
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq,
    MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq]
  rw [← MeasureTheory.Lp.toTemperedDistributionCLM_apply (f := 𝓕⁻ v + c⁻¹ • 𝓕⁻ v'),
    map_add, map_smul,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistributionCLM_apply]

end Work.EllipticEst.InteriorRegularity
