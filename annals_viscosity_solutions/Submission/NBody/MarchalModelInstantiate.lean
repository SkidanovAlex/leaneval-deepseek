import Submission.NBody.MarchalModelPotential
import Submission.Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict

/-!
# Discharging the potential bound of the model negativity

`Submission.NBody.exists_model_dir_negative` requires, for every `ρ ∈ (0, ρmax)`, the two
hypotheses

* `hpot` — the bound on the `θ`-average of the model potential term, and
* `hpotint` — the `θ`-integrability of the model potential term.

`hpotint` is `intervalIntegrable_modelPotVal_circle` (a finite sum of the commons
`intervalIntegrable_circle_gain`).  `hpot` is `circleAvg_modelPotVal_bound`, whose hypothesis
`hpj` — one bound per pair `(i₀,j)` — is *literally* the conclusion of the commons lemma
`Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict`, instantiated at
`xi := sbar i₀ - sbar j`, `c := √κ`, `z := ‖sbar i₀ - sbar j‖`.  This file performs that
instantiation.

The smallness hypothesis `hsmall` of the commons lemma,
`ρ / (√κ (T-ρ)^{2/3} ‖xi‖) ≤ 1/8`, is obtained by taking `ρ ≤ ρmax` with `ρmax` chosen small
(and `ρmax ≤ T/2`, so that `(T-ρ)^{2/3} ≥ (T/2)^{2/3}`).
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- Monotonicity of `ρ ↦ ρ / (c (T-ρ)^{2/3} z)` on `(0, T/2]`. -/
lemma div_le_div_ramp {c T ρ ρmax z : ℝ} (hc : 0 < c) (hT : 0 < T) (hρ : 0 < ρ)
    (hρmax : 0 < ρmax) (hρρ : ρ ≤ ρmax) (hρmaxT : ρmax ≤ T / 2) (hz : 0 < z) :
    ρ / (c * (T - ρ) ^ ((2:ℝ)/3) * z) ≤ ρmax / (c * (T / 2) ^ ((2:ℝ)/3) * z) := by
  have hρT : ρ ≤ T / 2 := le_trans hρρ hρmaxT
  have hb : 0 < c * (T - ρ) ^ ((2:ℝ)/3) * z := by
    have h1 : 0 < T - ρ := by linarith
    exact mul_pos (mul_pos hc (Real.rpow_pos_of_pos h1 _)) hz
  have hd : 0 < c * (T / 2) ^ ((2:ℝ)/3) * z :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos (by linarith) _)) hz
  rw [div_le_div_iff₀ hb hd]
  have hrpow : (T / 2) ^ ((2:ℝ)/3) ≤ (T - ρ) ^ ((2:ℝ)/3) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h2 : ρ * (T / 2) ^ ((2:ℝ)/3) ≤ ρmax * (T - ρ) ^ ((2:ℝ)/3) := by
    calc ρ * (T / 2) ^ ((2:ℝ)/3) ≤ ρmax * (T / 2) ^ ((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_right hρρ (Real.rpow_nonneg (by linarith) _)
      _ ≤ ρmax * (T - ρ) ^ ((2:ℝ)/3) := mul_le_mul_of_nonneg_left hrpow hρmax.le
  calc ρ * (c * (T / 2) ^ ((2:ℝ)/3) * z)
      = c * z * (ρ * (T / 2) ^ ((2:ℝ)/3)) := by ring
    _ ≤ c * z * (ρmax * (T - ρ) ^ ((2:ℝ)/3)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hc.le hz.le)
    _ = ρmax * (c * (T - ρ) ^ ((2:ℝ)/3) * z) := by ring

/-- **The model negativity with the potential bound discharged.**  All the hypotheses of
`exists_model_dir_negative` are produced from the blow-up data: `hpot` by the commons lemma
`integral_theta_model_potential_realpow_le_strict` and `hpotint` by
`intervalIntegrable_modelPotVal_circle`. -/
theorem exists_model_dir_negative_of_blowup {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) (hne : (k.erase i₀).Nonempty)
    {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) (sbar : EN E N) (e f : E) (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    {ρmax : ℝ} (hρmax : 0 < ρmax) (hρmaxT : ρmax ≤ T / 2)
    (hz : ∀ j ∈ k.erase i₀, 0 < ‖sbar i₀ - sbar j‖)
    (hsmallmax : ∀ j ∈ k.erase i₀,
      ρmax / (Real.sqrt κ * (T / 2) ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖) ≤ 1/8) :
    ∃ ρ > (0:ℝ), ∃ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ) < 0 := by
  have hκpos : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hT2 : 0 < T / 2 := by linarith
  -- the potential bound `hpot`
  have hpot : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)
          ≤ - potGainA m k i₀ κ sbar * ρ ^ ((1:ℝ)/2) + potGainB m k i₀ κ T sbar * ρ ^ 2 := by
    intro ρ hρ
    have hρpos : 0 < ρ := hρ.1
    have hρT2 : ρ ≤ T / 2 := le_trans hρ.2.le hρmaxT
    have hρT : ρ < T := by linarith
    refine circleAvg_modelPotVal_bound hm hκ hT hρpos hρT2 sbar e f he hf hef hz ?_
    intro j hj
    have hzj : 0 < ‖sbar i₀ - sbar j‖ := hz j hj
    -- the commons lemma at `c = √κ`, `z = ‖sbar i₀ - sbar j‖`
    have hsmall : ρ / (Real.sqrt κ * (T - ρ) ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖) ≤ 1/8 :=
      le_trans (div_le_div_ramp hκpos hT hρpos hρmax hρ.2.le hρmaxT hzj)
        (hsmallmax j hj)
    have hcomm := Commons.Analysis.Integral.integral_theta_model_potential_realpow_le_strict
      (E := E) e f (sbar i₀ - sbar j) he hf hef (c := Real.sqrt κ) (T := T) (ρ := ρ)
      (z := ‖sbar i₀ - sbar j‖) hκpos hT hρpos hρT rfl hzj hsmall
    refine circleAvg_potPairVal_le hρpos he hf hef rfl ?_
    rw [phiWeight]
    exact hcomm
  -- the θ-integrability `hpotint`
  have hpotint : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      IntervalIntegrable (fun θ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        volume 0 (2*Real.pi) :=
    fun ρ hρ => intervalIntegrable_modelPotVal_circle hκ hT hρ.1 sbar e f he hf hef
  refine exists_model_dir_negative hm hi₀ hκ hT sbar e f he hf hef
    (A := potGainA m k i₀ κ sbar) (B := potGainB m k i₀ κ T sbar)
    (potGainA_pos hm hκ sbar hne hz) (potGainB_nonneg hm hκ hT sbar) hρmax hρmaxT hpot hpotint

end Submission.NBody
