import Submission.NBody.MarchalModelInstantiate
import Submission.NBody.MarchalStdVarGeometry
import Submission.NBody.MarchalModelKinetic
import Submission.NBody.MarchalBumpIntegrable

/-!
# The transfer glue: `modelDiff δ` is the limit integrand of the transfer

`tendsto_transfer_of_data` (FT's `propo:blowup`) states that the rescaled Lagrangian difference
`∫₀^T (massInner m (q^λ)' f' + ½‖f'‖² + U_k(q^λ + f) - U_k(q^λ))` converges, as `λ → 0⁺`, to the
**same expression with `q^λ` replaced by the blow-up profile `q̄`**.

For the standard variation `f = stdVarVec m k i₀ δ T` (whose derivative is supported on the ramp),
that limit is exactly `modelDiff m k i₀ κ sbar T δ`:  the cross term is `modelCrossVal`, the quadratic
term is `modelQuadVal`, and the potential term is `modelPotVal` (which equals the integral of the
genuine cluster-potential difference, by `modelPotVal_eq_integral_clusterPotential`).

This file proves that identity (the "transfer glue"): it is a splitting of the single integral into
the sum of the three defining integrals, using the three interval-integrability facts.
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

/-- The coordinates of the blow-up profile differ by the rescaled separation (a local copy, since
the original in `MarchalModelPotential` is private). -/
private lemma blowUpProfile_pair_sub' (κ : ℝ) (sbar : EN E N) (t : ℝ) (i₀ j : Fin N) :
    (blowUpProfile κ sbar t).ofLp i₀ - (blowUpProfile κ sbar t).ofLp j
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar.ofLp i₀ - sbar.ofLp j) := by
  rw [blowUpProfile, PiLp.smul_apply, PiLp.smul_apply, smul_sub]

private lemma norm_smul_mul_nonneg' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : E) :
    ‖(a * b) • x‖ = a * b * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hb)]

/-! ## The splitting of the single integral -/

/-- **The splitting identity.**  An interval integral of a sum of three terms is the sum of the
three interval integrals. -/
theorem integral_lagrange_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} {T : ℝ}
    (q : ℝ → EN E N)
    (hA : IntervalIntegrable (fun s : ℝ => massInner m (deriv q s)
      (deriv (stdVarVec m k i₀ δ T) s)) volume 0 T)
    (hB : IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      volume 0 T)
    (hC : IntervalIntegrable (fun s : ℝ => clusterPotential m k (q s + stdVarVec m k i₀ δ T s)
      - clusterPotential m k (q s)) volume 0 T) :
    (∫ s in (0:ℝ)..T, (massInner m (deriv q s) (deriv (stdVarVec m k i₀ δ T) s)
        + (1/2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
        + clusterPotential m k (q s + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (q s)))
      = (∫ s in (0:ℝ)..T, massInner m (deriv q s) (deriv (stdVarVec m k i₀ δ T) s))
        + (1/2) * (∫ s in (0:ℝ)..T, ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        + (∫ s in (0:ℝ)..T, (clusterPotential m k (q s + stdVarVec m k i₀ δ T s)
            - clusterPotential m k (q s))) := by
  have hpt : (fun s : ℝ => massInner m (deriv q s) (deriv (stdVarVec m k i₀ δ T) s)
        + (1/2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
        + clusterPotential m k (q s + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (q s))
      = fun s => (massInner m (deriv q s) (deriv (stdVarVec m k i₀ δ T) s)
          + (1/2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
          + (clusterPotential m k (q s + stdVarVec m k i₀ δ T s)
              - clusterPotential m k (q s)) := by
    funext s; ring
  rw [hpt]
  rw [intervalIntegral.integral_add (μ := volume) (hA.add (hB.const_mul (1/2))) hC]
  rw [intervalIntegral.integral_add (μ := volume) hA (hB.const_mul (1/2))]
  rw [intervalIntegral.integral_const_mul]

/-! ## The three interval-integrability facts for the model -/

/-- The quadratic term `‖f'‖_[m]²` of the standard variation is interval integrable (the derivative
is concentrated on the ramp, where it is bounded). -/
theorem intervalIntegrable_deriv_stdVarVec_sq {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      volume (0:ℝ) T := by
  set A : ℝ := ‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹ with hA
  have hAnn : 0 ≤ A := mul_nonneg (weightedNorm_nonneg m _) (inv_nonneg.mpr (norm_nonneg δ))
  have hmaj : IntervalIntegrable (fun _ : ℝ => A ^ 2) volume (0:ℝ) T := intervalIntegrable_const
  refine hmaj.mono_fun' ?_ ?_
  · have hco : Continuous (fun v : EN E N => ‖v‖_[m] ^ 2) := (continuous_weightedNorm' m).pow 2
    exact (hco.measurable.comp (measurable_deriv _)).aestronglyMeasurable
  · have hae := deriv_stdVarVec_ae m k i₀ δ T hδ
    rw [Set.uIoc_of_le hT]
    filter_upwards [hae] with s hs
    rw [hs, Real.norm_eq_abs, hA, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (weightedNorm_nonneg m _)
      (weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T s) 2

/-- The cross term `massInner (deriv q̄) f'` of the blow-up profile is interval integrable: the
blow-up velocity grows like `t^{-1/3}` and the derivative of the standard variation is bounded. -/
theorem intervalIntegrable_massInner_blowUp_deriv_stdVarVec {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0) {κ T : ℝ} (hκ : 0 < κ)
    (hT : 0 ≤ T) (sbar : EN E N) :
    IntervalIntegrable (fun s : ℝ => massInner m (deriv (blowUpProfile κ sbar) s)
      (deriv (stdVarVec m k i₀ δ T) s)) volume (0:ℝ) T := by
  set A : ℝ := ‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹ with hA
  set K : ℝ := (2/3) * Real.sqrt κ * ‖sbar‖_[m] * A with hK
  have hmaj : IntervalIntegrable (fun s : ℝ => K * s ^ (-(1:ℝ)/3)) volume (0:ℝ) T :=
    (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := T) (r := -(1:ℝ)/3)
      (by norm_num)).const_mul K
  refine hmaj.mono_fun' ?_ ?_
  · have hco : Continuous (fun p : EN E N × EN E N => massInner m p.1 p.2) := by
      unfold massInner
      fun_prop
    exact (hco.measurable.comp ((measurable_deriv _).prodMk (measurable_deriv _))).aestronglyMeasurable
  · have hae := deriv_stdVarVec_ae m k i₀ δ T hδ
    rw [Set.uIoc_of_le hT]
    filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs hsIoc
    rw [hs, Real.norm_eq_abs, hK, hA]
    have hs0 : 0 < s := hsIoc.1
    have h1 : ‖deriv (blowUpProfile κ sbar) s‖_[m]
        = (2/3) * Real.sqrt κ * s ^ (-(1:ℝ)/3) * ‖sbar‖_[m] := by
      rw [deriv_blowUpProfile κ sbar hs0]
      rw [weightedNorm_smul (fun i => (hm i).le),
        abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg κ))
          (Real.rpow_nonneg hs0.le _))]
    calc |massInner m (deriv (blowUpProfile κ sbar) s) (stdVarVecDeriv m k i₀ δ T s)|
        ≤ ‖deriv (blowUpProfile κ sbar) s‖_[m] * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] :=
          abs_massInner_le_weightedNorm_mul m (fun i => (hm i).le) _ _
      _ ≤ ((2/3) * Real.sqrt κ * s ^ (-(1:ℝ)/3) * ‖sbar‖_[m])
            * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left
            (weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T s)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg κ))
              (Real.rpow_nonneg hs0.le _)) (weightedNorm_nonneg m _))
      _ = (2/3) * Real.sqrt κ * ‖sbar‖_[m] * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹)
            * s ^ (-(1:ℝ)/3) := by ring

/-- The potential difference of the symmetric bump is interval integrable as soon as each pair term
is. -/
theorem intervalIntegrable_clusterPotential_bump_diff {m : Fin N → ℝ} {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hT : 0 ≤ T) (sbar : EN E N) (δ : E)
    (hint : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T) :
    IntervalIntegrable (fun t : ℝ =>
      clusterPotential m k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (blowUpProfile κ sbar t)) volume (0:ℝ) T := by
  have hint' : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖blowUpProfile κ sbar t i₀ - blowUpProfile κ sbar t j + stdVar δ T t‖)⁻¹
        - (‖blowUpProfile κ sbar t i₀ - blowUpProfile κ sbar t j‖)⁻¹) volume (0:ℝ) T := by
    intro j hj
    refine (hint j hj).congr_ae ?_
    rw [Set.uIoc_of_le hT]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [blowUpProfile_pair_sub' κ sbar t i₀ j,
      norm_smul_mul_nonneg' (Real.sqrt_nonneg κ) (Real.rpow_nonneg ht.1.le _)]
  refine IntervalIntegrable.congr (f := fun t : ℝ => ∑ j ∈ k.erase i₀, m i₀ * m j *
      ((‖blowUpProfile κ sbar t i₀ - blowUpProfile κ sbar t j + stdVar δ T t‖)⁻¹
        - (‖blowUpProfile κ sbar t i₀ - blowUpProfile κ sbar t j‖)⁻¹)) ?_ ?_
  · intro t ht
    rw [Set.uIoc_of_le hT] at ht
    rw [stdVarVec_eq_stdPert]
    exact (clusterPotential_bump_diff m k hi₀ (blowUpProfile κ sbar t) δ T t).symm
  · refine (IntervalIntegrable.sum (k.erase i₀) fun j hj =>
        (hint' j hj).const_mul (m i₀ * m j)).congr ?_
    intro t _
    simp only [Finset.sum_apply]

/-! ## The glue -/

/-- **The transfer glue.**  `modelDiff δ` is the integrand of the transfer limit. -/
theorem modelDiff_eq_transfer_integrand {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T)
    (sbar : EN E N) {δ : E} (hδ : δ ≠ 0)
    (hint : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
      (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
        - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T) :
    modelDiff m k i₀ κ sbar T δ
      = ∫ s in (0:ℝ)..T, (massInner m (deriv (blowUpProfile κ sbar) s)
          (deriv (stdVarVec m k i₀ δ T) s)
        + (1/2) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2
        + clusterPotential m k (blowUpProfile κ sbar s + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (blowUpProfile κ sbar s)) := by
  have hpot := modelPotVal_eq_integral_clusterPotential (m := m) (k := k) (i₀ := i₀) hi₀ hT
    sbar δ hint
  have hpm : modelPotVal m k i₀ κ sbar T δ
      = ∫ t in (0:ℝ)..T, (clusterPotential m k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t)
          - clusterPotential m k (blowUpProfile κ sbar t)) := by
    rw [modelPotVal]
    exact hpot.symm
  rw [modelDiff, modelCrossVal, modelQuadVal, hpm, intervalIntegral.integral_const_mul]
  exact (integral_lagrange_eq (m := m) (k := k) (i₀ := i₀) (δ := δ) (T := T)
    (blowUpProfile κ sbar)
    (intervalIntegrable_massInner_blowUp_deriv_stdVarVec hm hδ hκ hT sbar)
    (intervalIntegrable_deriv_stdVarVec_sq hm hδ hT)
    (intervalIntegrable_clusterPotential_bump_diff hi₀ hT sbar δ hint)).symm

end Submission.NBody
