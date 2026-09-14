import Submission.NBody.MarchalModelNegative
import Submission.NBody.MarchalBumpPotential
import Submission.Commons.Analysis.Integral.intervalIntegrable_circle_gain
import Submission.Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg

/-!
# The model potential term as a pair sum

`modelPotVal` (in `Submission.NBody.MarchalModelNegative`) is *defined* as the sum, over the pairs
`(i₀,j)` of the cluster, of the single-pair model potential gain `potPairVal`.  This file proves
that it agrees with the integral of the genuine cluster-potential difference
`∫_0^T (U_k(q̄ t + v(t)) - U_k(q̄ t)) dt` — the form needed for the transfer
(`Submission.NBody.tendsto_transfer_of_data`).

The equality needs the interval-integrability of the individual pair terms (which holds for every
direction `δ` that is not a "collision direction"; see `Submission/ROADMAP.md` §SESSION 35.4).
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

/-- The `(i₀,j)` term of the cluster-potential difference of the blow-up profile, as a function
of the rescaled time. -/
private lemma blowUpProfile_pair_sub (κ : ℝ) (sbar : EN E N) (t : ℝ) (i₀ j : Fin N) :
    (blowUpProfile κ sbar t).ofLp i₀ - (blowUpProfile κ sbar t).ofLp j
      = (Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar.ofLp i₀ - sbar.ofLp j) := by
  rw [blowUpProfile, PiLp.smul_apply, PiLp.smul_apply, smul_sub]

private lemma norm_smul_mul_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : E) :
    ‖(a * b) • x‖ = a * b * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hb)]

/-- **The model potential term is the integral of the genuine cluster-potential difference.**
Equivalently, the pair sum defining `modelPotVal` is the (a.e. identical) expansion of
`clusterPotential_bump_diff`. -/
theorem modelPotVal_eq_integral_clusterPotential {m : Fin N → ℝ} {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hT : 0 ≤ T) (sbar : EN E N) (δ : E)
    (hint : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun t : ℝ =>
        (‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
          - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) volume 0 T) :
    (∫ t in (0:ℝ)..T, (clusterPotential m k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (blowUpProfile κ sbar t)))
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T δ := by
  have hpt : ∀ t : ℝ, 0 ≤ t →
      clusterPotential m k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (blowUpProfile κ sbar t)
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          ((‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
            - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) := by
    intro t ht
    rw [← stdPert_eq_stdVarVec m k i₀ δ T,
      clusterPotential_bump_diff m k hi₀ (blowUpProfile κ sbar t) δ T t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blowUpProfile_pair_sub κ sbar t i₀ j,
      norm_smul_mul_nonneg (Real.sqrt_nonneg κ) (Real.rpow_nonneg ht _)]
  have h1 : (∫ t in (0:ℝ)..T, (clusterPotential m k (blowUpProfile κ sbar t + stdVarVec m k i₀ δ T t)
        - clusterPotential m k (blowUpProfile κ sbar t)))
      = ∫ t in (0:ℝ)..T, ∑ j ∈ k.erase i₀, m i₀ * m j *
          ((‖(Real.sqrt κ * t ^ ((2:ℝ)/3)) • (sbar i₀ - sbar j) + stdVar δ T t‖)⁻¹
            - (Real.sqrt κ * t ^ ((2:ℝ)/3) * ‖sbar i₀ - sbar j‖)⁻¹) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT]
    filter_upwards with t ht
    exact hpt t ht.1.le
  rw [h1]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_const_mul]
    rfl
  · intro j hj
    exact (hint j hj).const_mul (m i₀ * m j)


/-! ## The circle average of the potential term -/

section Circle

variable {κ ρ : ℝ} {sbar : EN E N}

private lemma stdCoef_circleDir_mul {ρ T t : ℝ} (hρ : 0 < ρ) {e f : E} (θ : ℝ)
    (hef : ‖circleDir e f θ‖ = 1) :
    stdCoef (ρ • circleDir e f θ) T t * ρ = min ρ (max 0 (T - t)) := by
  have h2 : ρ * ((T - t) / ρ) = T - t := by rw [mul_comm, div_mul_cancel₀ (T - t) hρ.ne']
  have h1 : ρ * min 1 (max 0 ((T - t) / ρ)) = min ρ (max 0 (T - t)) := by
    rw [mul_min_of_nonneg (a := ρ) 1 (max 0 ((T - t) / ρ)) hρ.le, mul_one,
      mul_max_of_nonneg (a := ρ) 0 ((T - t) / ρ) hρ.le, mul_zero, h2]
  rw [stdCoef_smul_norm_one hρ hef, mul_comm, h1]

/-- The standard variation of the perturbation `ρ • circleDir e f θ`, as a function of the rescaled
time. -/
lemma stdVar_circleDir {ρ T : ℝ} (hρ : 0 < ρ) {e f : E} (θ : ℝ)
    (hef : ‖circleDir e f θ‖ = 1) (t : ℝ) :
    stdVar (ρ • circleDir e f θ) T t = (min ρ (max 0 (T - t))) • circleDir e f θ := by
  rw [stdVar, smul_smul, stdCoef_circleDir_mul (T := T) hρ θ hef]

/-- The single-pair model potential gain, evaluated at a displacement on the circle of radius `ρ`. -/
lemma potPairVal_circle {xi : E} {c T : ℝ} (hρ : 0 < ρ) {e f : E} (θ : ℝ)
    (hef : ‖circleDir e f θ‖ = 1) :
    potPairVal xi c T (ρ • circleDir e f θ)
      = ∫ t in (0:ℝ)..T, ((‖(c * t ^ ((2:ℝ)/3)) • xi
            + (min ρ (max 0 (T - t))) • circleDir e f θ‖)⁻¹
          - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹) := by
  rw [potPairVal]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [stdVar_circleDir (T := T) hρ θ hef (t := t)]

/-- The circle-integrability of the single-pair model potential gain (from the commons lemma
`Commons.Analysis.Integral.intervalIntegrable_circle_gain`). -/
lemma intervalIntegrable_potPairVal_circle {xi : E} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hρ : 0 < ρ) (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    IntervalIntegrable (fun θ : ℝ => potPairVal xi c T (ρ • circleDir e f θ))
      volume 0 (2 * Real.pi) := by
  have h := Commons.Analysis.Integral.intervalIntegrable_circle_gain hc hT hρ xi e f he hf hef
  refine h.congr_ae ?_
  filter_upwards with θ
  rw [potPairVal_circle (c := c) hρ θ (norm_circleDir he hf hef θ)]
  rfl

/-- **The circle average of `modelPotVal` is the weighted sum of the circle averages of the
single-pair gains.** -/
theorem circleAvg_modelPotVal_eq_sum {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {κ T : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) (sbar : EN E N) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      = ∑ j ∈ k.erase i₀, m i₀ * m j * ((1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
          potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ)) := by
  have hint : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun θ : ℝ =>
      potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ))
      volume 0 (2 * Real.pi) := fun j _ =>
    intervalIntegrable_potPairVal_circle (Real.sqrt_pos.mpr hκ) hT hρ e f he hf hef
  have h1 : (∫ θ in (0:ℝ)..(2*Real.pi), modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          (∫ θ in (0:ℝ)..(2*Real.pi),
            potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ)) := by
    rw [show (fun θ : ℝ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        = fun θ => ∑ j ∈ k.erase i₀, m i₀ * m j *
            potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ) from rfl]
    rw [intervalIntegral.integral_finsetSum (fun j hj => (hint j hj).const_mul _)]
    exact Finset.sum_congr rfl fun j hj => by
      rw [intervalIntegral.integral_const_mul]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Circle

/-! ## The bound on the circle average of the potential term -/

section PotBound

/-- The parabolic model constant
`W = ∫_0^∞ ((1/2π)∫_θ ((1+v²+2v cos θ)^{-1/2} - 1) dθ) v^{-3/2} dv`, which is **strictly
negative** (`Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg`). -/
noncomputable def phiWeight : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ),
    ((1 / (2 * Real.pi)) * ∫ theta in (0)..(2 * Real.pi),
        (((1 + v ^ 2 + 2 * v * Real.cos theta) ^ (-(1 : ℝ) / 2)) - 1))
      * v ^ (-(3 : ℝ) / 2)

lemma phiWeight_neg : phiWeight < 0 :=
  Commons.Analysis.Integral.integral_phi_rpow_neg_three_halves_neg

/-- **The `θ`-average bound for a single pair** (the SESSION-34 estimate, rephrased in terms of
`potPairVal`). -/
lemma circleAvg_potPairVal_le {xi : E} {c T ρ z B : ℝ} {e f : E} (hρ : 0 < ρ)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (hz : ‖xi‖ = z)
    (h : (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
          (∫ t in (0:ℝ)..T, (‖(c * t ^ ((2:ℝ)/3)) • xi
                + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
              - (c * t ^ ((2:ℝ)/3) * z)⁻¹) ≤ B) :
    (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        potPairVal xi c T (ρ • circleDir e f θ) ≤ B := by
  rw [show (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        potPairVal xi c T (ρ • circleDir e f θ)
      = (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
          (∫ t in (0:ℝ)..T, (‖(c * t ^ ((2:ℝ)/3)) • xi
                + (min ρ (max 0 (T - t))) • (Real.cos θ • e + Real.sin θ • f)‖)⁻¹
              - (c * t ^ ((2:ℝ)/3) * z)⁻¹) from by
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [potPairVal_circle (c := c) hρ θ (norm_circleDir he hf hef θ), hz]
    rfl]
  exact h

/-- **The bound on the circle average of `modelPotVal`**, given the per-pair bound. -/
theorem circleAvg_modelPotVal_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) (sbar : EN E N)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) {B : Fin N → ℝ}
    (hBj : ∀ j ∈ k.erase i₀, (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ) ≤ B j) :
    (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      ≤ ∑ j ∈ k.erase i₀, m i₀ * m j * B j := by
  rw [circleAvg_modelPotVal_eq_sum (m := m) hκ hT hρ sbar e f he hf hef]
  refine Finset.sum_le_sum fun j hjk => ?_
  exact mul_le_mul_of_nonneg_left (hBj j hjk)
    (mul_nonneg (hm i₀).le (hm j).le)

/-- The `θ`-integrability of `modelPotVal` on the circle of radius `ρ`. -/
lemma intervalIntegrable_modelPotVal_circle {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}
    {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) (sbar : EN E N) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    IntervalIntegrable (fun θ : ℝ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      volume 0 (2 * Real.pi) := by
  have h : ∀ j ∈ k.erase i₀, IntervalIntegrable (fun θ : ℝ =>
      m i₀ * m j * potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ))
      volume 0 (2 * Real.pi) := fun j _ =>
    (intervalIntegrable_potPairVal_circle (Real.sqrt_pos.mpr hκ) hT hρ e f he hf hef).const_mul _
  have hs := IntervalIntegrable.sum (k.erase i₀) h
  rw [show (∑ x ∈ k.erase i₀, fun θ : ℝ => m i₀ * m x *
        potPairVal (sbar i₀ - sbar x) (Real.sqrt κ) T (ρ • circleDir e f θ))
      = (fun θ : ℝ => ∑ x ∈ k.erase i₀, m i₀ * m x *
        potPairVal (sbar i₀ - sbar x) (Real.sqrt κ) T (ρ • circleDir e f θ)) from by
    funext θ; rw [Finset.sum_apply]] at hs
  rw [show (fun θ : ℝ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      = fun θ => ∑ j ∈ k.erase i₀, m i₀ * m j *
          potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ) from rfl]
  exact hs

end PotBound

section PotBoundFinal

/-- The gain constant of the potential bound. -/
noncomputable def potGainA (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (κ : ℝ)
    (sbar : EN E N) : ℝ :=
  ∑ j ∈ k.erase i₀, m i₀ * m j * ((3/2) * (Real.sqrt κ) ^ (-(3:ℝ)/2)
    * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * (- phiWeight))

/-- The cost constant of the potential bound. -/
noncomputable def potGainB (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (κ T : ℝ)
    (sbar : EN E N) : ℝ :=
  ∑ j ∈ k.erase i₀, 6 * m i₀ * m j / ((Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3)
    * ‖sbar i₀ - sbar j‖ ^ 2)

lemma potGainA_pos {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    {κ : ℝ} (hκ : 0 < κ) (sbar : EN E N) (hne : (k.erase i₀).Nonempty)
    (hz : ∀ j ∈ k.erase i₀, 0 < ‖sbar i₀ - sbar j‖) : 0 < potGainA m k i₀ κ sbar := by
  rw [potGainA]
  refine Finset.sum_pos (fun j hj => mul_pos (mul_pos (hm i₀) (hm j)) ?_) hne
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hκ) _))
    (Real.rpow_pos_of_pos (hz j hj) _)) (neg_pos.mpr phiWeight_neg)

lemma potGainB_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) (sbar : EN E N) : 0 ≤ potGainB m k i₀ κ T sbar := by
  rw [potGainB]
  refine Finset.sum_nonneg fun j _ => div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (hm i₀).le) (hm j).le) (by positivity)

/-- **The potential bound in the form required by `exists_model_dir_negative`.** -/
theorem circleAvg_modelPotVal_bound {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ)
    (hρT : ρ ≤ T / 2) (sbar : EN E N) (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (hz : ∀ j ∈ k.erase i₀, 0 < ‖sbar i₀ - sbar j‖)
    (hpj : ∀ j ∈ k.erase i₀, (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T (ρ • circleDir e f θ)
          ≤ (3/2) * ρ ^ ((1:ℝ)/2) * (Real.sqrt κ) ^ (-(3:ℝ)/2)
              * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * phiWeight
            + 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T - ρ) ^ ((4:ℝ)/3)
                * ‖sbar i₀ - sbar j‖ ^ 2)) :
    (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
      ≤ - potGainA m k i₀ κ sbar * ρ ^ ((1:ℝ)/2) + potGainB m k i₀ κ T sbar * ρ ^ 2 := by
  have hc2 : (0:ℝ) < (Real.sqrt κ) ^ 2 := pow_pos (Real.sqrt_pos.mpr hκ) 2
  have hT2 : (0:ℝ) < (T / 2) ^ ((4:ℝ)/3) := Real.rpow_pos_of_pos (by linarith) _
  have hpT : (0:ℝ) < T - ρ := by linarith
  have hle : (T / 2) ^ ((4:ℝ)/3) ≤ (T - ρ) ^ ((4:ℝ)/3) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  refine (circleAvg_modelPotVal_le hm hκ hT hρ sbar e f he hf hef
    (B := fun j => (3/2) * ρ ^ ((1:ℝ)/2) * (Real.sqrt κ) ^ (-(3:ℝ)/2)
        * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * phiWeight
      + 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T - ρ) ^ ((4:ℝ)/3)
          * ‖sbar i₀ - sbar j‖ ^ 2)) hpj).trans ?_
  -- replace `T - ρ` by `T / 2` in the cost term
  have hstep : ∑ j ∈ k.erase i₀, m i₀ * m j *
        ((3/2) * ρ ^ ((1:ℝ)/2) * (Real.sqrt κ) ^ (-(3:ℝ)/2)
            * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * phiWeight
          + 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T - ρ) ^ ((4:ℝ)/3)
              * ‖sbar i₀ - sbar j‖ ^ 2))
      ≤ ∑ j ∈ k.erase i₀, m i₀ * m j *
        ((3/2) * ρ ^ ((1:ℝ)/2) * (Real.sqrt κ) ^ (-(3:ℝ)/2)
            * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * phiWeight
          + 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3)
              * ‖sbar i₀ - sbar j‖ ^ 2)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hzpos : (0:ℝ) < ‖sbar i₀ - sbar j‖ ^ 2 := pow_pos (hz j hj) 2
    have hb : (Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3) * ‖sbar i₀ - sbar j‖ ^ 2
        ≤ (Real.sqrt κ) ^ 2 * (T - ρ) ^ ((4:ℝ)/3) * ‖sbar i₀ - sbar j‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hle
        (show (0:ℝ) ≤ (Real.sqrt κ) ^ 2 * ‖sbar i₀ - sbar j‖ ^ 2 by positivity)
      nlinarith [this]
    have hbpos : (0:ℝ) < (Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3)
        * ‖sbar i₀ - sbar j‖ ^ 2 := mul_pos (mul_pos hc2 hT2) hzpos
    have hnum : 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T - ρ) ^ ((4:ℝ)/3)
          * ‖sbar i₀ - sbar j‖ ^ 2)
        ≤ 6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3)
          * ‖sbar i₀ - sbar j‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hbpos hb
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hnum)
      (le_of_lt (mul_pos (hm i₀) (hm j)))
  refine hstep.trans ?_
  rw [potGainB]
  simp only [mul_add, Finset.sum_add_distrib]
  have hsum1 : ∑ j ∈ k.erase i₀, m i₀ * m j * ((3/2) * ρ ^ ((1:ℝ)/2)
        * (Real.sqrt κ) ^ (-(3:ℝ)/2) * (‖sbar i₀ - sbar j‖) ^ (-(3:ℝ)/2) * phiWeight)
      = - potGainA m k i₀ κ sbar * ρ ^ ((1:ℝ)/2) := by
    unfold potGainA
    simp only [neg_mul]
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum2 : ∑ j ∈ k.erase i₀, m i₀ * m j * (6 * ρ ^ 2 / ((Real.sqrt κ) ^ 2
        * (T / 2) ^ ((4:ℝ)/3) * ‖sbar i₀ - sbar j‖ ^ 2))
      = (∑ j ∈ k.erase i₀, 6 * m i₀ * m j / ((Real.sqrt κ) ^ 2
          * (T / 2) ^ ((4:ℝ)/3) * ‖sbar i₀ - sbar j‖ ^ 2)) * ρ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hzpos : (0:ℝ) < ‖sbar i₀ - sbar j‖ ^ 2 := pow_pos (hz j hj) 2
    have hbpos : (Real.sqrt κ) ^ 2 * (T / 2) ^ ((4:ℝ)/3) * ‖sbar i₀ - sbar j‖ ^ 2 ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos hc2 hT2) hzpos)
    field_simp
  rw [hsum1, hsum2]

end PotBoundFinal
