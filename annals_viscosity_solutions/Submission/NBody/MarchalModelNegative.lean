import Submission.NBody.MarchalModelKinetic
import Submission.Commons.Analysis.Integral.intervalIntegral_ite_le_const
import Submission.Commons.Analysis.Integral.circle_average_linear_eq_zero
import Submission.Commons.Analysis.Asymptotic.exists_pos_forall_neg_rpow_half_add
import Submission.NBody.MarchalBumpPotential
import Submission.NBody.MarchalBumpTransfer

/-!
# The model negativity of the standard-variation argument

The endgame of the Ferrario--Terracini argument (see `Submission/ROADMAP.md`, SESSION 34/35): the
*model* action difference obtained by perturbing the parabolic blow-up profile
`q̄(t) = √κ t^{2/3} s̄` by the standard variation in the direction `δ`,

  `M(δ) = ∫_0^T ( massInner m (q̄') (v^δ)'  +  ½ ‖(v^δ)'‖_m²  +  U_k(q̄ + v^δ) - U_k(q̄) ) dt`,

is negative for some direction `δ = ρ • e_θ` on the circle of radius `ρ` in a 2-plane.

The proof averages `M(ρ • e_θ)` over the circle.  The `θ`-average of the *kinetic* part is a
`θ`-independent quantity of order `ρ`, while the `θ`-average of the *potential* part is negative
of order `ρ^{1/2}`; hence for small `ρ` the total average is negative, and therefore some
direction on the circle has negative model action difference.

This file contains the kinetic half of the computation (exact), the circle-average reduction and
the arithmetic endgame.  The potential bound enters as an explicit hypothesis `hpot`; it is
discharged in `Submission.NBody.MarchalModelPotential`.
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

variable {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N}

/-! ## Bilinearity and the norm of the standard-variation direction -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The standard-variation direction is additive in the displacement vector. -/
lemma stdPertVec_add (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (v w : E) :
    stdPertVec m k i₀ (v + w) = stdPertVec m k i₀ v + stdPertVec m k i₀ w := by
  rw [stdPertVec, stdPertVec, stdPertVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_add, singleBodyVec_add]

/-- The squared mass norm of the standard-variation direction, as an explicit multiple of `‖v‖²`. -/
lemma stdPertVec_norm_sq {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N)) (i₀ : Fin N)
    (v : E) :
    ‖stdPertVec m k i₀ v‖_[m] ^ 2
      = (∑ j ∈ k, m j * ((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k) ^ 2) * ‖v‖ ^ 2 := by
  classical
  have h1 : ∀ i, m i * ‖stdPertVec m k i₀ v i‖ ^ 2
      = if i ∈ k then
          m i * (((if i = i₀ then 1 else 0) - m i₀ / clusterMass m k) ^ 2 * ‖v‖ ^ 2) else 0 := by
    intro i
    by_cases hi : i ∈ k
    · rw [if_pos hi, stdPertVec_apply_of_mem hi, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    · rw [if_neg hi, stdPertVec_apply_of_notMem hi]
      simp
  rw [weightedNorm_sq_eq_sum hm (stdPertVec m k i₀ v),
    Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The explicit constant appearing in `stdPertVec_norm_sq`. -/
noncomputable def stdPertCoefSq (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) : ℝ :=
  ∑ j ∈ k, m j * ((if j = i₀ then 1 else 0) - m i₀ / clusterMass m k) ^ 2

lemma stdPertVec_norm_sq' {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) (v : E) :
    ‖stdPertVec m k i₀ v‖_[m] ^ 2 = stdPertCoefSq m k i₀ * ‖v‖ ^ 2 :=
  stdPertVec_norm_sq hm k i₀ v

/-! ## The circle of directions in a 2-plane -/

/-- The point of the unit circle in the plane spanned by the orthonormal pair `(e, f)`. -/
noncomputable def circleDir (e f : E) (θ : ℝ) : E := Real.cos θ • e + Real.sin θ • f

@[simp] lemma circleDir_apply (e f : E) (θ : ℝ) :
    circleDir e f θ = Real.cos θ • e + Real.sin θ • f := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma norm_circleDir {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) (θ : ℝ) :
    ‖circleDir e f θ‖ = 1 := by
  have h : ‖circleDir e f θ‖ ^ 2 = 1 := by
    rw [circleDir, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      inner_smul_left, inner_smul_right, he, hf, hef, mul_one, mul_zero, mul_zero]
    simp only [mul_one, mul_zero, add_zero]
    rw [sq_abs, sq_abs]
    have := Real.cos_sq_add_sin_sq θ
    linarith
  nlinarith [norm_nonneg (circleDir e f θ)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma stdPertVec_circleDir (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (e f : E) (θ : ℝ) :
    stdPertVec m k i₀ (circleDir e f θ)
      = Real.cos θ • stdPertVec m k i₀ e + Real.sin θ • stdPertVec m k i₀ f := by
  rw [circleDir, stdPertVec_add, stdPertVec_smul, stdPertVec_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma massInner_add_right (m : Fin N → ℝ) (v u w : EN E N) :
    massInner m v (u + w) = massInner m v u + massInner m v w := by
  simp only [massInner, PiLp.add_apply, inner_add_right, mul_add, Finset.sum_add_distrib]

/-! ## The circle averages -/

lemma integral_cos_two_pi : ∫ θ in (0:ℝ)..(2*Real.pi), Real.cos θ = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero, sub_zero]

lemma integral_sin_two_pi : ∫ θ in (0:ℝ)..(2*Real.pi), Real.sin θ = 0 := by
  rw [integral_sin, Real.cos_zero, Real.cos_two_pi, sub_self]

lemma circleAvg_cos : (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi), Real.cos θ = 0 := by
  rw [integral_cos_two_pi, mul_zero]

lemma circleAvg_sin : (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi), Real.sin θ = 0 := by
  rw [integral_sin_two_pi, mul_zero]

/-- The circle average of the mass inner product of a fixed configuration against the standard
variation in the direction `circleDir e f θ` vanishes. -/
lemma circleAvg_massInner_stdPertVec (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N)
    (W : EN E N) (e f : E) :
    (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        massInner m W (stdPertVec m k i₀ (circleDir e f θ)) = 0 := by
  have h : ∀ θ, massInner m W (stdPertVec m k i₀ (circleDir e f θ))
      = massInner m W (stdPertVec m k i₀ e) * Real.cos θ
        + massInner m W (stdPertVec m k i₀ f) * Real.sin θ := by
    intro θ
    rw [stdPertVec_circleDir, massInner_add_right, massInner_smul_right, massInner_smul_right]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => h θ)]
  have h1 : IntervalIntegrable
      (fun x : ℝ => massInner m W (stdPertVec m k i₀ e) * Real.cos x) volume 0 (2*Real.pi) :=
    (continuous_const.mul continuous_cos).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun x : ℝ => massInner m W (stdPertVec m k i₀ f) * Real.sin x) volume 0 (2*Real.pi) :=
    (continuous_const.mul continuous_sin).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (μ := volume) h1 h2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_two_pi, integral_sin_two_pi, mul_zero, mul_zero, add_zero, mul_zero]


/-! ## The model action difference -/

/-- The standard-variation perturbation in the rescaled time equals `stdVarVec`. -/
lemma stdPert_eq_stdVarVec (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) (T : ℝ) :
    stdPert m k i₀ δ T = stdVarVec m k i₀ δ T := by
  funext s
  rw [stdPert, stdVarVec, stdVar, stdPertVec_smul]

/-- The kinetic cross term of the model action difference. -/
noncomputable def modelCrossVal (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (κ : ℝ)
    (sbar : EN E N) (T : ℝ) (δ : E) : ℝ :=
  ∫ t in (0:ℝ)..T,
    massInner m (deriv (blowUpProfile κ sbar) t) (deriv (stdVarVec m k i₀ δ T) t)

/-- The kinetic quadratic term of the model action difference. -/
noncomputable def modelQuadVal (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (T : ℝ)
    (δ : E) : ℝ :=
  ∫ t in (0:ℝ)..T, (1/2) * ‖deriv (stdVarVec m k i₀ δ T) t‖_[m] ^ 2

/-- The model potential gain of a **single pair** `(i₀,j)` of the cluster: the two bodies are
separated by `(c t^{2/3}) • xi` along the parabolic profile and by the relative displacement
`stdVar δ T t`.  (This is the term whose `θ`-average is bounded by the SESSION-34 lemma
`Commons.Analysis.Integral.integral_theta_model_potential_le_strict`.) -/
noncomputable def potPairVal (xi : E) (c T : ℝ) (δ : E) : ℝ :=
  ∫ t in (0:ℝ)..T,
    ((‖(c * t ^ ((2:ℝ)/3)) • xi + stdVar δ T t‖)⁻¹ - (c * t ^ ((2:ℝ)/3) * ‖xi‖)⁻¹)

/-- The potential term of the model action difference, written as the **sum over the pairs through
`i₀`** (see `clusterPotential_bump_diff`); writing it as a sum makes the `θ`-linearity of the circle
average definitional, and the `θ`-integrability a finite sum of single-pair integrabilities. -/
noncomputable def modelPotVal (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (κ : ℝ)
    (sbar : EN E N) (T : ℝ) (δ : E) : ℝ :=
  ∑ j ∈ k.erase i₀, m i₀ * m j * potPairVal (sbar i₀ - sbar j) (Real.sqrt κ) T δ

/-- The model action difference of the standard variation in the direction `δ`. -/
noncomputable def modelDiff (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (κ : ℝ)
    (sbar : EN E N) (T : ℝ) (δ : E) : ℝ :=
  modelCrossVal m k i₀ κ sbar T δ + modelQuadVal m k i₀ T δ + modelPotVal m k i₀ κ sbar T δ

/-! ## The kinetic cross term -/

variable {κ T ρ : ℝ} {sbar : EN E N}

omit [MeasurableSpace E] [BorelSpace E] in
lemma massInner_zero_right (m : Fin N → ℝ) (v : EN E N) : massInner m v 0 = 0 := by
  simp [massInner]

omit [MeasurableSpace E] [BorelSpace E] in
lemma massInner_neg_right (m : Fin N → ℝ) (v w : EN E N) :
    massInner m v (-w) = -massInner m v w := by
  simp only [massInner, PiLp.neg_apply, inner_neg_right, mul_neg, Finset.sum_neg_distrib]

/-- The standard-variation vector field for a displacement of norm `ρ` supported in the direction
`circleDir e f θ`. -/
lemma stdVarVec_circleDir (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (e f : E)
    {ρ T : ℝ} (hρ : 0 < ρ) (θ : ℝ) (hef : ‖circleDir e f θ‖ = 1) :
    stdVarVec m k i₀ (ρ • circleDir e f θ) T
      = fun s => (min 1 (max 0 ((T - s) / ρ)) * ρ) • stdPertVec m k i₀ (circleDir e f θ) := by
  funext s
  rw [stdVarVec, stdCoef_smul_norm_one hρ hef, stdPertVec_smul]
  simp only [smul_smul]

/-- The almost-everywhere derivative of the standard variation for `δ = ρ • circleDir`. -/
lemma stdVarVecDeriv_circleDir (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (e f : E)
    {ρ T : ℝ} (hρ : 0 < ρ) (θ : ℝ) (hef : ‖circleDir e f θ‖ = 1) (t : ℝ) :
    stdVarVecDeriv m k i₀ (ρ • circleDir e f θ) T t
      = if t ≤ T - ρ then 0 else -stdPertVec m k i₀ (circleDir e f θ) := by
  rw [stdVarVecDeriv, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hef, mul_one]
  by_cases h : t ≤ T - ρ
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, stdPertVec_smul, smul_smul, neg_mul, inv_mul_cancel₀ hρ.ne',
      neg_one_smul]

/-! ## The exact value of the kinetic cross term -/

/-- The cross term of the model kinetic energy, for a displacement of norm `ρ` in a direction on
the unit circle.  It is a *linear* functional of the direction. -/
lemma modelCrossVal_circle {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) {κ T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (sbar : EN E N)
    (e f : E) (θ : ℝ) (hef : ‖circleDir e f θ‖ = 1) :
    modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)
      = (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1))
          * massInner m sbar (stdPertVec m k i₀ (circleDir e f θ)) := by
  have hδne : ρ • circleDir e f θ ≠ 0 := by
    intro h
    have h0 : ‖ρ • circleDir e f θ‖ = 0 := by rw [h, norm_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hef, mul_one] at h0
    exact absurd h0 (ne_of_gt hρ)
  -- (A) replace the a.e. derivative by its explicit value
  have hA : modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)
      = ∫ t in (0:ℝ)..T,
          massInner m (deriv (blowUpProfile κ sbar) t)
            (stdVarVecDeriv m k i₀ (ρ • circleDir e f θ) T t) := by
    rw [modelCrossVal]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    have hae := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp
      (deriv_stdVarVec_ae m k i₀ (ρ • circleDir e f θ) T hδne)
    filter_upwards [hae] with t ht hmem
    rw [ht hmem]
  -- (B) the pointwise form
  have hB : ∫ t in (0:ℝ)..T,
        massInner m (deriv (blowUpProfile κ sbar) t)
          (stdVarVecDeriv m k i₀ (ρ • circleDir e f θ) T t)
      = ∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1)
            * massInner m sbar (stdPertVec m k i₀ (circleDir e f θ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    filter_upwards with t
    intro hmem
    rw [deriv_blowUpProfile κ sbar hmem.1,
      stdVarVecDeriv_circleDir m k i₀ e f hρ θ hef t]
    by_cases h : t ≤ T - ρ
    · rw [if_pos h, if_pos h, massInner_zero_right, mul_zero, zero_mul]
    · rw [if_neg h, if_neg h, massInner_smul_left hm, massInner_neg_right]
      ring
  -- (C) factor the direction out of the integral
  have hC : ∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1)
            * massInner m sbar (stdPertVec m k i₀ (circleDir e f θ))
      = (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1))
          * massInner m sbar (stdPertVec m k i₀ (circleDir e f θ)) := by
    rw [intervalIntegral.integral_mul_const]
  rw [hA, hB, hC]

/-! ## The exact value of the kinetic quadratic term -/

/-- The quadratic term of the model kinetic energy, for a displacement of norm `ρ`. -/
lemma modelQuadVal_circle {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (e f : E) (θ : ℝ)
    (hef : ‖circleDir e f θ‖ = 1) :
    modelQuadVal m k i₀ T (ρ • circleDir e f θ) = (1/2) * ρ * stdPertCoefSq m k i₀ := by
  have hδne : ρ • circleDir e f θ ≠ 0 := by
    intro h
    have h0 : ‖ρ • circleDir e f θ‖ = 0 := by rw [h, norm_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hef, mul_one] at h0
    exact absurd h0 (ne_of_gt hρ)
  have hA : modelQuadVal m k i₀ T (ρ • circleDir e f θ)
      = ∫ t in (0:ℝ)..T,
          (1/2) * ‖stdVarVecDeriv m k i₀ (ρ • circleDir e f θ) T t‖_[m] ^ 2 := by
    rw [modelQuadVal]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    have hae := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp
      (deriv_stdVarVec_ae m k i₀ (ρ • circleDir e f θ) T hδne)
    filter_upwards [hae] with t ht hmem
    rw [ht hmem]
  have hB : ∫ t in (0:ℝ)..T,
          (1/2) * ‖stdVarVecDeriv m k i₀ (ρ • circleDir e f θ) T t‖_[m] ^ 2
      = ∫ t in (0:ℝ)..T,
          (if t ≤ T - ρ then 0 else (1/2) * stdPertCoefSq m k i₀) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hT.le]
    filter_upwards with t
    intro hmem
    rw [stdVarVecDeriv_circleDir m k i₀ e f hρ θ hef t]
    by_cases h : t ≤ T - ρ
    · rw [if_pos h, if_pos h]
      simp [weightedNorm_zero]
    · rw [if_neg h, if_neg h]
      have hneg : ‖-stdPertVec m k i₀ (circleDir e f θ)‖_[m]
          = ‖stdPertVec m k i₀ (circleDir e f θ)‖_[m] := by
        rw [show (-stdPertVec m k i₀ (circleDir e f θ) : EN E N)
              = (-1:ℝ) • stdPertVec m k i₀ (circleDir e f θ) from (neg_one_smul ℝ _).symm,
          weightedNorm_smul (fun i => hm i) (-1) (stdPertVec m k i₀ (circleDir e f θ))]
        simp
      rw [hneg, stdPertVec_norm_sq' hm, hef, one_pow, mul_one]
  have hC := Commons.Analysis.Integral.intervalIntegral_ite_le_const (a := (0:ℝ)) (b := T)
    (c := T - ρ) (K := (1/2) * stdPertCoefSq m k i₀) (by linarith) (by linarith)
  rw [hA, hB, hC]
  ring

/-! ## The circle averages -/

lemma stdPertCoefSq_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) : 0 ≤ stdPertCoefSq m k i₀ :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hm j) (sq_nonneg _)

/-- The circle average of the cross term vanishes. -/
lemma circleAvg_modelCrossVal {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) {κ T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (sbar : EN E N)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ) = 0 := by
  have hpt : ∀ θ : ℝ, modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)
      = (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1))
          * massInner m sbar (stdPertVec m k i₀ (circleDir e f θ)) := fun θ =>
    modelCrossVal_circle hm k i₀ hT hρ hρT sbar e f θ (norm_circleDir he hf hef θ)
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const_mul]
  have hlin := Commons.Analysis.Integral.circle_average_linear_eq_zero
    (F := fun v => massInner m sbar (stdPertVec m k i₀ v))
    (fun u v => by rw [stdPertVec_add, massInner_add_right])
    (fun c u => by rw [stdPertVec_smul, massInner_smul_right]) e f
  have hlin' : (1 / (2 * Real.pi)) * ∫ x in (0:ℝ)..(2*Real.pi),
      massInner m sbar (stdPertVec m k i₀ (circleDir e f x)) = 0 := hlin
  rw [show (1 / (2 * Real.pi)) *
        ((∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1))
          * ∫ x in (0:ℝ)..(2*Real.pi), massInner m sbar (stdPertVec m k i₀ (circleDir e f x)))
      = (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
            (if t ≤ T - ρ then 0 else -1))
          * ((1 / (2 * Real.pi)) * ∫ x in (0:ℝ)..(2*Real.pi),
              massInner m sbar (stdPertVec m k i₀ (circleDir e f x))) from by ring,
    hlin', mul_zero]

/-- The circle average of the quadratic term. -/
lemma circleAvg_modelQuadVal {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (i₀ : Fin N) {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (e f : E)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelQuadVal m k i₀ T (ρ • circleDir e f θ) = (1/2) * ρ * stdPertCoefSq m k i₀ := by
  have hpt : ∀ θ : ℝ, modelQuadVal m k i₀ T (ρ • circleDir e f θ)
      = (1/2) * ρ * stdPertCoefSq m k i₀ := fun θ =>
    modelQuadVal_circle hm k i₀ hT hρ hρT e f θ (norm_circleDir he hf hef θ)
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp

/-! ## The model negativity -/

/-- **The model negativity of the standard variation.**  Averaging the model action difference of
the standard variation over the circle of directions of radius `ρ` in a `2`-plane, the cross term
averages to `0`, the quadratic term contributes the positive (`θ`-independent) amount `ρ C/2`, and
the potential term contributes at most `-A√ρ + B ρ²`; for small `ρ` the total is negative, hence
some direction on the circle has strictly negative model action difference. -/
theorem exists_model_dir_negative {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {κ T : ℝ} (hκ : 0 < κ) (hT : 0 < T) (sbar : EN E N)
    (e f : E) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    {A B ρmax : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hρmax : 0 < ρmax) (hρmaxT : ρmax ≤ T / 2)
    (hpot : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi),
        modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)
          ≤ -A * ρ ^ ((1:ℝ)/2) + B * ρ ^ 2)
    (hpotint : ∀ ρ ∈ Set.Ioo (0:ℝ) ρmax,
      IntervalIntegrable (fun θ => modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        volume 0 (2*Real.pi)) :
    ∃ ρ > (0:ℝ), ∃ θ ∈ Set.Icc (0:ℝ) (2*Real.pi),
      modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ) < 0 := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ :=
    Commons.Analysis.Asymptotic.exists_pos_forall_neg_rpow_half_add
      (A := A) (B := (1/2) * stdPertCoefSq m k i₀) (C := B)
      hA (mul_nonneg (by norm_num) (stdPertCoefSq_nonneg (fun i => (hm i).le) k i₀)) hB
  set ρ : ℝ := min ρ₀ ρmax / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact div_pos (lt_min hρ₀pos hρmax) (by norm_num)
  have hρltρ₀ : ρ < ρ₀ := by
    rw [hρdef]
    have := min_le_left ρ₀ ρmax
    linarith
  have hρltρmax : ρ < ρmax := by
    rw [hρdef]
    have := min_le_right ρ₀ ρmax
    linarith
  have hρT : ρ ≤ T := by
    rw [hρdef]; linarith
  have hρT2 : ρ ≤ T / 2 := by
    rw [hρdef]; linarith
  have hmem : ρ ∈ Set.Ioo (0:ℝ) ρmax := ⟨hρpos, hρltρmax⟩
  -- integrability / continuity of the kinetic part as a function of `θ`
  have hcrosscont : Continuous (fun θ : ℝ =>
      modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
    have hpt : (fun θ : ℝ => modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        = fun θ => (∫ t in (0:ℝ)..T, ((2:ℝ)/3 * Real.sqrt κ * t ^ (-(1:ℝ)/3)) *
              (if t ≤ T - ρ then 0 else -1))
            * (massInner m sbar (stdPertVec m k i₀ e) * Real.cos θ
              + massInner m sbar (stdPertVec m k i₀ f) * Real.sin θ) := by
      funext θ
      rw [modelCrossVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT sbar e f θ
          (norm_circleDir he hf hef θ),
        stdPertVec_circleDir, massInner_add_right, massInner_smul_right, massInner_smul_right]
      ring
    rw [hpt]
    fun_prop
  have hquadcont : Continuous (fun θ : ℝ =>
      modelQuadVal m k i₀ T (ρ • circleDir e f θ)) := by
    have hpt : (fun θ : ℝ => modelQuadVal m k i₀ T (ρ • circleDir e f θ))
        = fun _ => (1/2) * ρ * stdPertCoefSq m k i₀ := funext fun θ =>
      modelQuadVal_circle (fun i => (hm i).le) k i₀ hT hρpos hρT e f θ
        (norm_circleDir he hf hef θ)
    rw [hpt]
    exact continuous_const
  have hcross : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)) = 0 :=
    circleAvg_modelCrossVal (κ := κ) (sbar := sbar) (fun i => (hm i).le) k i₀
      hT hρpos hρT e f he hf hef
  have hquad : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelQuadVal m k i₀ T (ρ • circleDir e f θ)) = (1/2) * ρ * stdPertCoefSq m k i₀ :=
    circleAvg_modelQuadVal (T := T) (ρ := ρ) (fun i => (hm i).le) k i₀ hT hρpos
      hρT e f he hf hef
  have hpota : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
      modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)) ≤ -A * ρ ^ ((1:ℝ)/2) + B * ρ ^ 2 :=
    hpot ρ hmem
  have htot : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
      = (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
            modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ))
        + (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
            modelQuadVal m k i₀ T (ρ • circleDir e f θ))
        + (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
            modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
    have h1 : (∫ θ in (0:ℝ)..(2*Real.pi), modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
        = (∫ θ in (0:ℝ)..(2*Real.pi), modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ))
          + (∫ θ in (0:ℝ)..(2*Real.pi), modelQuadVal m k i₀ T (ρ • circleDir e f θ))
          + (∫ θ in (0:ℝ)..(2*Real.pi), modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
      rw [show (fun θ : ℝ => modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
          = fun θ => (modelCrossVal m k i₀ κ sbar T (ρ • circleDir e f θ)
              + modelQuadVal m k i₀ T (ρ • circleDir e f θ))
              + modelPotVal m k i₀ κ sbar T (ρ • circleDir e f θ) from rfl]
      rw [intervalIntegral.integral_add (μ := volume)
        ((hcrosscont.intervalIntegrable _ _).add (hquadcont.intervalIntegrable _ _))
        (hpotint ρ hmem)]
      rw [intervalIntegral.integral_add (μ := volume) (hcrosscont.intervalIntegrable _ _)
        (hquadcont.intervalIntegrable _ _)]
    rw [h1, mul_add, mul_add]
  have hub : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ))
      ≤ -A * ρ ^ ((1:ℝ)/2) + (1/2) * stdPertCoefSq m k i₀ * ρ + B * ρ ^ 2 := by
    rw [htot]
    linarith [hcross, hquad, hpota]
  have hρ₀' := hρ₀ ρ ⟨hρpos, hρltρ₀⟩
  have hneg : (1 / (2 * Real.pi)) * (∫ θ in (0:ℝ)..(2*Real.pi),
        modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ)) < 0 := by
    linarith [hub, hρ₀']
  have hlt : (∫ θ in (0:ℝ)..(2*Real.pi),
      modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ)) < 0 := by
    have h := mul_lt_mul_of_pos_left hneg hpi
    rw [← mul_assoc, one_div, mul_inv_cancel₀ hpi.ne', one_mul, mul_zero] at h
    exact h
  by_contra hcon
  have hnn : 0 ≤ (∫ θ in (0:ℝ)..(2*Real.pi),
      modelDiff m k i₀ κ sbar T (ρ • circleDir e f θ)) := by
    refine intervalIntegral.integral_nonneg hpi.le fun u hu => ?_
    by_contra hlt2
    exact hcon ⟨ρ, hρpos, u, hu, lt_of_not_ge hlt2⟩
  linarith

end Submission.NBody
