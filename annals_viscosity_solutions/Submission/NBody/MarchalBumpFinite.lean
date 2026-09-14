import Submission.NBody.MarchalSeqIntegrable
import Submission.NBody.MarchalBumpF5
import Submission.NBody.MarchalBumpRest
import Submission.NBody.MarchalSeqLeft
import Submission.NBody.MarchalReflectMinimizer
import Submission.Commons.MeasureTheory.ae_restrict_Ioc_add_mul
import Submission.Commons.MeasureTheory.ae_restrict_Ioc_sub_mul
import Submission.Commons.Analysis.Calculus.exists_holder_parametrisation

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody


/-- The constant bounding the weighted norm of the perturbation derivative. -/
noncomputable def bumpKappa (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) : ℝ :=
  (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) ^ 2

/-- The constant bounding the interaction-potential change of the bump. -/
noncomputable def bumpCross (m : Fin N → ℝ) (k : Finset (Fin N)) : ℝ :=
  ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2

lemma bumpCross_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) (k : Finset (Fin N)) :
    0 ≤ bumpCross m k := by
  rw [bumpCross]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hm _).le (hm _).le

lemma bumpKappa_nonneg (m : Fin N → ℝ) (k : Finset (Fin N)) (i₀ : Fin N) (δ : E) :
    0 ≤ bumpKappa m k i₀ δ := by
  rw [bumpKappa]; exact sq_nonneg _

lemma lagR_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {h : ℝ} (hh : 0 ≤ h) (x v : EN E N) :
    0 ≤ lagR m h x v := by
  rw [lagR_eq hm h x v]
  have h1 := U_nonneg hm x
  have h2 : 0 ≤ (1/2) * ‖v‖_[m] ^ 2 := by positivity
  linarith

lemma rpow_neg_two_thirds_div_mul {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    lam ^ (-(2:ℝ)/3) * (x / lam) ^ (-(2:ℝ)/3) = x ^ (-(2:ℝ)/3) := by
  rw [Real.div_rpow hx.le hlam.le, mul_div_assoc', mul_comm]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos hlam _))

/-- The window domination of the bumped Lagrangian (right side). -/
lemma lagR_bumpCurve_right_le_ae {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ}
    (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    {Cp2 ν : ℝ} (hCp2 : 0 ≤ Cp2) (hν : 0 < ν)
    (hUpotB : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t) ≤ Cp2 * t ^ (-(2:ℝ)/3))
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * t)) ν)
    (hsmall : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc (0:ℝ) T)),
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
            (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
        ≤ 2 * lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s))
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + (lam ^ (-(2:ℝ)/3) * Cp2 * s ^ (-(2:ℝ)/3)
                + bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) := by
  filter_upwards [deriv_bumpCurve_shift_ae (m := m) (k := k) (i₀ := i₀) (δ := δ)
      (t₀ := t₀) (γ := γ) hlam hT hδ hac,
    deriv_stdVarVec_ae m k i₀ δ T hδ,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hder hdstd hs
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  -- (1) kinetic part
  have hkin : kinetic m (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
      ≤ 2 * kinetic m (deriv γ (t₀ + lam * s)) + lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ := by
    have hnorm : ‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m]
        ≤ ‖deriv γ (t₀ + lam * s)‖_[m]
          + lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) := by
      calc ‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m]
          = ‖deriv γ (t₀ + lam * s) + lam ^ (-(1:ℝ)/3) • deriv (stdVarVec m k i₀ δ T) s‖_[m] := by
            rw [hder]
        _ ≤ ‖deriv γ (t₀ + lam * s)‖_[m]
              + ‖lam ^ (-(1:ℝ)/3) • deriv (stdVarVec m k i₀ δ T) s‖_[m] :=
            weightedNorm_add_le hm0 _ _
        _ = ‖deriv γ (t₀ + lam * s)‖_[m]
              + lam ^ (-(1:ℝ)/3) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] := by
            rw [weightedNorm_smul hm0, abs_of_pos (Real.rpow_pos_of_pos hlam _)]
        _ ≤ ‖deriv γ (t₀ + lam * s)‖_[m]
              + lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) := by
            have h1 : ‖deriv (stdVarVec m k i₀ δ T) s‖_[m]
                ≤ ‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹ := by
              rw [hdstd]
              exact weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T s
            have h2 : lam ^ (-(1:ℝ)/3) * ‖deriv (stdVarVec m k i₀ δ T) s‖_[m]
                ≤ lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hlam.le _)
            linarith
    have hkin1 : kinetic m (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
        = (1/2) * (‖deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s)‖_[m]) ^ 2 := by
      rw [kinetic, weightedNorm_sq_eq_sum hm0]
    have hkin2 : kinetic m (deriv γ (t₀ + lam * s))
        = (1/2) * (‖deriv γ (t₀ + lam * s)‖_[m]) ^ 2 := by
      rw [kinetic, weightedNorm_sq_eq_sum hm0]
    rw [hkin1, hkin2]
    have hsq := pow_le_pow_left₀ (weightedNorm_nonneg m _) hnorm 2
    have h2 : (‖deriv γ (t₀ + lam * s)‖_[m]
          + lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹)) ^ 2
        ≤ 2 * (‖deriv γ (t₀ + lam * s)‖_[m]) ^ 2
          + 2 * (lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹)) ^ 2 := by
      nlinarith [sq_nonneg (‖deriv γ (t₀ + lam * s)‖_[m]
          - lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹))]
    have h4 : (lam ^ (-(1:ℝ)/3)) ^ 2 = lam ^ (-(2:ℝ)/3) := by
      rw [sq, ← Real.rpow_add hlam]; norm_num
    have h3 : (1/2) * (2 * (lam ^ (-(1:ℝ)/3) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹)) ^ 2)
        = lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ := by
      rw [bumpKappa, mul_pow, h4]
      ring
    linarith [hsq, h2, h3]
  -- (2) potential part
  have hpot : U m (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
      ≤ U m (γ (t₀ + lam * s))
        + (lam ^ (-(2:ℝ)/3) * Cp2 * s ^ (-(2:ℝ)/3)
            + bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2)) := by
    have hdiff := bump_potential_diff (m := m) (k := k) (i₀ := i₀) (δ := δ) (lam := lam)
      (T := T) (t₀ := t₀) (γ := γ) hm hi₀ hlam hs.1.le
    have hX : clusterPotential m k
        (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s) ≤ Cp2 * s ^ (-(2:ℝ)/3) :=
      hUpotB s ⟨hs.1, hs.2⟩
    have hY : 0 ≤ clusterPotential m k (bumpRescaled m k γ t₀ lam s) :=
      clusterPotential_nonneg hm0 k _
    have hZ : clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
        - clusterPotentialRest m k (γ (t₀ + lam * s))
        ≤ bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) := by
      rw [bumpCross]
      exact clusterPotentialRest_bump_le hm hi₀ hν hlam hT (fun t ht => hsep t ht)
        hsmall ⟨hs.1, hs.2⟩
    have hp := Real.rpow_nonneg hlam.le (-(2:ℝ)/3)
    have hX' : lam ^ (-(2:ℝ)/3) * (clusterPotential m k
        (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)
        - clusterPotential m k (bumpRescaled m k γ t₀ lam s))
        ≤ lam ^ (-(2:ℝ)/3) * (Cp2 * s ^ (-(2:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (by linarith [hX, hY]) hp
    linarith [hdiff, hX', hZ]
  -- (3) assemble
  rw [show lagR m h (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
      = kinetic m (deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ + lam * s))
        + U m (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s)) + h from rfl,
    show lagR m h (γ (t₀ + lam * s)) (deriv γ (t₀ + lam * s))
      = kinetic m (deriv γ (t₀ + lam * s)) + U m (γ (t₀ + lam * s)) + h from rfl]
  have hU : 0 ≤ U m (γ (t₀ + lam * s)) := U_nonneg hm0 _
  linarith [hkin, hpot, hU, hh]




/-- The window domination of the bumped Lagrangian (right side), in the original time variable. -/
lemma lagR_bumpCurve_right_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ}
    (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    {Cp2 ν : ℝ} (hCp2 : 0 ≤ Cp2) (hν : 0 < ν)
    (hUpotB : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t) ≤ Cp2 * t ^ (-(2:ℝ)/3))
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * t)) ν)
    (hsmall : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ (t₀ + lam * T))),
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ + Cp2 * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2)) := by
  have hs := lagR_bumpCurve_right_le_ae (m := m) (h := h) hm hh (k := k) (i₀ := i₀) hi₀ hδ
    hlam hT hac hCp2 hν hUpotB hsep hsmall
  have ht := Commons.MeasureTheory.ae_restrict_Ioc_add_mul (t₀ := t₀) (lam := lam) (T := T)
    hlam hs
  refine (ht.and (MeasureTheory.ae_restrict_mem measurableSet_Ioc)).mono ?_
  rintro t ⟨hq, htmem⟩
  have ht0 : t₀ < t := htmem.1
  have htu : t₀ + lam * ((t - t₀) / lam) = t := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlam.ne']
    ring
  rw [htu] at hq
  have hx : 0 < t - t₀ := sub_pos.mpr ht0
  have hkey : lam ^ (-(2:ℝ)/3) * Cp2 * ((t - t₀) / lam) ^ (-(2:ℝ)/3)
      = Cp2 * |t - t₀| ^ (-(2:ℝ)/3) := by
    have h1 : lam ^ (-(2:ℝ)/3) * ((t - t₀) / lam) ^ (-(2:ℝ)/3) = (t - t₀) ^ (-(2:ℝ)/3) :=
      rpow_neg_two_thirds_div_mul hlam hx
    calc lam ^ (-(2:ℝ)/3) * Cp2 * ((t - t₀) / lam) ^ (-(2:ℝ)/3)
        = Cp2 * (lam ^ (-(2:ℝ)/3) * ((t - t₀) / lam) ^ (-(2:ℝ)/3)) := by ring
      _ = Cp2 * (t - t₀) ^ (-(2:ℝ)/3) := by rw [h1]
      _ = Cp2 * |t - t₀| ^ (-(2:ℝ)/3) := by rw [abs_of_pos hx]
  have hbK := bumpKappa_nonneg m k i₀ δ
  have hbc := bumpCross_nonneg hm k
  linarith [hq, hkey]

/-- The window domination of the bumped Lagrangian (left side), in the original time variable. -/
lemma lagR_bumpCurve_left_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ}
    (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N}
    (hacL : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) 0 (0 + lam * T))
    {Cp2 ν : ℝ} (hCp2 : 0 ≤ Cp2) (hν : 0 < ν)
    (hUpotB : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k (reflectCurve γ t₀) 0 lam t + stdVarVec m k i₀ δ T t)
        ≤ Cp2 * t ^ (-(2:ℝ)/3))
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (reflectCurve γ t₀ (0 + lam * t)) ν)
    (hsmall : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (t₀ - lam * T) t₀)),
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ + Cp2 * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2)) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hs := lagR_bumpCurve_right_le_ae (m := m) (h := h) hm hh (k := k) (i₀ := i₀) hi₀ hδ
    hlam hT (γ := reflectCurve γ t₀) (t₀ := 0) (by simpa using hacL) hCp2 hν hUpotB hsep hsmall
  have ht := Commons.MeasureTheory.ae_restrict_Ioc_sub_mul (t₀ := t₀) (lam := lam) (T := T) hlam hs
  refine (ht.and (MeasureTheory.ae_restrict_mem measurableSet_Ioc)).mono ?_
  rintro t ⟨hq, htmem⟩
  have ht0 : t₀ - lam * T < t := htmem.1
  have hu : t₀ - lam * ((t₀ - t) / lam) = t := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlam.ne']
    ring
  simp only [zero_add] at hq
  have e1 : bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀) (lam * ((t₀ - t) / lam))
      = bumpCurve m k i₀ δ T lam t₀ γ (t₀ - lam * ((t₀ - t) / lam)) :=
    bumpCurve_reflect δ T lam t₀ γ _
  have e2 : deriv (bumpCurve m k i₀ δ T lam 0 (reflectCurve γ t₀)) (lam * ((t₀ - t) / lam))
      = -deriv (bumpCurve m k i₀ δ T lam t₀ γ) (t₀ - lam * ((t₀ - t) / lam)) :=
    deriv_bumpCurve_reflect δ T lam t₀ γ _
  have e3 : deriv (reflectCurve γ t₀) (lam * ((t₀ - t) / lam))
      = -deriv γ (t₀ - lam * ((t₀ - t) / lam)) := deriv_reflectCurve γ t₀ _
  have e4 : reflectCurve γ t₀ (lam * ((t₀ - t) / lam)) = γ t := by
    show γ (t₀ - lam * ((t₀ - t) / lam)) = γ t
    rw [hu]
  rw [e1, e2, e3, e4, lagR_neg m hm0 h, lagR_neg m hm0 h, hu] at hq
  have hx : 0 ≤ t₀ - t := sub_nonneg.mpr htmem.2
  have hkey : lam ^ (-(2:ℝ)/3) * Cp2 * ((t₀ - t) / lam) ^ (-(2:ℝ)/3)
      = Cp2 * |t - t₀| ^ (-(2:ℝ)/3) := by
    rcases hx.eq_or_lt with hzero | hpos
    · rw [← hzero, zero_div, Real.zero_rpow (by norm_num : (-(2:ℝ)/3) ≠ 0), mul_zero,
        show t - t₀ = 0 by linarith, abs_zero, Real.zero_rpow (by norm_num : (-(2:ℝ)/3) ≠ 0),
        mul_zero]
    · have h1 : lam ^ (-(2:ℝ)/3) * ((t₀ - t) / lam) ^ (-(2:ℝ)/3)
          = (t₀ - t) ^ (-(2:ℝ)/3) := rpow_neg_two_thirds_div_mul hlam hpos
      calc lam ^ (-(2:ℝ)/3) * Cp2 * ((t₀ - t) / lam) ^ (-(2:ℝ)/3)
          = Cp2 * (lam ^ (-(2:ℝ)/3) * ((t₀ - t) / lam) ^ (-(2:ℝ)/3)) := by ring
        _ = Cp2 * (t₀ - t) ^ (-(2:ℝ)/3) := by rw [h1]
        _ = Cp2 * |t - t₀| ^ (-(2:ℝ)/3) := by
          rw [show t - t₀ = -(t₀ - t) by ring, abs_neg, abs_of_pos hpos]
  have hq' : lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t)
        (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
      ≤ 2 * lagR m h (γ t) (deriv γ t)
        + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
          + (lam ^ (-(2:ℝ)/3) * Cp2 * ((t₀ - t) / lam) ^ (-(2:ℝ)/3)
            + bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2))) := hq
  linarith [hq', hkey, bumpKappa_nonneg m k i₀ δ, bumpCross_nonneg hm k]

/-- **The global window domination.**  On the whole interval `(a,b]` the Lagrangian of the bumped
curve is dominated by twice the Lagrangian of `γ` plus an integrable correction. -/
lemma lagR_bumpCurve_le_global {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0)
    {lam T t₀ : ℝ} (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N} {a b : ℝ}
    (hacR : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (hacL : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) 0 (0 + lam * T))
    (horderL : a ≤ t₀ - lam * T) (horderR : t₀ + lam * T ≤ b)
    {Cp2R Cp2L νR νL : ℝ} (hCp2R : 0 ≤ Cp2R) (hCp2L : 0 ≤ Cp2L) (hνR : 0 < νR) (hνL : 0 < νL)
    (hUpotBR : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t) ≤ Cp2R * t ^ (-(2:ℝ)/3))
    (hUpotBL : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k (reflectCurve γ t₀) 0 lam t + stdVarVec m k i₀ δ T t)
        ≤ Cp2L * t ^ (-(2:ℝ)/3))
    (hsepR : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * t)) νR)
    (hsepL : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (reflectCurve γ t₀ (0 + lam * t)) νL)
    (hsmallR : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ νR)
    (hsmallL : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ νL) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hR := lagR_bumpCurve_right_le (m := m) (h := h) hm hh (k := k) (i₀ := i₀) hi₀ hδ hlam hT
    hacR hCp2R hνR hUpotBR hsepR hsmallR
  have hL := lagR_bumpCurve_left_le (m := m) (h := h) hm hh (k := k) (i₀ := i₀) hi₀ hδ hlam hT
    hacL hCp2L hνL hUpotBL hsepL hsmallL
  have hbK := bumpKappa_nonneg m k i₀ δ
  have hbc := bumpCross_nonneg hm k
  have hboundR : ∀ᵐ t ∂volume, t ∈ Set.Ioc t₀ (t₀ + lam * T) →
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp ?_
    refine hR.mono fun t ht => ?_
    have h2 : Cp2R * |t - t₀| ^ (-(2:ℝ)/3) ≤ max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    have h3 : bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
        ≤ bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
            + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hbc
      exact le_add_of_nonneg_right (div_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ)))
        (by positivity))
    linarith [ht, h2, h3]
  have hboundL : ∀ᵐ t ∂volume, t ∈ Set.Ioc (t₀ - lam * T) t₀ →
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp ?_
    refine hL.mono fun t ht => ?_
    have h2 : Cp2L * |t - t₀| ^ (-(2:ℝ)/3) ≤ max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)
    have h3 : bumpCross m k * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)
        ≤ bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
            + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hbc
      exact le_add_of_nonneg_left (div_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ)))
        (by positivity))
    linarith [ht, h2, h3]
  have hlowR : ∀ t, t₀ - lam * T < t → t ≤ t₀ - lam * T → False := fun t h1 h2 => absurd h1 (not_lt.mpr h2)
  have hout1 : ∀ᵐ t ∂volume, (t ∈ Set.Ioc a (t₀ - lam * T) ∧ t ≠ t₀ - lam * T) →
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have hlt : lam * T < |t - t₀| := by
      have hpos : 0 < lam * T := mul_pos hlam hT
      have h2 : |t - t₀| ≠ lam * T := by
        intro hcontra
        rcases (abs_eq (mul_nonneg hlam.le hT.le)).mp hcontra with h3 | h3
        · linarith [ht.1.2]
        · exact ht.2 (by linarith)
      have hle : lam * T ≤ |t - t₀| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1.2] : (0:ℝ) ≤ t₀ - t)]
        linarith [ht.1.2]
      exact lt_of_le_of_ne hle (Ne.symm h2)
    rw [deriv_bumpCurve_eq_of_lt hδ hlam hlt, bumpCurve_eq_of_le hδ hlam (le_of_lt hlt)]
    have h1 := lagR_nonneg hm0 hh (γ t) (deriv γ t)
    have h2 : 0 ≤ max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3) :=
      mul_nonneg (le_max_of_le_left hCp2R) (Real.rpow_nonneg (abs_nonneg _) _)
    have h4 : 0 ≤ bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
        + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)) := by
      refine mul_nonneg hbc (add_nonneg ?_ ?_) <;>
        exact div_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ))) (by positivity)
    have h3 : 0 ≤ lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ :=
      mul_nonneg (Real.rpow_nonneg hlam.le _) hbK
    linarith
  have hout2 : ∀ᵐ t ∂volume, (t ∈ Set.Ioc (t₀ + lam * T) b ∧ t ≠ t₀ + lam * T) →
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
    refine Filter.Eventually.of_forall fun t ht => ?_
    have hlt : lam * T < |t - t₀| := by
      have h1 : t₀ + lam * T < t := ht.1.1
      have hpos : 0 < lam * T := mul_pos hlam hT
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [deriv_bumpCurve_eq_of_lt hδ hlam hlt, bumpCurve_eq_of_le hδ hlam (le_of_lt hlt)]
    have h1 := lagR_nonneg hm0 hh (γ t) (deriv γ t)
    have h2 : 0 ≤ max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3) :=
      mul_nonneg (le_max_of_le_left hCp2R) (Real.rpow_nonneg (abs_nonneg _) _)
    have h4 : 0 ≤ bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
        + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)) := by
      refine mul_nonneg hbc (add_nonneg ?_ ?_) <;>
        exact div_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ))) (by positivity)
    have h3 : 0 ≤ lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ :=
      mul_nonneg (Real.rpow_nonneg hlam.le _) hbK
    linarith
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), |t - t₀| ≠ lam * T := by
    have hfin : ({t : ℝ | |t - t₀| = lam * T}).Finite :=
      finite_set_abs_eq (t₀ := t₀) (mul_nonneg hlam.le hT.le)
    rw [MeasureTheory.ae_iff]
    simpa using hfin.measure_zero volume
  have hall : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
      lagR m h (bumpCurve m k i₀ δ T lam t₀ γ t) (deriv (bumpCurve m k i₀ δ T lam t₀ γ) t)
        ≤ 2 * lagR m h (γ t) (deriv γ t)
          + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ
              + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
              + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
                  + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2))) := by
    filter_upwards [hboundR, hboundL, hout1, hout2, hne] with t hRt hLt h1t h2t hnet htmem
    rcases le_or_gt t (t₀ - lam * T) with hle | hgt
    · rcases eq_or_lt_of_le hle with heq | hlt
      · exfalso
        refine hnet ?_
        rw [heq, show t₀ - lam * T - t₀ = -(lam * T) by ring, abs_neg,
          abs_of_pos (mul_pos hlam hT)]
      · exact h1t ⟨⟨htmem.1, le_of_lt hlt⟩, ne_of_lt hlt⟩
    · rcases le_or_gt t t₀ with hle2 | hgt2
      · exact hLt ⟨hgt, hle2⟩
      · rcases le_or_gt t (t₀ + lam * T) with hle3 | hgt3
        · exact hRt ⟨hgt2, hle3⟩
        · exact h2t ⟨⟨hgt3, htmem.2⟩, ne_of_gt hgt3⟩
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr hall

/-- **Finiteness of the action from an integrable domination of the Lagrangian** (on an
almost-everywhere collision-free curve). -/
theorem actionOn_lt_top_of_le_integrable {m : Fin N → ℝ} {h : ℝ} {η : ℝ → EN E N} {a b : ℝ}
    {G : ℝ → ℝ} (hint : Integrable G (volume.restrict (Set.Ioc a b)))
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (η t))
    (hdom : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), lagR m h (η t) (deriv η t) ≤ G t) :
    actionOn m h η a b < ⊤ := by
  rw [actionOn]
  calc ∫⁻ t in Set.Ioc a b, lagrangian m h (η t) (deriv η t)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (η t) (deriv η t)) :=
        lintegral_congr_ae (hnc.mono fun t ht => lagrangian_eq_ofReal_lagR ht)
    _ ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (G t) :=
        lintegral_mono_ae (hdom.mono fun t ht => ENNReal.ofReal_le_ofReal ht)
    _ ≤ ∫⁻ t in Set.Ioc a b, ‖G t‖ₑ := by
        refine lintegral_mono fun t => ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ < ⊤ := hint.hasFiniteIntegral

/-- **Finiteness of the action of the bumped curve.** -/
theorem actionOn_bumpCurve_lt_top {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0)
    {lam T t₀ : ℝ} (hlam : 0 < lam) (hT : 0 < T) {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval γ a b)
    (hfin : actionOn m h γ a b < ⊤)
    (horderL : a ≤ t₀ - lam * T) (horderR : t₀ + lam * T ≤ b)
    (hncηR : ∀ t ∈ Ioo t₀ (t₀ + lam * T),
      WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ t))
    (hncηL : ∀ t ∈ Ioo (t₀ - lam * T) t₀,
      WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ t))
    {Cp2R Cp2L νR νL : ℝ} (hCp2R : 0 ≤ Cp2R) (hCp2L : 0 ≤ Cp2L) (hνR : 0 < νR) (hνL : 0 < νL)
    (hUpotBR : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t) ≤ Cp2R * t ^ (-(2:ℝ)/3))
    (hUpotBL : ∀ t ∈ Ioc (0:ℝ) T, clusterPotential m k
      (bumpRescaled m k (reflectCurve γ t₀) 0 lam t + stdVarVec m k i₀ δ T t)
        ≤ Cp2L * t ^ (-(2:ℝ)/3))
    (hsepR : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * t)) νR)
    (hsepL : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (reflectCurve γ t₀ (0 + lam * t)) νL)
    (hsmallR : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ νR)
    (hsmallL : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ νL) :
    actionOn m h (bumpCurve m k i₀ δ T lam t₀ γ) a b < ⊤ := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hposT : 0 < lam * T := mul_pos hlam hT
  have hacR : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T) := by
    refine hac.mono ?_
    rw [Set.uIcc_of_le (by linarith [hposT.le]), Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc (by linarith [horderL, hposT]) horderR
  have hacL : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) 0 (0 + lam * T) := by
    have h := absolutelyContinuousOnInterval_reflectCurve (t₀ := t₀) hac
    rw [zero_add]
    refine h.mono ?_
    rw [Set.uIcc_of_le (by linarith [hposT.le]), Set.uIcc_of_le (by linarith [hposT.le])]
    exact Set.Icc_subset_Icc (by linarith [horderL]) (by linarith [horderR])
  have hpow : Integrable (fun t : ℝ => |t - t₀| ^ (-(2:ℝ)/3)) (volume.restrict (Set.Ioc a b)) := by
    have h := (Commons.Analysis.Calculus.intervalIntegrable_abs_sub_rpow_of_le
      (c := t₀) (r := -(2:ℝ)/3) (by norm_num) hab).1
    simpa only [IntegrableOn] using h
  have hcst : ∀ C : ℝ, Integrable (fun _ : ℝ => C) (volume.restrict (Set.Ioc a b)) := by
    intro C
    have h := (intervalIntegrable_const (μ := volume) (c := C) (a := a) (b := b)).1
    simpa only [IntegrableOn] using h
  have hncγ : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hfin
  have hL : Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) :=
    integrable_lagR_of_actionOn_lt_top_of_ae hm0 hh hac hncγ hfin
  -- almost-everywhere collision freeness of the bumped curve
  have hncη : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      WithoutCollisions (bumpCurve m k i₀ δ T lam t₀ γ t) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hγ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc a b → WithoutCollisions (γ t) :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mp hncγ
    have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ t₀ := by
      rw [MeasureTheory.ae_iff]
      have hset : {t : ℝ | ¬ t ≠ t₀} = {t₀} := by
        ext t; simp [eq_comm]
      rw [hset]
      simp
    filter_upwards [hγ, hne0] with t hγt hne0t htmem
    by_cases hwin : |t - t₀| < lam * T
    · rcases lt_or_gt_of_ne hne0t with hlt | hgt
      · exact hncηL t ⟨by rw [abs_lt] at hwin; linarith [hwin.1], hlt⟩
      · exact hncηR t ⟨hgt, by rw [abs_lt] at hwin; linarith [hwin.2]⟩
    · rw [bumpCurve_eq_of_le hδ hlam (not_lt.mp hwin)]
      exact hγt htmem
  refine actionOn_lt_top_of_le_integrable (G := fun t => 2 * lagR m h (γ t) (deriv γ t)
      + (lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ + max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3)
          + bumpCross m k * ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
              + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)))) ?_ hncη ?_
  · have hA : Integrable (fun _ : ℝ => lam ^ (-(2:ℝ)/3) * bumpKappa m k i₀ δ)
        (volume.restrict (Set.Ioc a b)) := hcst _
    have hB : Integrable (fun t : ℝ => max Cp2R Cp2L * |t - t₀| ^ (-(2:ℝ)/3))
        (volume.restrict (Set.Ioc a b)) := hpow.const_mul _
    have hC : Integrable (fun _ : ℝ => bumpCross m k *
        ((2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νR ^ 2)
          + (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / νL ^ 2)))
        (volume.restrict (Set.Ioc a b)) := hcst _
    exact (hL.const_mul 2).add ((hA.add hB).add hC)
  · exact lagR_bumpCurve_le_global (m := m) (h := h) hm hh (k := k) (i₀ := i₀) hi₀ hδ hlam hT
      hacR hacL horderL horderR hCp2R hCp2L hνR hνL hUpotBR hUpotBL hsepR hsepL hsmallR hsmallL

end Submission.NBody
