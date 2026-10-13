import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular weight and its first two derivatives on `(0, π/2)` -/

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
abbrev sigE (η θ : ℝ) : ℝ := Real.sin (2 * θ) ^ (-η)

/-- The derivative of `σ` on the open interval: `σ' = -2η cos(2θ) sin(2θ)^{-(1+η)}`. -/
abbrev sigD (η θ : ℝ) : ℝ := -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))

/-- The second derivative of `σ` on the open interval. -/
abbrev sigDD (η θ : ℝ) : ℝ :=
  4 * η * Real.sin (2 * θ) ^ (-η)
    + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))

@[simp] theorem sigE_apply (η θ : ℝ) : sigE η θ = Real.sin (2 * θ) ^ (-η) := rfl

@[simp] theorem sigD_apply (η θ : ℝ) :
    sigD η θ = -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := rfl

@[simp] theorem sigDD_apply (η θ : ℝ) :
    sigDD η θ = 4 * η * Real.sin (2 * θ) ^ (-η)
      + 4 * η * (1 + η) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)) := rfl

/-! ## Derivatives of `σ` and `σ'` -/

/-- `σ` is differentiable on `(0, π/2)` with derivative `σ'`. -/
theorem sigE_hasDerivAt_weak (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => sigE η t) (sigD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hpow := hsin.rpow_const (p := -η) (Or.inl (ne_of_gt hspos))
  have hval : (Real.cos (2 * θ) * 2) * (-η) * Real.sin (2 * θ) ^ (-η - 1) = sigD η θ := by
    rw [sigD_apply]
    have h_exp : -η - 1 = -(1 + η) := by ring
    rw [h_exp]
    ring
  exact hpow.congr_deriv hval

/-- `σ'` is differentiable on `(0, π/2)` with derivative `σ''`. -/
theorem sigD_hasDerivAt_weak (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => sigD η t) (sigDD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * 2) θ := hlin.cos
  have hpow : HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(1 + η)))
      ((Real.cos (2 * θ) * 2) * (-(1 + η)) * Real.sin (2 * θ) ^ (-(1 + η) - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hspos))
  have hprod := (hcos.mul hpow).const_mul (-2 * η)
  have hfun : (fun t : ℝ => sigD η t)
      = fun y => -2 * η * (((fun t : ℝ => Real.cos (2 * t))
          * fun t : ℝ => Real.sin (2 * t) ^ (-(1 + η))) y) := by
    funext y
    simp only [Pi.mul_apply, sigD_apply]
    ring
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [sigDD_apply]
  have h2 : Real.sin (2 * θ) ^ (-(1 + η) - 1) = Real.sin (2 * θ) ^ (-(2 + η)) := by
    congr 1
    ring
  have h1 : Real.sin (2 * θ) ^ (-(1 + η))
      = Real.sin (2 * θ) ^ (-η) / Real.sin (2 * θ) := by
    rw [eq_div_iff hspos.ne', ← Real.rpow_add_one hspos.ne']
    congr 1
    ring
  rw [h1, h2]
  field_simp
  ring

/-- The absolute value of `σ'` on `(0, π/2)`. -/
theorem abs_sigD_le (η : ℝ) (hη0 : 0 ≤ η) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have ht : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(1 + η)) := Real.rpow_nonneg hspos.le _
  rw [sigD_apply, abs_mul, abs_mul, abs_mul,
    show |(-2 : ℝ)| = 2 by norm_num, abs_of_nonneg hη0, abs_of_nonneg ht]
  calc 2 * η * |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-(1 + η))
      ≤ 2 * η * 1 * Real.sin (2 * θ) ^ (-(1 + η)) := by
        refine mul_le_mul_of_nonneg_right ?_ ht
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := by ring

/-! ## An elementary one-sided squeeze -/

theorem tendsto_zero_of_eventually_le {f g : ℝ → ℝ} {l : Filter ℝ}
    (hf : ∀ᶠ t in l, 0 ≤ f t) (hfg : ∀ᶠ t in l, f t ≤ g t) (hg : Tendsto g l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hf] with t ht
    linarith
  · have h := (tendsto_order.mp hg).2 b hb
    filter_upwards [h, hfg] with t ht hle
    linarith

/-! ## Integrability of the six pieces of the two integrations by parts -/

/-- All the integrands appearing in the two integrations by parts are integrable on `Iθ`, under
the weak hypotheses `|f| ≤ M sin(2θ)`, `|f'| ≤ M` on the *open* interval and the integrability
of `(f'')² σ`. -/
theorem weak_integrands_integrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hint : IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => deriv f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * sigE η θ) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.Spaces.Iθ
      ∧ IntegrableOn (fun θ => f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hres : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hsin_pos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsig_int : Integrable (fun θ : ℝ => sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hres]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mp
      (Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith))
  have hint' : Integrable (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hres]
    exact hint
  have hf_aesm : AEStronglyMeasurable f (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hf.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hfd_aesm : AEStronglyMeasurable (deriv f)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv f).aestronglyMeasurable
  have hfdd_aesm : AEStronglyMeasurable (deriv (deriv f))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (measurable_deriv (deriv f)).aestronglyMeasurable
  have hsig_cont : ContinuousOn (fun θ : ℝ => sigE η θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsig_aesm : AEStronglyMeasurable (fun θ : ℝ => sigE η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsig_cont.aestronglyMeasurable measurableSet_Ioo
  have hcos2_aesm : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).continuousOn
      ).aestronglyMeasurable measurableSet_Ioo
  have hsinD_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(1 + η)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))
  have hsin2_aesm : AEStronglyMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(2 + η)))
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsin_pos θ hθ)))).aestronglyMeasurable measurableSet_Ioo
  have hsigD_aesm : AEStronglyMeasurable (fun θ : ℝ => sigD η θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    change AEStronglyMeasurable
      (fun θ : ℝ => -2 * η * Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))) _
    have hcos_cont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hmain : AEStronglyMeasurable
        (fun θ : ℝ => -2 * η * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((hcos_cont.mul hsinD_cont).const_mul (-2 * η)).aestronglyMeasurable measurableSet_Ioo
    simpa only [mul_assoc] using hmain
  have h1 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact (hfd_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg (hsin_pos θ hθ).le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hσ]
      have hfd : |deriv f θ| ≤ M := hdb θ hθ
      have h2 : deriv f θ ^ 2 ≤ M ^ 2 := by
        calc deriv f θ ^ 2 = |deriv f θ| ^ 2 := (sq_abs _).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfd 2
      exact mul_le_mul_of_nonneg_right h2 hσ
  have h2i : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    have hmaj : Integrable
        (fun θ : ℝ => (1 / 2) * (M ^ 2 * sigE η θ + (deriv (deriv f) θ) ^ 2 * sigE η θ))
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      ((hsig_int.const_mul (M ^ 2)).add hint').const_mul (1 / 2)
    refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
    · exact (hf_aesm.mul hfdd_aesm).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg (hsin_pos θ hθ).le _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hσ]
      have hspos := hsin_pos θ hθ
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have haM : |f θ| ≤ M := by
        have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        nlinarith [ha, hsin1, hM, hspos]
      have hamgm : 2 * (|f θ| * |deriv (deriv f) θ|) ≤ M ^ 2 + deriv (deriv f) θ ^ 2 := by
        have hA : 2 * (|f θ| * |deriv (deriv f) θ|)
            ≤ |f θ| ^ 2 + |deriv (deriv f) θ| ^ 2 := by
          nlinarith [sq_nonneg (|f θ| - |deriv (deriv f) θ|)]
        have hB : |f θ| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) haM 2
        have hC : |deriv (deriv f) θ| ^ 2 = deriv (deriv f) θ ^ 2 := sq_abs _
        linarith [hA, hB, hC]
      have hle : |f θ| * |deriv (deriv f) θ| ≤ (M ^ 2 + deriv (deriv f) θ ^ 2) / 2 := by
        linarith
      calc |f θ| * |deriv (deriv f) θ| * sigE η θ
          = (|f θ| * |deriv (deriv f) θ|) * sigE η θ := by ring
        _ ≤ ((M ^ 2 + deriv (deriv f) θ ^ 2) / 2) * sigE η θ :=
            mul_le_mul_of_nonneg_right hle hσ
        _ = (1 / 2) * (M ^ 2 * sigE η θ + (deriv (deriv f) θ) ^ 2 * sigE η θ) := by ring
  have h3i : IntegrableOn (fun θ : ℝ => f θ * deriv f θ * sigD η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (2 * η * M ^ 2)) ?_ ?_
    · exact (hf_aesm.mul hfd_aesm).mul hsigD_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have hb : |deriv f θ| ≤ M := hdb θ hθ
      have hsd : |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := abs_sigD_le η hη0 hθ
      have ht : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (-(1 + η)) := Real.rpow_nonneg hspos.le _
      have hA : |f θ| * |deriv f θ| ≤ (M * Real.sin (2 * θ)) * M :=
        mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hM hspos.le)
      have h2 : |f θ| * |deriv f θ| * |sigD η θ|
          ≤ ((M * Real.sin (2 * θ)) * M) * (2 * η * Real.sin (2 * θ) ^ (-(1 + η))) :=
        mul_le_mul hA hsd (abs_nonneg _) (mul_nonneg (mul_nonneg hM hspos.le) hM)
      refine le_trans h2 ?_
      have h3 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))
          = Real.sin (2 * θ) ^ (-η) := by
        rw [mul_comm, ← Real.rpow_add_one hspos.ne' (-(1 + η))]
        congr 1
        ring
      exact le_of_eq (by
        rw [sigE_apply]
        calc ((M * Real.sin (2 * θ)) * M) * (2 * η * Real.sin (2 * θ) ^ (-(1 + η)))
            = 2 * η * M ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η))) := by ring
          _ = 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (-η) := by rw [h3])
  have h4 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigE η θ) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact (hf_aesm.pow 2).mul hsig_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      have hσ : (0 : ℝ) ≤ sigE η θ := Real.rpow_nonneg hspos.le _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hσ]
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      have haM : |f θ| ≤ M := by
        have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        nlinarith [ha, hsin1, hM, hspos]
      have hf2 : f θ ^ 2 ≤ M ^ 2 := by
        calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) haM 2
      exact mul_le_mul_of_nonneg_right hf2 hσ
  have h5 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + η))) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn, hres]
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul (M ^ 2)) ?_ ?_
    · exact ((hf_aesm.pow 2).mul hcos2_aesm).mul hsin2_aesm
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hspos := hsin_pos θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
        abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))),
        abs_of_nonneg (Real.rpow_nonneg hspos.le _)]
      have hc : Real.cos (2 * θ) ^ 2 ≤ 1 := by
        have h := Real.abs_cos_le_one (2 * θ)
        nlinarith [abs_nonneg (Real.cos (2 * θ)), sq_abs (Real.cos (2 * θ)), h]
      have hf2 : f θ ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
        have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
        calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
          _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
      have h3 : Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))
          = Real.sin (2 * θ) ^ (-η) := by
        have h4' : Real.sin (2 * θ) ^ 2 = Real.sin (2 * θ) ^ (2 : ℝ) :=
          (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
        rw [h4', ← Real.rpow_add hspos]
        congr 1
        ring
      calc f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))
          ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * Real.sin (2 * θ) ^ (-(2 + η)) := by
            refine mul_le_mul (mul_le_mul hf2 hc (sq_nonneg _) (sq_nonneg _)) (le_refl _)
              (Real.rpow_nonneg hspos.le _) (mul_nonneg (sq_nonneg _) zero_le_one)
        _ = M ^ 2 * (Real.sin (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))) := by ring
        _ = M ^ 2 * sigE η θ := by rw [h3, sigE_apply]
  have h6 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ := by
    have hsum : Integrable (fun θ : ℝ => 4 * η * (f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η)))) (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Integrable.const_mul h4 (4 * η)).add
        (MeasureTheory.Integrable.const_mul h5 (4 * η * (1 + η)))
    refine hsum.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [sigDD_apply, sigE_apply]
    ring
  exact ⟨h1, h2i, h3i, h4, h5, h6⟩

/-! ## Vanishing of the two fluxes at both endpoints -/

/-- The two fluxes `f f' σ` and `f² σ'` vanish at `θ → 0⁺` and `θ → (π/2)⁻`, from the
bounds `|f θ| ≤ M sin(2θ)` and `|f' θ| ≤ M` on the open interval. -/
theorem weak_boundary_tendsto (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M) :
    Tendsto (fun θ => f θ * deriv f θ * sigE η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ * deriv f θ * sigE η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Tendsto (fun θ => f θ ^ 2 * sigD η θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have h4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hη1' : (0 : ℝ) < 1 - η := by linarith
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT h4]
    exact self_mem_nhdsWithin
  have hmemπ : Set.Ioo (Real.pi / 4) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (by linarith : Real.pi / 4 < Real.pi / 2)]
    exact self_mem_nhdsWithin
  -- pointwise estimates on the open interval
  have key1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ * deriv f θ * sigE η θ| ≤ M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hspos.le (-η))]
    have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
    have hb : |deriv f θ| ≤ M := hdb θ hθ
    have h3 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η) = Real.sin (2 * θ) ^ (1 - η) := by
      rw [mul_comm, ← Real.rpow_add_one hspos.ne' (-η)]
      congr 1
      ring
    have hA : (|f θ| * |deriv f θ|) * Real.sin (2 * θ) ^ (-η)
        ≤ ((M * Real.sin (2 * θ)) * M) * Real.sin (2 * θ) ^ (-η) :=
      mul_le_mul_of_nonneg_right (mul_le_mul ha hb (abs_nonneg _) (mul_nonneg hM hspos.le))
        (Real.rpow_nonneg hspos.le _)
    refine le_trans hA ?_
    exact le_of_eq (by
      calc ((M * Real.sin (2 * θ)) * M) * Real.sin (2 * θ) ^ (-η)
          = M ^ 2 * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-η)) := by ring
        _ = M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by rw [h3])
  have key2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ ^ 2 * sigD η θ| ≤ 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ))]
    have hf2 : f θ ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
      have ha : |f θ| ≤ M * Real.sin (2 * θ) := hfb θ hθ
      calc f θ ^ 2 = |f θ| ^ 2 := (sq_abs _).symm
        _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hsd : |sigD η θ| ≤ 2 * η * Real.sin (2 * θ) ^ (-(1 + η)) := abs_sigD_le η hη0 hθ
    have hA : f θ ^ 2 * |sigD η θ|
        ≤ (M * Real.sin (2 * θ)) ^ 2 * (2 * η * Real.sin (2 * θ) ^ (-(1 + η))) :=
      mul_le_mul hf2 hsd (abs_nonneg _) (sq_nonneg _)
    refine le_trans hA ?_
    have hp : Real.sin (2 * θ) ^ (1 - η)
        = Real.sin (2 * θ) ^ (-(1 + η)) * Real.sin (2 * θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hspos]
      congr 1
      ring
    exact le_of_eq (by
      calc (M * Real.sin (2 * θ)) ^ 2 * (2 * η * Real.sin (2 * θ) ^ (-(1 + η)))
          = 2 * η * M ^ 2
              * (Real.sin (2 * θ) ^ (-(1 + η)) * Real.sin (2 * θ) ^ 2) := by ring
        _ = 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η) := by rw [← hp])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ => M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      simpa only [Real.norm_eq_abs] using key1 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_right (1 - η) hη1').const_mul (M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le (g := fun θ : ℝ => M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simpa only [Real.norm_eq_abs] using key1 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hη1').const_mul (M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le
      (g := fun θ : ℝ => 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmem0] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
      simpa only [Real.norm_eq_abs] using key2 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_right (1 - η) hη1').const_mul (2 * η * M ^ 2)
      simpa using h
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_zero_of_eventually_le
      (g := fun θ : ℝ => 2 * η * M ^ 2 * Real.sin (2 * θ) ^ (1 - η))
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) ?_ ?_
    · filter_upwards [hmemπ] with θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      simpa only [Real.norm_eq_abs] using key2 θ hθI
    · have h := (Work.FTS.H2.tendsto_sin_rpow_zero_left (1 - η) hη1').const_mul (2 * η * M ^ 2)
      simpa using h

/-- **The two integrations by parts for a weak `C²` angular slice, combined into one identity.**

For `0 ≤ η < 1`, `f` of class `C²` on the open interval `(0, π/2)`, `M ≥ 0` with
`|f θ| ≤ M sin(2θ)` and `|deriv f θ| ≤ M` on `(0, π/2)`, and `(f'')² sin(2θ)^{-η}` integrable on
`Iθ = [0, π/2]`:

  `∫_{Iθ} (f')² σ = -∫_{Iθ} f f'' σ + 2η ∫_{Iθ} f² σ + 2η(1+η) ∫_{Iθ} f² cos²(2θ) sin(2θ)^{-(2+η)}`,
  `σ = sin(2θ)^{-η}`.

Route (this is the weak-class version of the *proved* `Work.FTS.EllipticEst.remov.slice_ibp_sigma_fts`,
which does exactly this for `f` of class `C²` on the *closed* interval with `f 0 = f (π/2) = 0`;
that file's `sigD_hasDerivAt_fts` is the model for the derivative of `σ`).  Two fluxes:
`Φ₁ = f f' σ` (so `Φ₁' = (f')²σ + f f''σ + f f' σ'`) and `Φ₂ = f² σ'` (so `Φ₂' = 2 f f' σ' + f² σ''`);
`Work.FTS.EllipticEst.AngSecond.slice_ftc_zero` applied to each gives `∫Φ₁' = 0`, `∫Φ₂' = 0`;
substituting the second into the first and expanding
`σ'' = 4η σ + 4η(1+η) cos²(2θ) sin(2θ)^{-(2+η)}` gives the identity.  All boundary terms vanish
because `|Φ₁| ≤ M² sin(2θ)^{1-η}` and `|Φ₂| ≤ 2η M² sin(2θ)^{1-η}`, and the integrands of the two
derivatives are integrable: `(f')²σ ≤ M²σ`, `f f' σ' ≤ 2ηM²σ`, `f²σ ≤ M² sin(2θ)^{2-η}`, and
`∫|f f''|σ < ∞` by Cauchy–Schwarz against the hypothesis, with
`Work.FTS.H2.intervalIntegrable_of_sin_bound` with `p = -η > -1` together with
`MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc` to pass from the
open-interval continuity to `Iθ`. -/
theorem sliceIbpSigmaWeakFts (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (f : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hfb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
  suffices key : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
      = -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + η))) by
    simpa only [sigE_apply] using key
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ :=
    weak_integrands_integrable η hη0 hη1 f M hM hf hfb hdb hint
  obtain ⟨hb1, hb2, hb3, hb4⟩ := weak_boundary_tendsto η hη0 hη1 f M hM hfb hdb
  -- `f` is `C²` at interior points, so its first and second derivatives exist there.
  have hcd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 2 f θ := by
    intro θ hθ
    exact (hf θ hθ).contDiffAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hdf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd θ hθ).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) θ) θ := fun θ hθ =>
    (((hcd θ hθ).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- The first integration by parts.
  have hA_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t * deriv f t * sigE η t)
        (deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
          + f θ * deriv f θ * sigD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hddf θ hθ)).mul (sigE_hasDerivAt_weak η hθ)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hA_int : IntervalIntegrable (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
        Work.Spaces.Iθ := (hI1.add hI2).add hI3
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hA_zero : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
      + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
      (fun t : ℝ => f t * deriv f t * sigE η t)
      (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ + f θ * deriv (deriv f) θ * sigE η θ
        + f θ * deriv f θ * sigD η θ) hA_deriv hA_int hb1 hb2
  have hA_split : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ + f θ * deriv f θ * sigD η θ)
      = (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ) := by
    have h12 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigE η θ
        + f θ * deriv (deriv f) θ * sigE η θ) Work.Spaces.Iθ := hI1.add hI2
    rw [MeasureTheory.integral_add h12 hI3, MeasureTheory.integral_add hI1 hI2]
  -- The second integration by parts.
  have hB_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t ^ 2 * sigD η t)
        (2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hdf θ hθ)).mul (sigD_hasDerivAt_weak η hθ)
    have hfun : (f * f) * (fun t : ℝ => sigD η t)
        = fun t : ℝ => f t ^ 2 * sigD η t := by
      funext t
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hB_int : IntervalIntegrable (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : IntegrableOn (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ) Work.Spaces.Iθ :=
      (MeasureTheory.Integrable.const_mul hI3 2).add hI6
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hB_zero : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
      + f θ ^ 2 * sigDD η θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t ^ 2 * sigD η t)
      (fun θ : ℝ => 2 * (f θ * deriv f θ * sigD η θ) + f θ ^ 2 * sigDD η θ)
      hB_deriv hB_int hb3 hb4
  -- Expand `σ''`.
  have hI6_eq : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ)
      = 4 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ)
        + 4 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ,
            f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η))) := by
    have hfun : (fun θ => f θ ^ 2 * sigDD η θ)
        = (fun θ => 4 * η * (f θ ^ 2 * sigE η θ)
            + 4 * η * (1 + η) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
                * Real.sin (2 * θ) ^ (-(2 + η)))) := by
      funext θ
      simp only [sigDD_apply, sigE_apply]
      ring
    rw [hfun, MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hI4 (4 * η))
        (MeasureTheory.Integrable.const_mul hI5 (4 * η * (1 + η))),
      MeasureTheory.integral_const_mul (4 * η) (fun θ => f θ ^ 2 * sigE η θ),
      MeasureTheory.integral_const_mul (4 * η * (1 + η))
        (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (-(2 + η)))]
  have hB_split : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigD η θ)
        + f θ ^ 2 * sigDD η θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ)
        + (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDD η θ) := by
    rw [MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hI3 2) hI6,
      MeasureTheory.integral_const_mul 2 (fun θ => f θ * deriv f θ * sigD η θ)]
  -- Assemble.
  set a := ∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigE η θ with ha
  set b := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigE η θ with hb
  set c := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigD η θ with hc
  set d := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigE η θ with hd
  set e := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
    * (Real.sin (2 * θ)) ^ (-(2 + η)) with he
  have h1' : a + b + c = 0 := by
    rw [← hA_split]; exact hA_zero
  have h2' : 2 * c + (4 * η * d + 4 * η * (1 + η) * e) = 0 := by
    rw [← hI6_eq, ← hB_split]; exact hB_zero
  have hmain : a = -b + 2 * η * d + 2 * η * (1 + η) * e := by linarith
  exact hmain

end Work.FTS.EllipticEst.AngAWeak
