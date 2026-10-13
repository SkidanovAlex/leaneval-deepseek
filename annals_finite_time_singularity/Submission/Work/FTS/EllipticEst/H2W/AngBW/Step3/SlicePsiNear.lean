import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_wrho_products
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.Honest.integrableOn_of_sin_sq_mul
import Submission.Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest

set_option autoImplicit false


set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

private lemma pi_div_four_pos : (0 : ℝ) < Real.pi / 4 := by positivity

private lemma sig_pos_of_mem_Ioo_pi4 {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) : 0 < σ θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact Real.rpow_pos_of_pos hsin _

private lemma sig_nonneg_of_mem_Icc_pi4 {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) : 0 ≤ σ θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

private lemma integrableOn_sig_pi4 : IntegrableOn σ (Set.Ioo 0 (Real.pi / 4)) := by
  refine (Work.FTS.EllipticEst.TanTheta.integrableOn_sin_two_rpow_neg (η := Work.Spaces.eta)
    Work.Spaces.eta_lt_one).mono_set ?_
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

/-- **The interpolation bound for the first derivative.** -/
private lemma deriv_sq_le_of_mem (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {A θ : ℝ} (hA0 : 0 < A) (hAle : A ≤ Real.pi / 4) (hθ : θ ∈ Set.Ioo 0 A)
    (hX' : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioo 0 A)) :
    (deriv u θ) ^ 2 ≤ 2 * (deriv u A) ^ 2
      + 2 * ((2 * A) ^ (Work.Spaces.eta) * A)
        * (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z) := by
  have hθle : θ ≤ A := le_of_lt hθ.2
  have hAle2 : A < Real.pi / 2 := by linarith [hAle, Real.pi_pos]
  have huIoc : Set.uIcc θ A ⊆ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθle]
    intro x hx
    exact ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hAle2⟩
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv : ∀ x ∈ Set.uIcc θ A, DifferentiableAt ℝ (deriv u) x := by
    intro x hx
    exact (hd1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds (huIoc hx))
  have hint : IntervalIntegrable (deriv (deriv u)) volume θ A := by
    have hcont : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
      hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)
    exact (hcont.mono huIoc).intervalIntegrable
  have hFTC : (∫ x in θ..A, deriv (deriv u) x) = deriv u A - deriv u θ :=
    intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hZint : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioc θ A) :=
    (hX'.mono_set (fun z hz => ⟨lt_trans hθ.1 hz.1, hz.2⟩)).congr_set_ae
      (MeasureTheory.Ioo_ae_eq_Ioc (a := θ) (b := A)).symm
  have hcontSin : ContinuousOn (fun z : ℝ => (Real.sin (2 * z)) ^ (Work.Spaces.eta))
      (Set.Icc θ A) := by
    refine ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const ?_
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hθ.1 hz.1
    have h2z0 : (0 : ℝ) < 2 * z := by linarith
    have h2zp : 2 * z < Real.pi := by linarith [hz.2, hAle2, Real.pi_pos]
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2z0 h2zp))
  have hWint : IntegrableOn (fun z => (Real.sin (2 * z)) ^ (Work.Spaces.eta)) (Set.Ioc θ A) :=
    (hcontSin.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hcontV : ContinuousOn (deriv (deriv u)) (Set.Icc θ A) := by
    have h := (hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono huIoc
    rwa [Set.uIcc_of_le hθle] at h
  have hCint : IntegrableOn (fun z => |deriv (deriv u) z|) (Set.Ioc θ A) :=
    (hcontV.abs.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hpt : ∀ z ∈ Set.Ioc θ A,
      |(|deriv (deriv u) z|)| ≤ Real.sqrt ((deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt ((Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
    intro z hz
    have hs : 0 < Real.sin (2 * z) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hz.1, hθ.1]) (by linarith [hz.2, hAle2])
    have hsq : Real.sqrt ((deriv (deriv u) z) ^ 2 * σ z)
        = |deriv (deriv u) z| * Real.sqrt (σ z) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have hσnn : 0 ≤ σ z := le_of_lt (Real.rpow_pos_of_pos hs _)
    have hone : Real.sqrt (σ z) * Real.sqrt ((Real.sin (2 * z)) ^ (Work.Spaces.eta)) = 1 := by
      rw [← Real.sqrt_mul (x := σ z) hσnn]
      have h1 : σ z * (Real.sin (2 * z)) ^ (Work.Spaces.eta) = 1 := by
        change (Real.sin (2 * z)) ^ (-(Work.Spaces.eta)) * (Real.sin (2 * z)) ^ (Work.Spaces.eta)
          = 1
        rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
      rw [h1, Real.sqrt_one]
    rw [abs_abs, hsq, mul_assoc, hone, mul_one]
  have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt hZint hWint hCint
    (fun z hz => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem_Icc_pi4
      ⟨le_of_lt (lt_trans hθ.1 hz.1), le_trans hz.2 hAle⟩))
    (fun z hz => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
      (by linarith [hz.2, hAle2, Real.pi_pos])) _)
    hpt
  have hIabs : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ≤
      Real.sqrt (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
    rw [abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _))] at hcs
    exact hcs
  have hZb : (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
      ≤ ∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z := by
    refine MeasureTheory.setIntegral_mono_set hX' ?_ ?_
    · show ∀ᵐ z ∂(volume.restrict (Set.Ioo 0 A)), 0 ≤ (deriv (deriv u) z) ^ 2 * σ z
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Eventually.of_forall (fun z hz => mul_nonneg (sq_nonneg _)
        (sig_nonneg_of_mem_Icc_pi4 ⟨by linarith [hz.1], by linarith [hz.2, Real.pi_pos]⟩))
    · rw [MeasureTheory.ae_le_set]
      refine measure_mono_null ?_ (measure_singleton A)
      intro z hz
      rw [Set.mem_singleton_iff]
      rcases lt_or_eq_of_le hz.1.2 with h | h
      · exact absurd ⟨lt_trans hθ.1 hz.1.1, h⟩ hz.2
      · exact h
  have hWb : (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))
      ≤ (2 * A) ^ (Work.Spaces.eta) * A := by
    rw [← intervalIntegral.integral_of_le hθle]
    have hle : ∀ z ∈ Set.Icc θ A,
        (Real.sin (2 * z)) ^ (Work.Spaces.eta) ≤ (2 * A) ^ (Work.Spaces.eta) := by
      intro z hz
      have h1 : Real.sin (2 * z) ≤ 2 * z := Real.sin_le (by linarith [hz.1, hθ.1])
      have h2 : (0 : ℝ) ≤ Real.sin (2 * z) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
          (by linarith [hz.2, hAle2, Real.pi_pos])
      have h3 : (Real.sin (2 * z)) ^ (Work.Spaces.eta) ≤ (2 * z) ^ (Work.Spaces.eta) :=
        Real.rpow_le_rpow h2 h1 Work.Spaces.eta_nonneg
      have h4 : (2 * z) ^ (Work.Spaces.eta) ≤ (2 * A) ^ (Work.Spaces.eta) :=
        Real.rpow_le_rpow (by linarith [hz.1, hθ.1]) (by linarith [hz.2]) Work.Spaces.eta_nonneg
      linarith
    have hkey : (∫ x in θ..A, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
        ≤ ∫ x in θ..A, (2 * A) ^ (Work.Spaces.eta) :=
      intervalIntegral.integral_mono_on hθle (hcontSin.intervalIntegrable_of_Icc hθle)
        intervalIntegrable_const hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hkey
    have h1 : (A - θ) * (2 * A) ^ (Work.Spaces.eta)
        ≤ A * (2 * A) ^ (Work.Spaces.eta) :=
      mul_le_mul_of_nonneg_right (by linarith [hθ.1]) (Real.rpow_nonneg (by linarith [hA0]) _)
    have h2 : A * (2 * A) ^ (Work.Spaces.eta) = (2 * A) ^ (Work.Spaces.eta) * A := by ring
    linarith [hkey, h1, h2]
  have hZ0 : 0 ≤ ∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z :=
    setIntegral_nonneg measurableSet_Ioc (fun z hz => mul_nonneg (sq_nonneg _)
      (sig_nonneg_of_mem_Icc_pi4 ⟨le_of_lt (lt_trans hθ.1 hz.1), le_trans hz.2 hAle⟩))
  have hW0 : 0 ≤ ∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta) :=
    setIntegral_nonneg measurableSet_Ioc (fun z hz => Real.rpow_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hz.1, hθ.1])
        (by linarith [hz.2, hAle2, Real.pi_pos])) _)
  have hI2 : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2
      ≤ (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A) := by
    have h1 : (Real.sqrt (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * Real.sqrt (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))) ^ 2
        = (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
          * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
      rw [mul_pow, Real.sq_sqrt hZ0, Real.sq_sqrt hW0]
    have h2 : (∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2
        ≤ (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
          * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta)) := by
      have h3 := pow_le_pow_left₀ (setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _))
        hIabs 2
      rwa [h1] at h3
    have h4 : (∫ z in Set.Ioc θ A, (deriv (deriv u) z) ^ 2 * σ z)
        * (∫ z in Set.Ioc θ A, (Real.sin (2 * z)) ^ (Work.Spaces.eta))
        ≤ (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A) :=
      mul_le_mul hZb hWb hW0 (le_trans hZ0 hZb)
    linarith
  have hintI : (∫ x in θ..A, |deriv (deriv u) x|) = ∫ z in Set.Ioc θ A, |deriv (deriv u) z| :=
    intervalIntegral.integral_of_le hθle
  have habs : |deriv u θ| ≤ |deriv u A| + ∫ x in θ..A, |deriv (deriv u) x| := by
    have h1 : deriv u θ = deriv u A - ∫ x in θ..A, deriv (deriv u) x := by linarith [hFTC]
    have h2 : |∫ x in θ..A, deriv (deriv u) x| ≤ ∫ x in θ..A, |deriv (deriv u) x| :=
      intervalIntegral.abs_integral_le_integral_abs hθle
    calc |deriv u θ| = |deriv u A - ∫ x in θ..A, deriv (deriv u) x| := by rw [h1]
      _ ≤ |deriv u A| + |∫ x in θ..A, deriv (deriv u) x| := by
          refine (abs_sub_le_iff (b := ∫ x in θ..A, deriv (deriv u) x)
            (c := |deriv u A| + |∫ x in θ..A, deriv (deriv u) x|)).mpr ⟨?_, ?_⟩
          · linarith [le_abs_self (deriv u A), neg_le_abs (∫ x in θ..A, deriv (deriv u) x)]
          · linarith [neg_le_abs (deriv u A), le_abs_self (∫ x in θ..A, deriv (deriv u) x)]
      _ ≤ |deriv u A| + ∫ x in θ..A, |deriv (deriv u) x| := by linarith
  have hYnn : 0 ≤ ∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z :=
    setIntegral_nonneg measurableSet_Ioo (fun z hz => mul_nonneg (sq_nonneg _)
      (sig_nonneg_of_mem_Icc_pi4 ⟨by linarith [hz.1], by linarith [hz.2, Real.pi_pos]⟩))
  have hWnn : 0 ≤ (2 * A) ^ (Work.Spaces.eta) * A :=
    mul_nonneg (Real.rpow_nonneg (by linarith [hA0]) _) (le_of_lt hA0)
  have hIle : (∫ x in θ..A, |deriv (deriv u) x|)
      ≤ Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A)) := by
    rw [hintI]
    have h0 : 0 ≤ ∫ z in Set.Ioc θ A, |deriv (deriv u) z| :=
      setIntegral_nonneg measurableSet_Ioc (fun z _ => abs_nonneg _)
    have h3 : Real.sqrt ((∫ z in Set.Ioc θ A, |deriv (deriv u) z|) ^ 2)
        ≤ Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A)) := Real.sqrt_le_sqrt hI2
    rwa [Real.sqrt_sq h0] at h3
  have hp : |deriv u θ| ≤ |deriv u A|
      + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A)) := by
    linarith
  have h1 : (deriv u θ) ^ 2 ≤ (|deriv u A|
      + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2 := by
    have h' : |deriv u θ| ^ 2 ≤ (|deriv u A|
        + Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
          * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hp 2
    rwa [sq_abs] at h'
  have hs2 : (Real.sqrt ((∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
      * ((2 * A) ^ (Work.Spaces.eta) * A))) ^ 2
      = (∫ z in Set.Ioo 0 A, (deriv (deriv u) z) ^ 2 * σ z)
        * ((2 * A) ^ (Work.Spaces.eta) * A) := Real.sq_sqrt (mul_nonneg hYnn hWnn)
  nlinarith [h1, hs2, sq_nonneg (|deriv u A| - Real.sqrt ((∫ z in Set.Ioo 0 A,
      (deriv (deriv u) z) ^ 2 * σ z) * ((2 * A) ^ (Work.Spaces.eta) * A))),
    sq_abs (deriv u A)]

/-! ## Conjunct 1 -/

private lemma integrableOn_div_cos_sq (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) := by
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hF : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) :=
    hB.mono_set hsub
  have hcont : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 4)) :=
    continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2) (fun θ hθ => by
      have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
      positivity)
  have hbdd : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
      ‖1 / Real.cos θ ^ 2‖ ≤ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun θ hθ => by
      have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 4) hθ.1.le
          (by linarith [Real.pi_pos]) hθ.2.le
        rwa [Real.cos_pi_div_four] at h
      have hcospos : 0 < Real.cos θ := lt_of_lt_of_le (by positivity) hcos
      have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
        have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [← h2]
        exact pow_le_pow_left₀ (by positivity) hcos 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.cos θ ^ 2)]
      linarith)
  have hI := hF.mul_bdd (hcont.aestronglyMeasurable measurableSet_Ioo) hbdd
  refine hI.congr ?_
  show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
    u θ ^ 2 * σ θ * (1 / Real.cos θ ^ 2) = (u θ / Real.cos θ) ^ 2 * σ θ
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall (fun θ hθ => by
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [div_pow]
    ring)

/-! ## Conjunct 2 -/

/-- The derivative of `θ ↦ u θ / cos θ`, in the single-fraction form. -/
private lemma deriv_div_cos_formula (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2 := by
  have hmem : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hd : HasDerivAt u (deriv u θ) θ :=
    ((hu.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)).hasDerivAt
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hmem.2⟩)
  have hdiv : HasDerivAt (fun t => u t / Real.cos t)
      ((deriv u θ * Real.cos θ - u θ * (-Real.sin θ)) / Real.cos θ ^ 2) θ :=
    hd.div (Real.hasDerivAt_cos θ) hcos
  rw [hdiv.deriv]
  rw [show deriv u θ * Real.cos θ - u θ * (-Real.sin θ)
      = deriv u θ * Real.cos θ + u θ * Real.sin θ by ring]

private lemma psi'_sq_le (u : ℝ → ℝ) (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (fun t => u t / Real.cos t) θ) ^ 2 * σ θ
      ≤ 4 * ((deriv u θ) ^ 2 * σ θ) + 8 * ((u θ) ^ 2 * σ θ) := by
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := Real.pi / 4) hθ.1.le
      (by linarith [Real.pi_pos]) hθ.2.le
    rwa [Real.cos_pi_div_four] at h
  have hcospos : 0 < Real.cos θ := lt_of_lt_of_le (by positivity) hcos
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) hcos 2
  have hsin2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hσ : 0 ≤ σ θ := le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ)
  rw [deriv_div_cos_formula u hu hθ]
  have hkey : ((deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2) ^ 2
      ≤ 4 * (deriv u θ) ^ 2 + 8 * (u θ) ^ 2 := by
    have hden : 0 < (Real.cos θ ^ 2) ^ 2 := by positivity
    rw [div_pow, div_le_iff₀ hden]
    have hA : (1 : ℝ) ≤ 4 * (Real.cos θ ^ 2) ^ 2 := by nlinarith [hcos2]
    have hB : (1 : ℝ) ≤ 2 * Real.cos θ ^ 2 := by linarith
    have h1 : (deriv u θ * Real.cos θ + u θ * Real.sin θ) ^ 2
        ≤ 2 * (deriv u θ * Real.cos θ) ^ 2 + 2 * (u θ * Real.sin θ) ^ 2 := by
      nlinarith [sq_nonneg (deriv u θ * Real.cos θ - u θ * Real.sin θ)]
    have h2 : 2 * (u θ * Real.sin θ) ^ 2 ≤ 8 * (u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by
      have hs4 : Real.sin θ ^ 2 ≤ 4 * (Real.cos θ ^ 2) ^ 2 := le_trans hsin2 hA
      calc 2 * (u θ * Real.sin θ) ^ 2 = 2 * (u θ) ^ 2 * Real.sin θ ^ 2 := by ring
        _ ≤ 2 * (u θ) ^ 2 * (4 * (Real.cos θ ^ 2) ^ 2) :=
              mul_le_mul_of_nonneg_left hs4 (by positivity)
        _ = 8 * (u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by ring
    have h3 : 2 * (deriv u θ * Real.cos θ) ^ 2
        ≤ 4 * (deriv u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by
      have hc2nn : 0 ≤ 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 := by positivity
      calc 2 * (deriv u θ * Real.cos θ) ^ 2
          = 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 := by ring
        _ = 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 * 1 := by ring
        _ ≤ 2 * (deriv u θ) ^ 2 * Real.cos θ ^ 2 * (2 * Real.cos θ ^ 2) :=
              mul_le_mul_of_nonneg_left hB hc2nn
        _ = 4 * (deriv u θ) ^ 2 * (Real.cos θ ^ 2) ^ 2 := by ring
    linarith [h1, h2, h3]
  calc ((deriv u θ * Real.cos θ + u θ * Real.sin θ) / Real.cos θ ^ 2) ^ 2 * σ θ
      ≤ (4 * (deriv u θ) ^ 2 + 8 * (u θ) ^ 2) * σ θ := mul_le_mul_of_nonneg_right hkey hσ
    _ = 4 * ((deriv u θ) ^ 2 * σ θ) + 8 * ((u θ) ^ 2 * σ θ) := by ring

private lemma integrableOn_deriv_div_cos_sq (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 * σ θ)
      (Set.Ioo 0 (Real.pi / 4)) := by
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hX' : IntegrableOn (fun z => (deriv (deriv u) z) ^ 2 * σ z) (Set.Ioo 0 (Real.pi / 4)) :=
    hX.mono_set hsub
  have hB' : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 (Real.pi / 4)) :=
    hB.mono_set hsub
  set M : ℝ := 2 * (deriv u (Real.pi / 4)) ^ 2
    + 2 * ((2 * (Real.pi / 4)) ^ (Work.Spaces.eta) * (Real.pi / 4))
      * (∫ z in Set.Ioo 0 (Real.pi / 4), (deriv (deriv u) z) ^ 2 * σ z) with hMdef
  have hdom : IntegrableOn (fun θ => 4 * (M * σ θ) + 8 * ((u θ) ^ 2 * σ θ))
      (Set.Ioo 0 (Real.pi / 4)) :=
    ((integrableOn_sig_pi4.const_mul M).const_mul 4).add (hB'.const_mul 8)
  refine Integrable.mono_nonneg hdom ?_ ?_ ?_
  · apply Measurable.aestronglyMeasurable
    change Measurable (fun θ : ℝ => deriv (fun t => u t / Real.cos t) θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _) (le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hpt := psi'_sq_le u hu hθ
    have hb : (deriv u θ) ^ 2 ≤ M := by
      rw [hMdef]
      exact deriv_sq_le_of_mem u hu pi_div_four_pos (le_refl _) hθ hX'
    have h1 : (deriv u θ) ^ 2 * σ θ ≤ M * σ θ :=
      mul_le_mul_of_nonneg_right hb (le_of_lt (sig_pos_of_mem_Ioo_pi4 hθ))
    linarith [hpt, h1]


/-! ## The requested lemma -/

theorem slice_psi_near_zero (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 4)) :=
  ⟨integrableOn_div_cos_sq u hu hB, integrableOn_deriv_div_cos_sq u hu hB hX⟩



open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Tools

Two auxiliary results, proved in sibling modules, are used below:

* `Work.FTS.EllipticEst.Honest.integrableOn_of_sin_sq_mul` — removal of the `sin²` factor on
  the right half (there `sin² θ ≥ 1/2`);
* `Work.FTS.EllipticEst.Honest.bdd_of_integrableOn_deriv` — boundedness of a differentiable
  function whose derivative is integrable.
-/

/-! ## Elementary facts about the angular weight -/

/-- `sig θ = sin(2θ)^{-η}` is measurable. -/
private lemma sig_meas : Measurable Work.FTS.EllipticEst.AngSecond.sig := by
  unfold Work.FTS.EllipticEst.AngSecond.sig
  fun_prop

/-- `sig` is integrable on `(π/4, π/2)` (the only singularity is at `π/2`, of order
`η = 99/100 < 1`). -/
private lemma sig_integrableOn :
    MeasureTheory.IntegrableOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have h := Work.FTS.EllipticEst.TanTheta.integrableOn_sin_two_rpow_neg
    (η := Work.Spaces.eta) (by norm_num [Work.Spaces.eta])
  exact h.mono_set (fun x hx => ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)

/-- `sig` is continuous on `(π/4, π/2)`. -/
private lemma sig_continuousOn :
    ContinuousOn Work.FTS.EllipticEst.AngSecond.sig
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  change ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (Real.pi / 4) (Real.pi / 2))
  refine ContinuousOn.rpow_const ?_ (fun θ hθ => Or.inl ?_)
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
      (by linarith [hθ.2, Real.pi_pos]))

/-- Membership in the closed angular interval from membership in the open right half. -/
private lemma mem_Iθ_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    θ ∈ Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact ⟨by linarith [Real.pi_pos, hθ.1], le_of_lt hθ.2⟩

/-! ## The slice lemma -/

theorem slice_psi_near_pi2 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ∧
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
  have hlt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun θ hθ => ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  -- ### first conjunct: the `sin²θ` factor can be removed on the right half
  have h1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine integrableOn_of_sin_sq_mul ?_ ?_ ?_
    · exact ((measurable_deriv _).pow_const 2).mul sig_meas
    · intro θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg (mem_Iθ_of_mem_Ioo hθ))
    · simpa only [mul_assoc] using hY
  refine ⟨h1, ?_⟩
  -- ### second conjunct: `φ = u/cos θ` is bounded
  have hderiv : ∀ x ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      HasDerivAt (fun θ => u θ / Real.cos θ) (deriv (fun θ => u θ / Real.cos θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
    have hdu : DifferentiableAt ℝ u x :=
      (hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)
    have hcos : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos],
        by linarith [hx.2, Real.pi_pos]⟩)
    exact (hdu.div Real.differentiableAt_cos hcos).hasDerivAt
  have hsq : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' h1 ?_ ?_
    · exact ((measurable_deriv _).pow_const 2).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hsig1 : 1 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
        Work.FTS.EllipticEst.AngSecond.one_le_sig ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
      have hsq0 : 0 ≤ (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hsq0]
      nlinarith [hsig1, hsq0]
  have habs : MeasureTheory.IntegrableOn
      (fun θ => |deriv (fun θ => u θ / Real.cos θ) θ|)
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (by simp)
    refine MeasureTheory.Integrable.mono' (hsq.add hone) ?_ ?_
    · exact ((measurable_deriv _).abs).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ _
      have hnn : 0 ≤ |deriv (fun θ => u θ / Real.cos θ) θ| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_abs, Pi.add_apply]
      by_cases hcase : |deriv (fun θ => u θ / Real.cos θ) θ| ≤ 1
      · nlinarith [sq_nonneg (deriv (fun θ => u θ / Real.cos θ) θ)]
      · rw [not_le] at hcase
        nlinarith [sq_abs (deriv (fun θ => u θ / Real.cos θ) θ), hcase, hnn]
  have hIntφ' : MeasureTheory.IntegrableOn (deriv (fun θ => u θ / Real.cos θ))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' habs (measurable_deriv _).aestronglyMeasurable ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
  obtain ⟨C, hC0, hC⟩ := bdd_of_integrableOn_deriv hlt hderiv hIntφ'
  have hφcont : ContinuousOn (fun θ => u θ / Real.cos θ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (hu.continuousOn.mono hsub).div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩))
  refine MeasureTheory.Integrable.mono' (sig_integrableOn.const_mul (C ^ 2)) ?_ ?_
  · exact ((hφcont.pow 2).mul sig_continuousOn).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hb := hC θ hθ
    have hs0 : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg (mem_Iθ_of_mem_Ioo hθ)
    have hsqC : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
      nlinarith [hb, abs_nonneg (u θ / Real.cos θ), sq_abs (u θ / Real.cos θ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hs0)]
    exact mul_le_mul_of_nonneg_right hsqC hs0


end Work.FTS.EllipticEst.H2W.AngBW.S3
