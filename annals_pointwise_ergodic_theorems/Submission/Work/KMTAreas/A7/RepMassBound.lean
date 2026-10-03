import Mathlib
import Submission.Work.KMTAreas.A7.repPerQCardBound
import Submission.Work.KMTAreas.A7.RepFibreKfMass
import Submission.Work.KMTAreas.A7.hiKconcN_fibre
import Submission.Work.KMTAreas.A7.M0deriv_period
import Submission.Work.KMTAreas.A7Rep.mStarF_eq_one_of_varphiN_ne
import Submission.Work.KMTAreas.A7Rep.mStargF_eq_one_of_varphitildeN_ne
import Submission.Work.KMTAreas.A7Rep.hiKmodNU_eq_fibreFlat

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The two elementary facts about the character `ee` (local copies)

`continuous_ee` and `norm_ee` live in `Submission/Work/KMTAreas/A7/hiFibreCoeffAux.lean`,
which cannot be imported in this file's import closure (it redeclares `integrable_mul_ee`,
which is also declared in `hiCrudeMult.lean`).  They are reproduced here under fresh names. -/

lemma rep_continuous_ee : Continuous ee := by
  unfold ee
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal))

lemma rep_norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

private lemma mine_norm_fourier (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) : ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply]
  exact _root_.Circle.norm_coe _

private lemma mine_norm_momPhase (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ)
    (n : ℤ) : ‖momPhase P N α₁ α₂ ξ₁ ξ₂ n‖ = 1 := by
  rw [momPhase, norm_mul, norm_mul, mine_norm_fourier, mine_norm_fourier, rep_norm_ee]
  ring

private lemma mine_norm_inv_natCast_mul_le_one (q : ℕ) : ‖((q : ℂ))⁻¹‖ * (q : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp
  · rw [norm_inv, Complex.norm_natCast, inv_mul_cancel₀ (by positivity)]

private lemma mine_norm_weylAvg_le_one (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (ξ₁ ξ₂ : ℝ) : ‖weylAvg P N α₁ α₂ ξ₁ ξ₂‖ ≤ 1 := by
  have hcard : (Finset.Ioc (N / 2) N).card ≤ N := by
    have h : (Finset.Ioc (N / 2) N).card = N - N / 2 := by simp
    rw [h]; exact Nat.sub_le _ _
  have hsum : ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖ ≤ (N : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∑ n ∈ Finset.Ioc (N / 2) N, ‖momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖
        = ((Finset.Ioc (N / 2) N).card : ℝ) := by
      simp [mine_norm_momPhase]
    rw [h1]
    exact_mod_cast hcard
  rw [weylAvg]
  refine (norm_mul_le _ _).trans ?_
  calc ‖((N : ℂ))⁻¹‖ * ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ ξ₁ ξ₂ (n : ℤ)‖
      ≤ ‖((N : ℂ))⁻¹‖ * (N : ℝ) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ ≤ 1 := mine_norm_inv_natCast_mul_le_one N

private lemma mine_norm_mTilde_le_half (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) :
    ‖mTilde P N ξ₁ ξ₂‖ ≤ 1 / 2 := by
  rw [mTilde]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
    (C := 1) (f := fun t : ℝ =>
      ee (ξ₁ * (N : ℝ) * t + ξ₂ * PevalR P ((N : ℝ) * t)))
    (fun t _ => by rw [rep_norm_ee])
  rw [one_mul, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num] at h
  exact h

private lemma mine_norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ‖mZ P q α₁ α₂‖ ≤ 1 := by
  by_cases hq : q = 0
  · subst hq
    simp [mZ]
  · exact norm_mZ_le_one P q (Nat.pos_of_ne_zero hq) α₁ α₂

private lemma mine_continuous_PevalR (P : Polynomial ℤ) : Continuous (fun t : ℝ => PevalR P t) := by
  have h2 : (fun t : ℝ => PevalR P t)
      = fun t : ℝ => ∑ i ∈ Finset.range ((P.map (Int.castRingHom ℝ)).natDegree + 1),
          (P.map (Int.castRingHom ℝ)).coeff i * t ^ i := by
    funext t; rw [PevalR, Polynomial.eval_eq_sum_range]
  rw [h2]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_id.pow i))

private lemma mine_continuous_weylAvg_pair (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    Continuous (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2) := by
  simp only [weylAvg]
  refine Continuous.mul continuous_const ?_
  refine continuous_finsetSum _ (fun n _ => ?_)
  simp only [momPhase]
  refine Continuous.mul (continuous_const.mul continuous_const) ?_
  refine rep_continuous_ee.comp ?_
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

private lemma mine_continuous_ee_pair (p : ℤ × ℤ) :
    Continuous (fun z : ℝ × ℝ => ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := by
  refine rep_continuous_ee.comp ?_
  refine Continuous.neg ?_
  exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

private lemma mine_stronglyMeasurable_mTilde_pair (P : Polynomial ℤ) (N : ℕ) :
    StronglyMeasurable (fun z : ℝ × ℝ => mTilde P N z.1 z.2) := by
  have hP : Continuous (fun t : ℝ => PevalR P t) := mine_continuous_PevalR P
  have harg : Continuous (fun w : (ℝ × ℝ) × ℝ =>
      w.1.1 * (N : ℝ) * w.2 + w.1.2 * PevalR P ((N : ℝ) * w.2)) := by
    have hA : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1.1) := continuous_fst.fst
    have hB : Continuous (fun w : (ℝ × ℝ) × ℝ => w.1.2) := continuous_fst.snd
    have hC : Continuous (fun w : (ℝ × ℝ) × ℝ => w.2) := continuous_snd
    exact ((hA.mul continuous_const).mul hC).add (hB.mul (hP.comp (continuous_const.mul hC)))
  have hsm : StronglyMeasurable (fun z : ℝ × ℝ => ∫ t : ℝ,
      ee (z.1 * (N : ℝ) * t + z.2 * PevalR P ((N : ℝ) * t))
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    StronglyMeasurable.integral_prod_right' ((rep_continuous_ee.comp harg).stronglyMeasurable)
  have hfun : (fun z : ℝ × ℝ => mTilde P N z.1 z.2)
      = fun z : ℝ × ℝ => ∫ t : ℝ, ee (z.1 * (N : ℝ) * t + z.2 * PevalR P ((N : ℝ) * t))
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    funext z
    rw [mTilde, intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  rw [hfun]
  exact hsm

private lemma mine_integrable_bumps_prod (P : Polynomial ℤ) (N k₁ k₂ : ℕ) :
    Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2)
      (volume.prod volume) :=
  Integrable.mul_prod (Work.A7.varphiN_integrable_measurable N k₁).1
    (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).1

private lemma mine_integrable_uncurry_weylAvg (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) :
    Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ =>
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      (volume.prod volume) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ =>
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
      = fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
        * weylAvg P N α₁ α₂ z.1 z.2 * ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2)) := by
    funext z; rfl
  rw [hfun]
  refine (mine_integrable_bumps_prod P N k₁ k₂).norm.mono' ?_ ?_
  · have h₁ : Measurable (fun z : ℝ × ℝ => varphiN N k₁ z.1) :=
      (Work.A7.varphiN_integrable_measurable N k₁).2.comp measurable_fst
    have h₂ : Measurable (fun z : ℝ × ℝ => varphitildeN P.natDegree N k₂ z.2) :=
      (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).2.comp measurable_snd
    have h₃ : Measurable (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2) :=
      (mine_continuous_weylAvg_pair P N α₁ α₂).measurable
    have h₄ : Measurable (fun z : ℝ × ℝ =>
        ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := (mine_continuous_ee_pair p).measurable
    exact (((h₁.mul h₂).mul h₃).mul h₄).aestronglyMeasurable
  · filter_upwards with z
    have hw := mine_norm_weylAvg_le_one P N α₁ α₂ z.1 z.2
    have h0 : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul, norm_mul, norm_mul, rep_norm_ee, mul_one]
    simpa using mul_le_mul_of_nonneg_left hw h0

private lemma mine_integrable_uncurry_mTilde (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (q : ℕ) (p : ℤ × ℤ) :
    Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ => mZ P q α₁ α₂ *
      (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))))
      (volume.prod volume) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ => mZ P q α₁ α₂ *
      (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      = fun z : ℝ × ℝ => mZ P q α₁ α₂ *
        (varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
          * mTilde P N z.1 z.2 * ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := by
    funext z; rfl
  rw [hfun]
  refine (mine_integrable_bumps_prod P N k₁ k₂).norm.mono' ?_ ?_
  · have h₁ : Measurable (fun z : ℝ × ℝ => varphiN N k₁ z.1) :=
      (Work.A7.varphiN_integrable_measurable N k₁).2.comp measurable_fst
    have h₂ : Measurable (fun z : ℝ × ℝ => varphitildeN P.natDegree N k₂ z.2) :=
      (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).2.comp measurable_snd
    have h₃ : Measurable (fun z : ℝ × ℝ => mTilde P N z.1 z.2) :=
      (mine_stronglyMeasurable_mTilde_pair P N).measurable
    have h₄ : Measurable (fun z : ℝ × ℝ =>
        ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2))) := (mine_continuous_ee_pair p).measurable
    have h₅ : Measurable (fun z : ℝ × ℝ => mZ P q α₁ α₂ *
        (varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2 * mTilde P N z.1 z.2
          * ee (-((p.1 : ℝ) * z.1 + (p.2 : ℝ) * z.2)))) :=
      (((h₁.mul h₂).mul h₃).mul h₄).const_mul (mZ P q α₁ α₂)
    exact h₅.aestronglyMeasurable
  · filter_upwards with z
    have hb : ‖mZ P q α₁ α₂‖ ≤ 1 := mine_norm_mZ_le_one P q α₁ α₂
    have h2 : ‖mTilde P N z.1 z.2‖ ≤ 1 := le_trans (mine_norm_mTilde_le_half P N z.1 z.2)
      (by norm_num)
    have ha : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, rep_norm_ee, mul_one]
    have hmid : ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * ‖mTilde P N z.1 z.2‖
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 1 :=
      mul_le_mul_of_nonneg_left h2 ha
    have hstep : ‖mZ P q α₁ α₂‖ *
        (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * ‖mTilde P N z.1 z.2‖)
        ≤ 1 * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 1) := by
      refine mul_le_mul hb hmid (mul_nonneg ha (norm_nonneg _)) (by norm_num)
    simpa using hstep

private lemma mine_iterated_integral_sub {F G : ℝ → ℝ → ℂ}
    (hF : Integrable (Function.uncurry F) (volume.prod volume))
    (hG : Integrable (Function.uncurry G) (volume.prod volume)) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, (F θ₁ θ₂ - G θ₁ θ₂))
      = (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, F θ₁ θ₂) - (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, G θ₁ θ₂) := by
  have hfun : Function.uncurry (fun θ₁ θ₂ : ℝ => F θ₁ θ₂ - G θ₁ θ₂)
      = Function.uncurry F - Function.uncurry G := by
    funext z; rfl
  have hFG : Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ => F θ₁ θ₂ - G θ₁ θ₂))
      (volume.prod volume) := by
    rw [hfun]; exact hF.sub hG
  have h2 : (∫ z : ℝ × ℝ, (F z.1 z.2 - G z.1 z.2) ∂(volume.prod volume))
      = (∫ z : ℝ × ℝ, F z.1 z.2 ∂(volume.prod volume))
        - (∫ z : ℝ × ℝ, G z.1 z.2 ∂(volume.prod volume)) := integral_sub hF hG
  rw [integral_integral hFG, h2, ← integral_integral hF, ← integral_integral hG]

private lemma mine_integral_mZ_mul_mTilde (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (q : ℕ) (p : ℤ × ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, mZ P q α₁ α₂ *
        (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))))
      = mZ P q α₁ α₂ *
        (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * mTilde P N θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))) := by
  simp_rw [integral_const_mul]

/-- The per-fibre linearity identity of the `M₀`-split. -/
private theorem mine_fibreDiff (P : Polynomial ℤ) (N k₁ k₂ q : ℕ)
    (p : Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle) (j₁ j₂ : ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N p.1 p.2 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
      - mZ P q p.1 p.2 * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁
          * varphitildeN P.natDegree N k₂ θ₂ * mTilde P N θ₁ θ₂
          * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
      = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * M0 P N q p.1 p.2 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)) := by
  have hF : Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ =>
      varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * weylAvg P N p.1 p.2 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))))
      (volume.prod volume) := mine_integrable_uncurry_weylAvg P N k₁ k₂ p.1 p.2 (j₁, j₂)
  have hG : Integrable (Function.uncurry (fun θ₁ θ₂ : ℝ => mZ P q p.1 p.2 *
      (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * mTilde P N θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))))
      (volume.prod volume) := mine_integrable_uncurry_mTilde P N k₁ k₂ p.1 p.2 q (j₁, j₂)
  have hcongr : (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * M0 P N q p.1 p.2 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
      = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
          (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * weylAvg P N p.1 p.2 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))
            - mZ P q p.1 p.2 * (varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * mTilde P N θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))) := by
    refine integral_congr_ae ?_
    filter_upwards with θ₁
    refine integral_congr_ae ?_
    filter_upwards with θ₂
    simp only [M0]
    ring
  rw [hcongr, mine_iterated_integral_sub hF hG,
    mine_integral_mZ_mul_mTilde P N k₁ k₂ p.1 p.2 q (j₁, j₂)]

/-! ## The kernel difference -/

theorem repKernDiff (ρ : ℝ) (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (N l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hband₁ : (k₁ : ℤ) + 1 + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
      ≤ Work.Analysis.EndVar.logN N)
    (hband₂ : (k₂ : ℤ) + 1 + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
      ≤ Work.Analysis.EndVar.logN N)
    (hna₁ : Work.Analysis.IonescuWainger.NonAliasing
      (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hna₂ : Work.Analysis.IonescuWainger.NonAliasing
      (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (Work.KMTAreas.A7.diffFreqs ρ l₂)) :
    Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ j₁ j₂
      - Work.KMTAreas.A7.hiKmodNRep ρ P N l₁ l₂ k₁ k₂ j₁ j₂
      = Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ j₁ j₂ := by
  classical
  -- the band conditions in the weaker form used by the model-side reduction
  have hb₁ : (k₁ : ℤ) + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
      ≤ Work.Analysis.EndVar.logN N := by omega
  have hb₂ : (k₂ : ℤ) + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
      ≤ Work.Analysis.EndVar.logN N := by omega
  -- the two cutoffs equal `1` on the supports of the bumps
  have hcut₁ : ∀ θ : ℝ, Work.KMTAreas.A7.varphiN N k₁ θ ≠ 0 →
      Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) θ = 1 :=
    Work.KMTAreas.A7Rep.mStarF_eq_one_of_varphiN_ne N k₁ (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) hband₁
  have hcut₂ : ∀ θ : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ ≠ 0 →
      Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) θ = 1 :=
    Work.KMTAreas.A7Rep.mStargF_eq_one_of_varphitildeN_ne P hdeg N k₂ (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) hband₂
  -- the model kernel in flat fibre form
  have hmod := Work.KMTAreas.A7Rep.hiKmodNU_eq_fibreFlat ρ P (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) N l₁ l₂ k₁ k₂ j₁ j₂
    hdeg hl₁ hl₂ hb₁ hb₂ hna₁ hna₂ hcut₁ hcut₂
  -- the concrete kernel in fibre form, the model kernel in flat fibre form, and `hiM0Ker`
  rw [Work.KMTAreas.A7.hiKconcN_fibre ρ P N l₁ l₂ k₁ k₂ j₁ j₂, Work.KMTAreas.A7.hiKmodNRep,
    hmod, Work.KMTAreas.A7.hiM0Ker]
  -- combine the two sums and apply the per-fibre identity
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have h := mine_fibreDiff P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p j₁ j₂
  rw [← h, mul_sub]
  ring

/-! ## Integrability of the `M₀`-fibre symbol -/

private lemma rep_integrable_bumps_prod (P : Polynomial ℤ) (N k₁ k₂ : ℕ) :
    Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2)
      (volume.prod volume) :=
  Integrable.mul_prod (Work.A7.varphiN_integrable_measurable N k₁).1
    (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).1

private lemma rep_measurable_M0 (P : Polynomial ℤ) (N q : ℕ)
    (α β : Work.Analysis.IonescuWainger.Circle) :
    Measurable (fun z : ℝ × ℝ => M0 P N q α β z.1 z.2) := by
  have h1 : Measurable (fun z : ℝ × ℝ => weylAvg P N α β z.1 z.2) :=
    (mine_continuous_weylAvg_pair P N α β).measurable
  have h2 : Measurable (fun z : ℝ × ℝ => mTilde P N z.1 z.2) :=
    (mine_stronglyMeasurable_mTilde_pair P N).measurable
  have h3 : (fun z : ℝ × ℝ => M0 P N q α β z.1 z.2)
      = fun z : ℝ × ℝ => weylAvg P N α β z.1 z.2 - mZ P q α β * mTilde P N z.1 z.2 := rfl
  rw [h3]
  exact h1.sub (measurable_const.mul h2)

private lemma rep_norm_M0_le_two (P : Polynomial ℤ) (N q : ℕ)
    (α β : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ) :
    ‖M0 P N q α β ξ₁ ξ₂‖ ≤ 2 := by
  rw [M0]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖weylAvg P N α β ξ₁ ξ₂‖ ≤ 1 := mine_norm_weylAvg_le_one P N α β ξ₁ ξ₂
  have h2 : ‖mZ P q α β * mTilde P N ξ₁ ξ₂‖ ≤ 1 * (1 / 2) :=
    (norm_mul_le _ _).trans
      (mul_le_mul (mine_norm_mZ_le_one P q α β) (mine_norm_mTilde_le_half P N ξ₁ ξ₂)
        (norm_nonneg _) (by norm_num))
  linarith

private lemma rep_integrable_uncurry_M0 (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α β : Work.Analysis.IonescuWainger.Circle) :
    Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
      * M0 P N q α β z.1 z.2) (volume.prod volume) := by
  refine ((rep_integrable_bumps_prod P N k₁ k₂).norm.const_mul 2).mono' ?_ ?_
  · have h1 : Measurable (fun z : ℝ × ℝ => varphiN N k₁ z.1) :=
      (Work.A7.varphiN_integrable_measurable N k₁).2.comp measurable_fst
    have h2 : Measurable (fun z : ℝ × ℝ => varphitildeN P.natDegree N k₂ z.2) :=
      (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).2.comp measurable_snd
    exact ((h1.mul h2).mul (rep_measurable_M0 P N q α β)).aestronglyMeasurable
  · filter_upwards with z
    simp only [norm_mul]
    have hb := rep_norm_M0_le_two P N q α β z.1 z.2
    have h₁ : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ := norm_nonneg _
    have h₂ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ z.2‖ := norm_nonneg _
    have h₃ : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg h₁ h₂
    calc ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
          * ‖M0 P N q α β z.1 z.2‖
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 2 :=
          mul_le_mul_of_nonneg_left hb h₃
      _ = 2 * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖) := by ring

private lemma rep_integrable_uncurry_M0_ee (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α β : Work.Analysis.IonescuWainger.Circle) (p₁ p₂ : ℤ) :
    Integrable (fun z : ℝ × ℝ => varphiN N k₁ z.1 * varphitildeN P.natDegree N k₂ z.2
      * M0 P N q α β z.1 z.2 * ee (-((p₁ : ℝ) * z.1 + (p₂ : ℝ) * z.2)))
      (volume.prod volume) := by
  refine ((rep_integrable_bumps_prod P N k₁ k₂).norm.const_mul 2).mono' ?_ ?_
  · have h1 : Measurable (fun z : ℝ × ℝ => varphiN N k₁ z.1) :=
      (Work.A7.varphiN_integrable_measurable N k₁).2.comp measurable_fst
    have h2 : Measurable (fun z : ℝ × ℝ => varphitildeN P.natDegree N k₂ z.2) :=
      (Work.A7.varphitildeN_integrable_measurable P.natDegree N k₂).2.comp measurable_snd
    have h4 : Measurable (fun z : ℝ × ℝ => ee (-((p₁ : ℝ) * z.1 + (p₂ : ℝ) * z.2))) :=
      (mine_continuous_ee_pair (p₁, p₂)).measurable
    exact (((h1.mul h2).mul (rep_measurable_M0 P N q α β)).mul h4).aestronglyMeasurable
  · filter_upwards with z
    simp only [norm_mul, rep_norm_ee, mul_one]
    have hb := rep_norm_M0_le_two P N q α β z.1 z.2
    have h₁ : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ := norm_nonneg _
    have h₂ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ z.2‖ := norm_nonneg _
    have h₃ : (0 : ℝ) ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ :=
      mul_nonneg h₁ h₂
    calc ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖
          * ‖M0 P N q α β z.1 z.2‖
        ≤ ‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖ * 2 :=
          mul_le_mul_of_nonneg_left hb h₃
      _ = 2 * (‖varphiN N k₁ z.1‖ * ‖varphitildeN P.natDegree N k₂ z.2‖) := by ring

/-! ## The per-fibre `ℓ¹(ℤ²)` mass bound -/

private lemma rep_kf_bridge (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α β : Work.Analysis.IonescuWainger.Circle) (p₁ p₂ : ℤ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * M0 P N q α β θ₁ θ₂ * ee (-((p₁ : ℝ) * θ₁ + (p₂ : ℝ) * θ₂)))
      = kf (fun θ₁ θ₂ => varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * M0 P N q α β θ₁ θ₂) p₁ p₂ := by
  rw [kf_eq_kfX _ p₁ p₂ (rep_integrable_uncurry_M0 P N q k₁ k₂ α β)]
  rw [kfX]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ₁ => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ₂ => ?_))
  change varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
      * M0 P N q α β θ₁ θ₂ * ee (-((p₁ : ℝ) * θ₁ + (p₂ : ℝ) * θ₂))
    = varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
      * M0 P N q α β θ₁ θ₂ * ee (-((p₁ : ℝ) * θ₁)) * ee (-((p₂ : ℝ) * θ₂))
  rw [ee_neg_add]
  ring

theorem repFibreMass (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N q k₁ k₂ : ℕ) (α β : Work.Analysis.IonescuWainger.Circle),
        1 ≤ N → 1 ≤ q → q • α = 0 → q • β = 0 →
        k₁ ≤ (Work.Analysis.EndVar.logN N).toNat →
        k₂ ≤ (Work.Analysis.EndVar.logN N).toNat →
        (Summable fun p : ℤ × ℤ => ‖∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
            varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N q α β θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))‖) ∧
        (∑' p : ℤ × ℤ, ‖∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
            varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N q α β θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))‖)
          ≤ C * (q : ℝ) * ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) + 1) ^ A
              * (2 : ℝ) ^ (2 * k₁ + 2 * P.natDegree * k₂) / (N : ℝ) := by
  obtain ⟨K, A, hK, hA, hbd⟩ := repKf_hbd P hdeg
  refine ⟨100 * K, A, by positivity, hA, ?_⟩
  intro N q k₁ k₂ α β hN hq hα hβ _hk₁ _hk₂
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr₁pos : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  have hr₁le : (N : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hNpos]; exact hN1
  have hr₂pos : (0 : ℝ) < ((N : ℝ) ^ P.natDegree)⁻¹ := by positivity
  have hr₂le : ((N : ℝ) ^ P.natDegree)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]; exact one_le_pow₀ hN1
  set Br : ℝ := (2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) + 1 with hBr
  set W : ℝ := (2 : ℝ) ^ (2 * k₁ + 2 * P.natDegree * k₂) with hW
  set CC : ℝ := K * (q : ℝ) * Br ^ A * W / (N : ℝ) with hCC
  have hBrpos : (0 : ℝ) < Br := by rw [hBr]; positivity
  have hWpos : (0 : ℝ) < W := by rw [hW]; positivity
  have hCCnn : (0 : ℝ) ≤ CC := by
    rw [hCC]
    have h2 : (0 : ℝ) < (N : ℝ) := hNpos
    positivity
  have hpt : ∀ p₁ p₂ : ℤ, ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * M0 P N q α β θ₁ θ₂) p₁ p₂‖
      ≤ CC * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p₁
          * Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p₂) := by
    intro p₁ p₂
    refine kf_le (fun θ₁ θ₂ => varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
        * M0 P N q α β θ₁ θ₂) CC ((N : ℝ)⁻¹) (((N : ℝ) ^ P.natDegree)⁻¹) ?_ ?_ p₁ p₂
    · intro i j hi hj q₁ q₂
      exact repKf_ibp P N q k₁ k₂ α β i j hi hj q₁ q₂
    · intro i j hi hj
      have h := hbd N q k₁ k₂ α β hN hq hα hβ i j hi hj
      rw [repKf_inv_rpow N hN i, repKf_inv_rpow_pow N P.natDegree hN j, hCC, hBr, hW]
      exact h.trans (le_of_eq (by ring))
  have hWnn : ∀ p : ℤ, 0 ≤ Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p :=
    fun p => Work.KMTPlan.A6.wt_nonneg (by positivity) p
  have hWnn' : ∀ p : ℤ, 0 ≤ Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p :=
    fun p => Work.KMTPlan.A6.wt_nonneg (by positivity) p
  have hsumm_wt : Summable (fun p : ℤ × ℤ => Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
      * Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p.2) :=
    Summable.mul_of_nonneg ((Work.KMTPlan.A6.wt_tsum_le ((N : ℝ)⁻¹) hr₁pos hr₁le).1)
      ((Work.KMTPlan.A6.wt_tsum_le (((N : ℝ) ^ P.natDegree)⁻¹) hr₂pos hr₂le).1)
      (fun p => hWnn p) (fun p => hWnn' p)
  have hmaj : Summable (fun p : ℤ × ℤ => CC * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
      * Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p.2)) := hsumm_wt.mul_left CC
  have hsumm_kf : Summable (fun p : ℤ × ℤ => ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
      * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2‖) :=
    Summable.of_nonneg_of_le
      (f := fun p : ℤ × ℤ => CC * (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
        * Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p.2))
      (g := fun p : ℤ × ℤ => ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
        * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2‖)
      (fun p => norm_nonneg _) (fun p => hpt p.1 p.2) hmaj
  have hpt_left : ∀ p : ℤ × ℤ, ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
      * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2‖
      ≤ CC * Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1
        * Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p.2 :=
    fun p => (hpt p.1 p.2).trans
      (le_of_eq (mul_assoc CC (Work.KMTPlan.A6.wt ((N : ℝ)⁻¹) p.1)
        (Work.KMTPlan.A6.wt (((N : ℝ) ^ P.natDegree)⁻¹) p.2)).symm)
  have hbound : (∑' p : ℤ × ℤ, ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
      * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2‖) ≤ 100 * CC :=
    hiCrudeTsum (fun p : ℤ × ℤ => kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
        * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2) CC ((N : ℝ)⁻¹)
      (((N : ℝ) ^ P.natDegree)⁻¹) hCCnn hr₁pos hr₁le hr₂pos hr₂le
      (fun p => hpt_left p)
  constructor
  · refine Summable.congr hsumm_kf (fun p => ?_)
    rw [rep_kf_bridge]
  · have hts : (∑' p : ℤ × ℤ, ‖∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
        varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
          * M0 P N q α β θ₁ θ₂
          * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))‖)
        = ∑' p : ℤ × ℤ, ‖kf (fun θ₁ θ₂ => varphiN N k₁ θ₁
            * varphitildeN P.natDegree N k₂ θ₂ * M0 P N q α β θ₁ θ₂) p.1 p.2‖ :=
      tsum_congr (fun p => by rw [rep_kf_bridge])
    rw [hts]
    exact hbound.trans (le_of_eq (by rw [hCC, hBr, hW]; ring))

/-! ## The exact-height fibre sum -/

private theorem rep_diffFreqs_subset (ρ : ℝ) (l : ℕ) :
    diffFreqs ρ l ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  intro γ hγ
  unfold diffFreqs at hγ
  split_ifs at hγ with h
  · rwa [h]
  · exact (Finset.mem_sdiff.mp hγ).1

private theorem rep_arithQ_nsmul_eq_zero {ρ : ℝ} {L : ℕ}
    {α : Work.Analysis.IonescuWainger.Circle}
    (h : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ L) : (arithQ ρ L) • α = 0 := by
  have h1 : arithQ ρ L = Work.Analysis.IonescuWainger.iwQl ρ L := by
    show Nat.max 1 (Work.Analysis.IonescuWainger.iwQl ρ L)
      = Work.Analysis.IonescuWainger.iwQl ρ L
    exact Nat.max_eq_right (Nat.one_le_iff_ne_zero.mpr
      (Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := L)).ne')
  rw [h1]
  exact Work.Analysis.IonescuWainger.iwQl_nsmul_eq_zero h

private theorem rep_lmaxR_eq (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by
  have h : ((max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) : ℤ) : ℝ)
      = ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by
    rw [show (max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) : ℤ)
        = ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℤ) by omega]
    exact_mod_cast rfl
  simpa only [lmaxR, Work.Analysis.EndVar.lmax] using h

private theorem rep_logN_nonneg (N : ℕ) : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
  rw [Work.Analysis.EndVar.logN]
  positivity

private theorem rep_le_logN_toNat {N k : ℕ} (h : (k : ℤ) ≤ Work.Analysis.EndVar.logN N) :
    k ≤ (Work.Analysis.EndVar.logN N).toNat := by
  have h0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := rep_logN_nonneg N
  have h2 : (k : ℤ) ≤ (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]; exact h
  exact_mod_cast h2

private theorem rep_uRep_ge (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    max l₁ l₂ + 3 ≤ uRep ρ l₁ l₂ k₁ k₂ := le_max_right _ _

/-- The `ℕ`-level `L` of the repaired window `uRep`. -/
private def repL (l₁ l₂ k₁ k₂ : ℕ) : ℕ := max (max l₁ l₂) (max k₁ k₂)

private theorem rep_lmaxR_eq_repL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((repL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := rep_lmaxR_eq l₁ l₂ k₁ k₂

private theorem rep_l₁_le_repL (l₁ l₂ k₁ k₂ : ℕ) : l₁ ≤ repL l₁ l₂ k₁ k₂ :=
  le_trans (le_max_left _ _) (le_max_left _ _)

private theorem rep_l₂_le_repL (l₁ l₂ k₁ k₂ : ℕ) : l₂ ≤ repL l₁ l₂ k₁ k₂ :=
  le_trans (le_max_right _ _) (le_max_left _ _)

private theorem rep_k₁_le_repL (l₁ l₂ k₁ k₂ : ℕ) : k₁ ≤ repL l₁ l₂ k₁ k₂ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

private theorem rep_k₂_le_repL (l₁ l₂ k₁ k₂ : ℕ) : k₂ ≤ repL l₁ l₂ k₁ k₂ :=
  le_trans (le_max_right _ _) (le_max_right _ _)
/-- The fibre coefficient of `hiM0Ker` at the fibre period `perQ β.1 β.2`. -/
noncomputable def repG (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (β : Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle)
    (p : ℤ × ℤ) : ℂ :=
  ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
    * M0 P N (Work.KMTPlan.A6.perQ β.1 β.2) β.1 β.2 θ₁ θ₂
    * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))

private lemma rep_two_rpow_add (x y : ℝ) :
    (2 : ℝ) ^ (x + y) = (2 : ℝ) ^ x * (2 : ℝ) ^ y :=
  Real.rpow_add (by norm_num) x y

private lemma rep_two_rpow_mono {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private lemma rep_two_rpow_nonneg (x : ℝ) : 0 ≤ (2 : ℝ) ^ x := Real.rpow_nonneg (by norm_num) x

private lemma rep_two_rpow_pos (x : ℝ) : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x

private lemma rep_two_nat_pow_le {k L : ℕ} (h : k ≤ L) : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (L : ℝ) := by
  rw [← Real.rpow_natCast (2 : ℝ) k]
  exact rep_two_rpow_mono (by exact_mod_cast h)

/-! ## The target: the `ℓ¹` mass bound of the §6 model-approximation error -/

theorem RepMassBound (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∃ D : ℝ, 0 < D ∧ ∀ (N l₁ l₂ k₁ k₂ : ℕ),
        1 ≤ N → 1 ≤ l₁ → 1 ≤ l₂ →
        (k₁ : ℤ) + 1 + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
          ≤ Work.Analysis.EndVar.logN N →
        (k₂ : ℤ) + 1 + 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)
          ≤ Work.Analysis.EndVar.logN N →
        (2 : ℝ) ^ k₁ ≤ (N : ℝ) →
        (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree →
        Work.Analysis.IonescuWainger.NonAliasing
          (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (Work.KMTAreas.A7.diffFreqs ρ l₁) →
        Work.Analysis.IonescuWainger.NonAliasing
          (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)) (Work.KMTAreas.A7.diffFreqs ρ l₂) →
        (Summable fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
            - Work.KMTAreas.A7.hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖) ∧
        (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
            - Work.KMTAreas.A7.hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖)
          ≤ D * (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
              + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) * ((N : ℝ))⁻¹ := by
  classical
  obtain ⟨Cf, Af, hCf, hAf, hfib⟩ := repFibreMass P hdeg
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hdeg)
  refine ⟨max 1 (max 6 (Af * (P.natDegree : ℝ) + 2 + 2 * (P.natDegree : ℝ))), ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  · intro ρ hρ hρ1
    obtain ⟨Cq, hCq, hperQ, hcard⟩ := repPerQCardBound ρ hρ hρ1 1 (by norm_num)
    refine ⟨max 1 (Cf * Cq ^ 3 * 3 ^ Af), ?_, ?_⟩
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · intro N l₁ l₂ k₁ k₂ hN hl₁ hl₂ hb₁ hb₂ h2k₁ h2k₂ hna₁ hna₂
      -- ### the kernel identity
      have hker : ∀ p : ℤ × ℤ, Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
          - Work.KMTAreas.A7.hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2
          = Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2 :=
        fun p => repKernDiff ρ P hdeg N l₁ l₂ k₁ k₂ p.1 p.2 hl₁ hl₂ hb₁ hb₂ hna₁ hna₂
      -- ### abbreviations
      set L : ℕ := repL l₁ l₂ k₁ k₂ with hL
      set Br : ℝ := (2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) + 1 with hBr
      set W : ℝ := (2 : ℝ) ^ (2 * k₁ + 2 * P.natDegree * k₂) with hW
      set Sl : ℝ := (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + (2 : ℝ) ^ (ρ * (l₂ : ℝ)) with hSl_def
      set X : ℝ := (2 : ℝ) ^ Sl with hX
      set Aexp : ℝ := max 1 (max 6 (Af * (P.natDegree : ℝ) + 2 + 2 * (P.natDegree : ℝ)))
        with hAexp
      set Dexp : ℝ := max 1 (Cf * Cq ^ 3 * 3 ^ Af) with hDexp
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      have hXpos : (0 : ℝ) < X := by rw [hX]; exact rep_two_rpow_pos _
      -- ### the log bounds
      have hk₁log : k₁ ≤ (Work.Analysis.EndVar.logN N).toNat := by
        refine rep_le_logN_toNat ?_
        have h2 : (0 : ℤ) ≤ 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) := by positivity
        omega
      have hk₂log : k₂ ≤ (Work.Analysis.EndVar.logN N).toNat := by
        refine rep_le_logN_toNat ?_
        have h2 : (0 : ℤ) ≤ 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ) := by positivity
        omega
      -- ### the fibre set
      set SS : Finset (Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle) :=
        (diffFreqs ρ l₁).product (diffFreqs ρ l₂) with hSS
      have hfreq : ∀ β ∈ SS,
          β.1 ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
            ∧ β.2 ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ := by
        intro β hβ
        rw [hSS] at hβ
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hβ
        exact ⟨rep_diffFreqs_subset ρ l₁ h1, rep_diffFreqs_subset ρ l₂ h2⟩
      have hperQb : ∀ β ∈ SS, ((Work.KMTPlan.A6.perQ β.1 β.2 : ℕ) : ℝ) ≤ Cq * X := by
        intro β hβ
        obtain ⟨h1, h2⟩ := hfreq β hβ
        have h := hperQ l₁ l₂ β.1 h1 β.2 h2
        rw [one_mul] at h
        rw [hX, hSl_def]
        exact h
      -- ### the per-fibre mass bound
      have hfibβ : ∀ β ∈ SS, Summable (fun p : ℤ × ℤ => ‖repG P N k₁ k₂ β p‖)
          ∧ (∑' p : ℤ × ℤ, ‖repG P N k₁ k₂ β p‖) ≤ Cf * ((Work.KMTPlan.A6.perQ β.1 β.2 : ℕ) : ℝ)
              * Br ^ Af * W / (N : ℝ) := by
        intro β hβ
        obtain ⟨h1, h2⟩ := hfreq β hβ
        have hqa : 0 < arithQ ρ (max l₁ l₂) := arithQ_pos ρ _
        have hsm₁ : (arithQ ρ (max l₁ l₂)) • β.1 = 0 := rep_arithQ_nsmul_eq_zero
          ((Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left _ _)) h1)
        have hsm₂ : (arithQ ρ (max l₁ l₂)) • β.2 = 0 := rep_arithQ_nsmul_eq_zero
          ((Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_right _ _)) h2)
        have ho₁ : IsOfFinAddOrder β.1 :=
          isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hqa, hsm₁⟩
        have ho₂ : IsOfFinAddOrder β.2 :=
          isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hqa, hsm₂⟩
        have hq : 0 < Work.KMTPlan.A6.perQ β.1 β.2 :=
          Work.KMTPlan.A6.SpikeToolbox.perQ_pos ho₁ ho₂
        simpa only [repG, hBr, hW] using hfib N (Work.KMTPlan.A6.perQ β.1 β.2) k₁ k₂ β.1 β.2
          hN hq (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_left β.1 β.2)
          (Work.KMTPlan.A6.SpikeToolbox.perQ_smul_right β.1 β.2) hk₁log hk₂log
      -- ### the fibre decomposition of `hiM0Ker`
      have hdecomp : ∀ p : ℤ × ℤ, Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2
          = ∑ β ∈ SS, fourier (T := 1) (-p.1) β.1 * fourier (T := 1) (-p.2) β.2
              * repG P N k₁ k₂ β p := by
        intro p
        have h1 : Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2
            = ∑ β ∈ SS, fourier (T := 1) (-p.1) β.1 * fourier (T := 1) (-p.2) β.2
              * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
                  * M0 P N (arithQ ρ (max l₁ l₂)) β.1 β.2 θ₁ θ₂
                  * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))) := by
          rw [Work.KMTAreas.A7.hiM0Ker, ← hSS]
        rw [h1]
        refine Finset.sum_congr rfl (fun β hβ => ?_)
        obtain ⟨h1', h2'⟩ := hfreq β hβ
        have hqa : 0 < arithQ ρ (max l₁ l₂) := arithQ_pos ρ _
        have hsm₁ : (arithQ ρ (max l₁ l₂)) • β.1 = 0 := rep_arithQ_nsmul_eq_zero
          ((Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left _ _)) h1')
        have hsm₂ : (arithQ ρ (max l₁ l₂)) • β.2 = 0 := rep_arithQ_nsmul_eq_zero
          ((Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_right _ _)) h2')
        have ho₁ : IsOfFinAddOrder β.1 :=
          isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hqa, hsm₁⟩
        have ho₂ : IsOfFinAddOrder β.2 :=
          isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hqa, hsm₂⟩
        have hM0eq := M0_eq_perQ P N hqa hsm₁ hsm₂ ho₁ ho₂
        have hint : (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N (arithQ ρ (max l₁ l₂)) β.1 β.2 θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)))
            = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N (Work.KMTPlan.A6.perQ β.1 β.2) β.1 β.2 θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun θ₁ => ?_))
          refine integral_congr_ae (Filter.Eventually.of_forall (fun θ₂ => ?_))
          change varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N (arithQ ρ (max l₁ l₂)) β.1 β.2 θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))
            = varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
              * M0 P N (Work.KMTPlan.A6.perQ β.1 β.2) β.1 β.2 θ₁ θ₂
              * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))
          rw [hM0eq]
        rw [hint]
        simp only [repG]
      -- ### summability of the fibre sum
      have hsumm_fib : ∀ β ∈ SS, Summable (fun p : ℤ × ℤ => ‖repG P N k₁ k₂ β p‖) :=
        fun β hβ => (hfibβ β hβ).1
      have hsumm_sum : Summable (fun p : ℤ × ℤ => ∑ β ∈ SS, ‖repG P N k₁ k₂ β p‖) :=
        summable_sum (s := SS) hsumm_fib
      have htri : ∀ p : ℤ × ℤ, ‖Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖
          ≤ ∑ β ∈ SS, ‖repG P N k₁ k₂ β p‖ := by
        intro p
        rw [hdecomp p]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun β hβ => ?_))
        calc ‖fourier (T := 1) (-p.1) β.1 * fourier (T := 1) (-p.2) β.2
              * repG P N k₁ k₂ β p‖
            = ‖repG P N k₁ k₂ β p‖ := by
              simp only [norm_mul, mine_norm_fourier, one_mul]
          _ ≤ ‖repG P N k₁ k₂ β p‖ := le_rfl
      have hsumm_M0 : Summable (fun p : ℤ × ℤ =>
          ‖Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖) :=
        Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => ∑ β ∈ SS, ‖repG P N k₁ k₂ β p‖)
          (g := fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖)
          (fun p => norm_nonneg _) (fun p => htri p) hsumm_sum
      -- ### the uniform fibre bound
      have hunif : ∀ β ∈ SS, (∑' p : ℤ × ℤ, ‖repG P N k₁ k₂ β p‖)
          ≤ Cf * (Cq * X) * Br ^ Af * W / (N : ℝ) := by
        intro β hβ
        have hstep := hperQb β hβ
        have hstepb := (hfibβ β hβ).2
        have hBrnn : (0 : ℝ) ≤ Br ^ Af := Real.rpow_nonneg (by rw [hBr]; positivity) Af
        have hWnn : (0 : ℝ) ≤ W := by rw [hW]; positivity
        have hNinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
        refine hstepb.trans ?_
        rw [div_eq_mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hCf.le) hBrnn) hWnn) hNinv
      have hsumfib : (∑' p : ℤ × ℤ, ∑ β ∈ SS, ‖repG P N k₁ k₂ β p‖)
          ≤ (SS.card : ℝ) * (Cf * (Cq * X) * Br ^ Af * W / (N : ℝ)) := by
        rw [Summable.tsum_finsetSum hsumm_fib]
        refine (Finset.sum_le_sum (fun β hβ => hunif β hβ)).trans (le_of_eq ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
      -- ### the cardinality bound
      have hcardb : (SS.card : ℝ) ≤ Cq ^ 2 * X ^ 2 := by
        have h1 : ((diffFreqs ρ l₁).card : ℝ)
            ≤ Cq * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
          (Nat.cast_le.mpr (Finset.card_le_card (rep_diffFreqs_subset ρ l₁))).trans (hcard l₁)
        have h2 : ((diffFreqs ρ l₂).card : ℝ)
            ≤ Cq * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) :=
          (Nat.cast_le.mpr (Finset.card_le_card (rep_diffFreqs_subset ρ l₂))).trans (hcard l₂)
        have hcardSS : (SS.card : ℝ)
            = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
          have hp : SS.card = (diffFreqs ρ l₁).card * (diffFreqs ρ l₂).card := by
            rw [hSS]; simp
          rw [hp]
          push_cast
          ring
        have hexp2 : (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
              + 2 * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) = X ^ 2 := by
          rw [hX, hSl_def,
            ← Real.rpow_natCast ((2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))
              + (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) 2,
            ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
        rw [hcardSS]
        refine (mul_le_mul h1 h2 (by positivity) (by positivity)).trans (le_of_eq ?_)
        rw [show Cq * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
              * (Cq * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₂ : ℝ))))
            = Cq ^ 2 * ((2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
              * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) by ring,
          ← rep_two_rpow_add, hexp2]
      -- ### the final absorption
      have hX3 : X ^ 3 = (2 : ℝ) ^ (3 * Sl) := by
        rw [hX, hSl_def, ← Real.rpow_natCast ((2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))
            + (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) 3, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      have hBrpow : Br ^ Af ≤ 3 ^ Af * (2 : ℝ) ^ (Af * ((P.natDegree : ℝ) * (L : ℝ))) := by
        have hBrpos : (0 : ℝ) < Br := by rw [hBr]; positivity
        have hle : Br ≤ 3 * (2 : ℝ) ^ ((P.natDegree : ℝ) * (L : ℝ)) := by
          have h1 : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * (L : ℝ)) := by
            refine (rep_two_nat_pow_le (rep_k₁_le_repL l₁ l₂ k₁ k₂)).trans ?_
            refine rep_two_rpow_mono ?_
            rw [hL]
            push_cast
            nlinarith [hd1, (by positivity : (0:ℝ) ≤ (repL l₁ l₂ k₁ k₂ : ℕ))]
          have h2 : (2 : ℝ) ^ (P.natDegree * k₂)
              ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * (L : ℝ)) := by
            rw [hL, ← Real.rpow_natCast (2 : ℝ) (P.natDegree * k₂)]
            refine rep_two_rpow_mono ?_
            have hk : (k₂ : ℝ) ≤ (repL l₁ l₂ k₁ k₂ : ℕ) := by
              exact_mod_cast rep_k₂_le_repL l₁ l₂ k₁ k₂
            push_cast
            nlinarith [hd1, hk]
          have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * (L : ℝ)) :=
            Real.one_le_rpow (by norm_num) (by positivity)
          rw [hBr]
          linarith
        refine (Real.rpow_le_rpow hBrpos.le hle hAf).trans (le_of_eq ?_)
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num)]
        congr 1
        ring_nf
      have hW_le : W ≤ (2 : ℝ) ^ ((2 + 2 * (P.natDegree : ℝ)) * (L : ℝ)) := by
        rw [hW, hL, ← Real.rpow_natCast (2 : ℝ) (2 * k₁ + 2 * P.natDegree * k₂)]
        refine rep_two_rpow_mono ?_
        have hk₁ := rep_k₁_le_repL l₁ l₂ k₁ k₂
        have hk₂ := rep_k₂_le_repL l₁ l₂ k₁ k₂
        have hLnn : (0 : ℝ) ≤ (repL l₁ l₂ k₁ k₂ : ℕ) := by positivity
        have hcast : ((2 * k₁ + 2 * P.natDegree * k₂ : ℕ) : ℝ)
            = 2 * (k₁ : ℝ) + 2 * (P.natDegree : ℝ) * (k₂ : ℝ) := by push_cast; ring
        rw [hcast]
        have h1 : (k₁ : ℝ) ≤ (repL l₁ l₂ k₁ k₂ : ℕ) := by exact_mod_cast hk₁
        have h2 : (k₂ : ℝ) ≤ (repL l₁ l₂ k₁ k₂ : ℕ) := by exact_mod_cast hk₂
        nlinarith [h1, h2, hLnn, hd1]
      have hSl_le : Sl ≤ 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
        rw [hSl_def]
        have hl₁ : (l₁ : ℝ) ≤ (L : ℝ) := by rw [hL]; exact_mod_cast rep_l₁_le_repL l₁ l₂ k₁ k₂
        have hl₂ : (l₂ : ℝ) ≤ (L : ℝ) := by rw [hL]; exact_mod_cast rep_l₂_le_repL l₁ l₂ k₁ k₂
        have i1 : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
          rep_two_rpow_mono (by nlinarith [hρ.le, hl₁])
        have i2 : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
          rep_two_rpow_mono (by nlinarith [hρ.le, hl₂])
        linarith
      have hexp : X ^ 3 * Br ^ Af * W
          ≤ 3 ^ Af * (2 : ℝ) ^ (Aexp * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))) := by
        have ha : (2 : ℝ) ^ (3 * Sl) ≤ (2 : ℝ) ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ))) :=
          rep_two_rpow_mono (by linarith [hSl_le])
        have hstep : (2 : ℝ) ^ (3 * Sl) * Br ^ Af * W
            ≤ (2 : ℝ) ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ)))
              * (3 ^ Af * (2 : ℝ) ^ (Af * ((P.natDegree : ℝ) * (L : ℝ))))
              * (2 : ℝ) ^ ((2 + 2 * (P.natDegree : ℝ)) * (L : ℝ)) := by
          refine mul_le_mul (mul_le_mul ha hBrpow (by positivity) (by positivity)) hW_le
            (by positivity) (by positivity)
        rw [hX3]
        refine hstep.trans ?_
        rw [show (2 : ℝ) ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ)))
              * (3 ^ Af * (2 : ℝ) ^ (Af * ((P.natDegree : ℝ) * (L : ℝ))))
              * (2 : ℝ) ^ ((2 + 2 * (P.natDegree : ℝ)) * (L : ℝ))
            = 3 ^ Af * ((2 : ℝ) ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ)))
              * ((2 : ℝ) ^ (Af * ((P.natDegree : ℝ) * (L : ℝ)))
                * (2 : ℝ) ^ ((2 + 2 * (P.natDegree : ℝ)) * (L : ℝ)))) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [show (2 : ℝ) ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ)))
              * ((2 : ℝ) ^ (Af * ((P.natDegree : ℝ) * (L : ℝ)))
                * (2 : ℝ) ^ ((2 + 2 * (P.natDegree : ℝ)) * (L : ℝ)))
            = 2 ^ (6 * (2 : ℝ) ^ (ρ * (L : ℝ))
                + (Af * ((P.natDegree : ℝ) * (L : ℝ))
                  + (2 + 2 * (P.natDegree : ℝ)) * (L : ℝ))) by
          rw [← rep_two_rpow_add, ← rep_two_rpow_add]]
        rw [show (6 * (2 : ℝ) ^ (ρ * (L : ℝ))
              + (Af * ((P.natDegree : ℝ) * (L : ℝ))
                + (2 + 2 * (P.natDegree : ℝ)) * (L : ℝ)))
            = 6 * (2 : ℝ) ^ (ρ * (L : ℝ))
              + (Af * (P.natDegree : ℝ) + 2 + 2 * (P.natDegree : ℝ)) * (L : ℝ) by ring]
        refine rep_two_rpow_mono ?_
        have hA1 : 6 ≤ Aexp := by
          rw [hAexp]
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        have hA2 : Af * (P.natDegree : ℝ) + 2 + 2 * (P.natDegree : ℝ) ≤ Aexp := by
          rw [hAexp]
          exact le_trans (le_max_right _ _) (le_max_right _ _)
        have hρL : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := rep_two_rpow_nonneg _
        have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
        have e1 := mul_le_mul_of_nonneg_right hA1 hρL
        have e2 := mul_le_mul_of_nonneg_right hA2 hLnn
        linarith
      -- ### assembling
      have hDexple : Cf * Cq ^ 3 * 3 ^ Af ≤ Dexp := by
        rw [hDexp]; exact le_max_right _ _
      have hfinal : (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖)
          ≤ Dexp * (2 : ℝ) ^ (Aexp * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))) / (N : ℝ) := by
        refine (Summable.tsum_le_tsum (fun p => htri p) hsumm_M0 hsumm_sum).trans ?_
        refine hsumfib.trans ?_
        have h2 : (SS.card : ℝ) * (Cf * (Cq * X) * Br ^ Af * W / (N : ℝ))
            ≤ (Cq ^ 2 * X ^ 2) * (Cf * (Cq * X) * Br ^ Af * W / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hcardb (by positivity)
        refine h2.trans ?_
        have h4 : (Cq ^ 2 * X ^ 2) * (Cf * (Cq * X) * Br ^ Af * W / (N : ℝ))
            = Cf * Cq ^ 3 * (X ^ 3 * Br ^ Af * W) / (N : ℝ) := by ring
        rw [h4]
        have h5 : Cf * Cq ^ 3 * (X ^ 3 * Br ^ Af * W) / (N : ℝ)
            ≤ Cf * Cq ^ 3 * (3 ^ Af
                * (2 : ℝ) ^ (Aexp * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ)))) / (N : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
        refine h5.trans ?_
        have h6 : Cf * Cq ^ 3 * (3 ^ Af
              * (2 : ℝ) ^ (Aexp * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))))
            = (Cf * Cq ^ 3 * 3 ^ Af) * (2 : ℝ) ^ (Aexp * ((2 : ℝ) ^ (ρ * (L : ℝ)) + (L : ℝ))) := by
          ring
        rw [h6]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDexple (by positivity)) (by positivity)
      -- ### conclusion
      constructor
      · have hfun : (fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.hiKconcN ρ P N l₁ l₂ k₁ k₂ p.1 p.2
            - Work.KMTAreas.A7.hiKmodNRep ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖)
            = fun p : ℤ × ℤ => ‖Work.KMTAreas.A7.hiM0Ker ρ P N l₁ l₂ k₁ k₂ p.1 p.2‖ := by
          funext p
          rw [hker p]
        rw [hfun]
        exact hsumm_M0
      · rw [tsum_congr (fun p => by rw [hker p])]
        have hAle : lmaxR l₁ l₂ k₁ k₂ = (L : ℝ) := by
          rw [rep_lmaxR_eq_repL l₁ l₂ k₁ k₂, ← hL]
        rw [hAle]
        refine hfinal.trans (le_of_eq ?_)
        rw [div_eq_mul_inv]

end

end Work.KMTAreas.A7
