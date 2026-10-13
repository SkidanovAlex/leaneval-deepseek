import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.ClassC.level0_psiSeries_concrete
import Submission.Work.FTS.ClassCHon.radGreen_modeEnergy_interval
import Submission.Work.FTS.ClassCHon.radGreen_size_bound
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds
import Submission.Work.FTS.ClassCHon.CmpSupp.coeff_le_decay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.ClassCHon.CmpSupp

theorem coeff_facts {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {F : ℝ → ℝ → ℝ} (hmom : ∀ z : ℝ, Work.Elliptic.Fstar F z = 0)
    (hsmooth : ∀ m : ℕ, ∀ n : ℕ,
        ContDiffOn ℝ n (Work.FTS.PhiStar.Series.cmode m F) (Set.Ioi 0))
    (hsuppc : ∀ m : ℕ, ∀ z : ℝ, z ∉ Set.Icc a b → Work.FTS.PhiStar.Series.cmode m F z = 0)
    (hfar : ∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 1))
    (hnear : ∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hbound : ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b,
        |Work.FTS.PhiStar.Series.cmode m F t|
          ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) :
    (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz)
    ∧ (∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
            (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
              * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2))
    ∧ (∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
        ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|)) := by
  obtain ⟨A, hA0, hAsz⟩ := Work.FTS.ClassCHon.radGreen_size_bound
  obtain ⟨K, hKpos, hKbd⟩ := hbound
  have hKnn : 0 ≤ K := hKpos.le
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  -- the uniform size bound on the source, valid on all of `ℝ`
  have hMsupp : ∀ m : ℕ, ∀ t : ℝ,
      |Work.FTS.PhiStar.Series.cmode m F t|
        ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    intro m t
    by_cases ht : t ∈ Set.Icc a b
    · exact hKbd m t ht
    · rw [hsuppc m t ht, abs_zero]
      exact div_nonneg hKnn (Real.sqrt_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: weighted `L²`-integrability of `acoeff`
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      refine (MeasureTheory.integrableOn_zero).congr_fun ?_ hIz
      intro z hz
      change (0 : ℝ) = (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
      · rw [← hz0]
        simp [Work.Spaces.w]
      · rw [Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F (fun t ht => hmom t) z hz0]
        ring
    · have hm : 1 ≤ m := hpos
      have h := Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn (α := α) (m := m)
        (c := Work.FTS.PhiStar.Series.cmode m F) hα hα4 hm ((hsmooth m 0).continuousOn)
        (hnear m) (hfar m)
      exact h.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm
  · -- conjunct 2: the weighted `L²` comparison
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      have hInt0 : (∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
        have h1 : (∫ z in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_),
            MeasureTheory.integral_zero]
          rw [Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F (fun t ht => hmom t) z hz]
          ring
        exact (MeasureTheory.setIntegral_congr_set (f := fun z : ℝ =>
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm).trans h1
      rw [hInt0, Work.FTS.ClassC.muSeq, if_pos rfl, Real.sqrt_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · have hm : 1 ≤ m := hpos
      have hMnn : 0 ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
        div_nonneg hKnn (Real.sqrt_nonneg _)
      -- the sharp per-mode energy bound
      have henergy := Work.FTS.ClassCHon.radGreen_modeEnergy_interval (α := α) hα hα4 m hm ha hab
        (c := Work.FTS.PhiStar.Series.cmode m F) (hsmooth m) ⟨_, hMnn, hMsupp m⟩ (hsuppc m)
      have hAtr : (∫ z in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
        MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0))
      have hCtr : (∫ z in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
        MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0))
      have hmu : Work.FTS.ClassC.muSeq α m
          = Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
        rw [Work.FTS.ClassC.muSeq, if_neg (ne_of_gt hpos)]
      have hE : Work.FTS.ClassC.muSeq α m ^ 2 * (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        rw [← hAtr, ← hCtr, hmu]
        exact henergy
      have hmu0 : 0 ≤ Work.FTS.ClassC.muSeq α m :=
        (Work.FTS.ClassC.muSeq_pos hα hα4 m).le
      have hAnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      have hCnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      have hRHS : (∫ z in Work.Spaces.Iz,
            (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
              * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = Work.EllipticEst.ModalSolution.eNorm m * (∫ z in Work.Spaces.Iz,
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        have hcongr : (∫ z in Work.Spaces.Iz,
              (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
            = ∫ z in Work.Spaces.Iz, Work.EllipticEst.ModalSolution.eNorm m
                * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
          apply MeasureTheory.setIntegral_congr_fun hIz
          intro z _
          show (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
              * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2
            = Work.EllipticEst.ModalSolution.eNorm m
              * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          rw [mul_pow, Real.sq_sqrt (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul]
      calc Work.FTS.ClassC.muSeq α m * Real.sqrt (∫ z in Work.Spaces.Iz,
              (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = Real.sqrt (Work.FTS.ClassC.muSeq α m ^ 2 * (∫ z in Work.Spaces.Iz,
              (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
            rw [Real.sqrt_mul (sq_nonneg (Work.FTS.ClassC.muSeq α m)), Real.sqrt_sq hmu0]
        _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
            Real.sqrt_le_sqrt hE
        _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
              (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
            rw [hRHS]
            exact Real.sqrt_le_sqrt
              (le_mul_of_one_le_left hCnn (eNorm_bounds m).1)
  · -- conjunct 3: summability in `m`
    intro z hz
    have hsum0 : Summable (fun m : ℕ => ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hsum1 : Summable (fun m : ℕ => (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
      convert hsum0 using 1
      ext m
      rw [Real.rpow_neg (Nat.cast_nonneg m)]
    have hsum : Summable (fun m : ℕ => (2 * A * K) * (m : ℝ) ^ (-(3 / 2 : ℝ))) :=
      hsum1.mul_left _
    refine Summable.of_nonneg_of_le (f := fun m : ℕ => (2 * A * K) * (m : ℝ) ^ (-(3 / 2 : ℝ)))
      ?_ ?_ hsum
    · intro m
      exact mul_nonneg (by positivity) (abs_nonneg _)
    · intro m
      rcases Nat.eq_zero_or_pos m with hm0 | hpos
      · subst hm0
        rw [Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F (fun t ht => hmom t) z hz,
          abs_zero, mul_zero, Nat.cast_zero,
          Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ)) ≠ 0), mul_zero]
      · have hm : 1 ≤ m := hpos
        have hsz := hAsz α hα hα4 m hm ha
          (div_nonneg hKnn (Real.sqrt_nonneg _)) (hsmooth m) (hMsupp m) (hsuppc m) z hz
        have h1 : |Work.FTS.PhiStar.Series.acoeff α m F z|
            ≤ A * (K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) / (m : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2), mul_comm]
          exact hsz
        calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|
            ≤ ((m : ℝ) + 1)
                * (A * (K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) / (m : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (2 * A * K) * (m : ℝ) ^ (-(3 / 2 : ℝ)) := coeff_le_decay A K hA0 hKpos m hm

end Work.FTS.ClassCHon.CmpSupp
