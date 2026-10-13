import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.level0_psiSeries_concrete
import Submission.Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas
import Submission.Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.ClassCHon.CmpSupp.coeff_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon

/-- **The two per-mode facts of the level-`0` modal estimate for a general source**: the
weighted `L²`-integrability of each mode coefficient `acoeff α m F`, and the per-mode energy
inequality with the paper's constant `muSeq α m`:

  `muSeq α m · √(∫_z (a_m z)² w z²) ≤ √(∫_z (√(eNorm m) · cmode m F z)² w z²)`.

For `m ≥ 1` this is `Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy` (the sharp per-mode bound
`Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_o` at the clamped `cmode m F`, whose analytic
hypotheses come from `cmode_modeEnergy_integrable` and `cmode_isLittleO_at_zero`, with
`muSeq α m = lamR m − 3α² − 3α(5+α)/2`), and `hint_a` from
`Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas`; for `m = 0` the vanishing moment
`hmom` gives `cmode 0 F = 0` on `(0,∞)` and hence `acoeff α 0 F = 0` a.e.
(`Work.FTS.PhiStar.Series.acoeff_zero_of_fstar`), so both claims are trivial there.

These are exactly the `hint_a` and `hper` inputs of
`Work.FTS.ClassC.lintegral_psiTrunc_le` (and hence of the level-`0` honesty of
`psiSeries α F`); the compactly supported sibling of this pair of conjuncts is
`Work.FTS.ClassCHon.CmpSupp.coeff_facts`.  Use `Work.FTS.ClassCHon.CmpSupp.eNorm_bounds` for
`1 ≤ eNorm m`. -/
theorem perMode_data_of_source {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF0 : Work.Spaces.HkMem α 0 F) (hF1 : Work.Spaces.HkMem α 1 F)
    (hmom : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    (∀ m : ℕ, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    ∧ (∀ m : ℕ, Work.FTS.ClassC.muSeq α m *
        Real.sqrt (∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  classical
  have hIz : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  -- the vanishing moment kills the mode-`0` coefficient on the open half-line
  have hzero : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 :=
    fun z hz => Work.FTS.PhiStar.Series.acoeff_zero_of_fstar α F
      (fun t ht => hmom t ht) z hz
  refine ⟨?_, ?_⟩
  · -- conjunct 1: weighted `L²`-integrability of each mode coefficient
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      refine (MeasureTheory.integrableOn_zero).congr_fun ?_ hIz
      intro z hz
      change (0 : ℝ) = (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
      · rw [← hz0]
        simp [Work.Spaces.w]
      · rw [hzero z hz0]
        ring
    · exact Work.FTS.PhiStar.Honesty.integrableOn_acoeff_sq_w_sq_meas (α := α) (m := m) (F := F)
        hα hα4 hpos hsm hF0
        (Work.FTS.PhiStar.Honesty.aemeasurable_cmode_clamp (α := α) m hsm)
  · -- conjunct 2: the per-mode weighted energy inequality with `muSeq α m`
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · subst hm0
      have hInt0 : (∫ z in Work.Spaces.Iz,
          (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
        have h1 : (∫ z in Set.Ioi (0 : ℝ),
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2) = 0 := by
          rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_),
            MeasureTheory.integral_zero]
          rw [hzero z hz]
          ring
        exact (MeasureTheory.setIntegral_congr_set (f := fun z : ℝ =>
            (Work.FTS.PhiStar.Series.acoeff α 0 F z) ^ 2 * (Work.Spaces.w z) ^ 2)
          (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm).trans h1
      rw [hInt0, Work.FTS.ClassC.muSeq, if_pos rfl, Real.sqrt_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · have hm : 1 ≤ m := hpos
      have hmu : Work.FTS.ClassC.muSeq α m
          = Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
        rw [Work.FTS.ClassC.muSeq, if_neg (ne_of_gt hpos)]
      rw [hmu]
      exact Work.FTS.PhiStar.Honesty.acoeff_perModeEnergy (α := α) (F := F) m hα hα4 hm hsm
        hF0 (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds m).1
        (Work.FTS.PhiStar.Honesty.cmode_isLittleO_at_zero m hsm hF1)

end Work.FTS.ClassCHon
