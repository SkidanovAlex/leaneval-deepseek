import Mathlib
import Submission.Work.TMPuig.DualDefs
import Submission.Work.TMPuig.FourierAux

open MeasureTheory intervalIntegral

noncomputable section

namespace Work.TMPuig

/-- The `[0,1]`-Fourier coefficient `fourierCoeffOn` agrees with the periodic integral `cF`. -/
lemma cF_eq_fourierCoeffOn {f : ℝ → ℂ} (hab : (0 : ℝ) < 1) (n : ℤ) :
    fourierCoeffOn hab f n = cF f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  rw [cF]
  apply intervalIntegral.integral_congr
  intro x _
  beta_reduce
  rw [smul_eq_mul, fourier_coe_apply, chr]
  congr 1
  congr 1
  simp only [sub_zero, Complex.ofReal_one, div_one]
  push_cast
  try ring

/-- For a continuous `1`-periodic complex function `f = dualV B` that never vanishes, the
Fourier coefficients `cF f n` are square summable (Parseval) and not all of them vanish. -/
theorem dualV_parseval {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hcont : Continuous (dualV B)) (hper : ∀ x, dualV B (x + 1) = dualV B x)
    (hne : ∀ x, dualV B x ≠ 0) :
    Summable (fun n : ℤ => ‖cF (dualV B) n‖ ^ 2) ∧ ∃ n : ℤ, cF (dualV B) n ≠ 0 := by
  set f : ℝ → ℂ := dualV B with hf
  have hfcont : Continuous f := by rw [hf]; exact hcont
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hmLp : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    obtain ⟨C, hC⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
        hfcont.continuousOn
    refine MemLp.of_bound hfcont.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun x hx => hC x (Set.Ioc_subset_Icc_self hx)
  have hsum : HasSum (fun n : ℤ => ‖cF f n‖ ^ 2) (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
    have hcoe : ∀ n : ℤ, fourierCoeffOn h01 f n = cF f n := fun n => cF_eq_fourierCoeffOn h01 n
    have h := hasSum_sq_fourierCoeffOn h01 hmLp
    simp only [sub_zero, inv_one, one_smul] at h
    simpa only [hcoe] using h
  refine ⟨hsum.summable, ?_⟩
  by_contra h
  push_neg at h
  have hzero : ∑' n : ℤ, ‖cF f n‖ ^ 2 = 0 := by simp [h]
  have hint : ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 = 0 := by
    have hh := hsum.tsum_eq
    rw [hzero] at hh
    exact hh.symm
  have hgcont : Continuous fun x : ℝ => ‖f x‖ ^ 2 := by fun_prop
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun x : ℝ => ‖f x‖ ^ 2) :=
    Filter.Eventually.of_forall fun x => by positivity
  have hae : (fun x : ℝ => ‖f x‖ ^ 2)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (0 : ℝ → ℝ) :=
    (integral_eq_zero_iff_of_le_of_nonneg_ae (show (0 : ℝ) ≤ 1 by norm_num) hnonneg
      (hgcont.intervalIntegrable 0 1)).mp hint
  have hEqOn : Set.EqOn (fun x : ℝ => ‖f x‖ ^ 2) (0 : ℝ → ℝ) (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae hgcont.continuousOn
      continuousOn_const
  have hhalf : ‖f (1 / 2)‖ ^ 2 = 0 := by
    simpa using hEqOn (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1)
  refine hne (1 / 2) ?_
  have h1 : ‖f (1 / 2)‖ = 0 := sq_eq_zero_iff.mp hhalf
  have h2 : f (1 / 2) = 0 := norm_eq_zero.mp h1
  simpa [hf] using h2

end Work.TMPuig
