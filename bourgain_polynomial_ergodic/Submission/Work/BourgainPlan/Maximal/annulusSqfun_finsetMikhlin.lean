import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbolSum_mikhlin
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpDefs
import Submission.Work.BourgainPlan.Maximal.annulusK_memLp
import Submission.Work.BourgainPlan.Maximal.mikhlinConvolutionLp

/-!
# The Mikhlin step of the `L^p` annulus square-function bound

The signed symbol sums `annulusSymbolSum b j F ε` have Mikhlin constants uniform in `j`, `F` and the
signs `ε` (`annulusSymbolSum_mikhlin`).  This module feeds them into the convolution form of the
Mikhlin multiplier theorem (`mikhlinConvolutionLp`) to obtain the `L^p` bound of the *signed*
convolution kernel, in the `∫⁻ ‖·‖ₑ^p` form in which the randomisation argument uses it:

**`annulusSymbolSum_convolution_le`**: for `1 < p < ∞` there is `C` with, for every `j`, every
finite `F`, every coefficient family `‖ε n‖ ≤ 1` and every `f ∈ L^p(ℝ)`,

  `∫⁻ x, ‖∫ y, 𝓕⁻ (∑_{n∈F} ε n · b (j+n)) (x - y) · f y‖^p ≤ C ∫⁻ x, ‖f x‖^p`.

The two integrability hypotheses of the Mikhlin bound are discharged by the finite-sum structure:
`Θ = ∑_{n∈F} ε n · b (j+n)` is a finite sum of integrable (compactly supported continuous)
functions, and `𝓕⁻Θ = ∑_{n∈F} ε n · K_{j+n}` is a finite sum of integrable kernels
(`annulusK_memLp`), the second identity being the (unconditional) additivity of `𝓕⁻`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

/-- The signed symbol sum is `C^∞`. -/
lemma contDiff_annulusSymbolSum (b : ℤ → ℝ → ℂ)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (annulusSymbolSum b j F ε) := by
  unfold annulusSymbolSum
  refine ContDiff.sum (f := fun n : ℤ => fun ξ : ℝ => ε n * b (j + n) ξ) (fun n hn => ?_)
  have h1 : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun _ : ℝ => ε n) := contDiff_const
  exact h1.mul (hsmooth (j + n))

/-- The signed symbol sum has compact support (it is supported in the finite union of the
intervals `[-2^{1-(j+n)}, 2^{1-(j+n)}]`, `n ∈ F`). -/
lemma hasCompactSupport_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) : HasCompactSupport (annulusSymbolSum b j F ε) := by
  rw [show annulusSymbolSum b j F ε = fun ξ : ℝ => ∑ n ∈ F, ε n * b (j + n) ξ from rfl]
  refine HasCompactSupport.of_support_subset_isCompact
    (K := ⋃ n ∈ (F : Set ℤ), Set.Icc (-((2:ℝ)^(1-(j+n)))) ((2:ℝ)^(1-(j+n)))) ?_ ?_
  · exact Set.Finite.isCompact_biUnion F.finite_toSet (fun n _ => isCompact_Icc)
  · intro ξ hξ
    simp only [Function.mem_support] at hξ
    have hex : ∃ n ∈ F, b (j + n) ξ ≠ 0 := by
      by_contra h
      push Not at h
      exact hξ (Finset.sum_eq_zero (fun n hn => by rw [h n hn, mul_zero]))
    obtain ⟨n, hnF, hbn⟩ := hex
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simpa using hnF
    · have hle : |ξ| ≤ (2:ℝ)^(1-(j+n)) := by
        by_contra hcon
        exact hbn (annulusK_eq_zero b hb (j + n) ξ (not_le.mp hcon))
      exact abs_le.mp hle

/-- The signed symbol sum is integrable. -/
lemma integrable_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) : Integrable (annulusSymbolSum b j F ε) volume :=
  ((contDiff_annulusSymbolSum b hsmooth j F ε).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_annulusSymbolSum b hb j F ε)

/-- The inverse Fourier transform of the signed symbol sum is integrable. -/
lemma integrable_fourierInv_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) :
    Integrable (FourierTransformInv.fourierInv (annulusSymbolSum b j F ε)) volume :=
  Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
    (hasCompactSupport_annulusSymbolSum b hb j F ε) (contDiff_annulusSymbolSum b hsmooth j F ε)

/-- **The Mikhlin bound for a signed annulus symbol sum.** -/
theorem annulusSymbolSum_convolution_le (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
      ∀ f : ℝ → ℂ, MemLp f (ENNReal.ofReal p) volume →
      ∫⁻ x, ‖∫ y : ℝ,
          FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y‖ₑ ^ p
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨Cm, hCm, hmik⟩ := mikhlinConvolutionLp p hp
  obtain ⟨A, hA0, hAb⟩ := annulusSymbolSum_mikhlin b hb hsmooth
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hA1 : 0 < A + 1 := by linarith
  refine ⟨(Cm * (A + 1)) ^ p, Real.rpow_pos_of_pos (mul_pos hCm hA1) p,
    fun j F ε hε f hf => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hAb j F ε hε
  have h1' : ∀ ξ : ℝ, ‖annulusSymbolSum b j F ε ξ‖ ≤ A + 1 := fun ξ => le_trans (h1 ξ) (by linarith)
  have h2' : ∀ ξ : ℝ, |ξ| * ‖deriv (annulusSymbolSum b j F ε) ξ‖ ≤ A + 1 :=
    fun ξ => le_trans (h2 ξ) (by linarith)
  have h3' : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (annulusSymbolSum b j F ε) ξ‖ ≤ A + 1 :=
    fun ξ => le_trans (h3 ξ) (by linarith)
  have hbnd := hmik (annulusSymbolSum b j F ε) (A + 1) (by linarith)
    (integrable_annulusSymbolSum b hb hsmooth j F ε)
    (annulusSymbolSum_contDiff b hsmooth j F ε) h1' h2' h3'
    (integrable_fourierInv_annulusSymbolSum b hb hsmooth j F ε) f hf
  have hconvm : AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ,
      FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y) volume := by
    have hJ : AEStronglyMeasurable (fun z : ℝ × ℝ =>
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (z.1 - z.2) * f z.2)
        ((volume : Measure ℝ).prod volume) :=
      ((integrable_fourierInv_annulusSymbolSum b hb hsmooth j F ε).aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
        hf.aestronglyMeasurable.comp_snd
    exact hJ.integral_prod_right'
  calc ∫⁻ x, ‖∫ y : ℝ,
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y‖ₑ ^ p
      = (MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ,
          FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
          (ENNReal.ofReal p) volume) ^ p := (annulusELpNorm_rpow_eq_lintegral hp0 hconvm).symm
    _ ≤ (ENNReal.ofReal (Cm * (A + 1)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) volume) ^ p :=
        ENNReal.rpow_le_rpow hbnd hp0.le
    _ = ENNReal.ofReal ((Cm * (A + 1)) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCm.le (by linarith)) hp0.le,
          annulusELpNorm_rpow_eq_lintegral hp0 hf.aestronglyMeasurable]

end Work.BourgainPlan.Maximal
