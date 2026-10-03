import Mathlib
import Submission.Work.KMTAreas.A7.ExcDefs
import Submission.Work.KMTAreas.A7.FourierDecayExplicit
import Submission.Work.KMTAreas.A7.IwArithFreqsCardUniform
import Submission.Work.KMTAreas.A7.IwKernelEqFourier

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory
open scoped FourierTransform BigOperators ENNReal NNReal

namespace Work.KMTAreas.A7

/-! ## The comparison weight -/

/-- The comparison sequence for `j^{-2}` decay on `ℤ`. -/
noncomputable def kmtKernWeight (j : ℤ) : ℂ := ((1 / (1 + |(j : ℝ)|) ^ 2 : ℝ) : ℂ)

lemma norm_kmtKernWeight (j : ℤ) : ‖kmtKernWeight j‖ = 1 / (1 + |(j : ℝ)|) ^ 2 := by
  rw [kmtKernWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma summable_kmtKernWeight : Summable (fun j : ℤ => ‖kmtKernWeight j‖) :=
  Work.KMTContract.kernel_l1_of_decay (c := kmtKernWeight) (C := 1)
    (fun j => by rw [norm_kmtKernWeight j])

/-- The representative of a frequency on the circle, in `[0,1)`. -/
noncomputable def kmtFreqRep (α : Work.Analysis.IonescuWainger.Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 α).val

lemma abs_kmtFreqRep_le_one (α : Work.Analysis.IonescuWainger.Circle) : |kmtFreqRep α| ≤ 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 α).2
  rw [Set.mem_Ico] at h
  rw [kmtFreqRep, abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## The two `L¹` bounds -/

/-- The `L¹` norm of a finite sum of translates of a compactly supported continuous function is
at most the number of translates times the `L¹` norm. -/
lemma integral_norm_sum_kmtTransl_le (A : Finset Work.Analysis.IonescuWainger.Circle)
    (F : ℝ → ℂ) (hFcont : Continuous F) (hFcs : HasCompactSupport F) :
    (∫ y : ℝ, ‖∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖)
      ≤ (A.card : ℝ) * ∫ θ : ℝ, ‖F θ‖ := by
  have hintF : Integrable F := hFcont.integrable_of_hasCompactSupport hFcs
  have heach : ∀ α ∈ A,
      Integrable (fun y : ℝ => ‖F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖) :=
    fun α _ => (hintF.comp_sub_right _).norm
  have hsumint : Integrable (fun y : ℝ =>
      ∑ α ∈ A, ‖F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖) :=
    MeasureTheory.integrable_finsetSum _ heach
  have hcont : Continuous (fun y : ℝ => ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) :=
    continuous_finsetSum _ (fun α _ => hFcont.comp (continuous_id.sub continuous_const))
  have hsum_int : Integrable (fun y : ℝ =>
      ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) :=
    Integrable.mono' hsumint hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y =>
        norm_sum_le A (fun α => F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val))))
  have hlhs : Integrable (fun y : ℝ =>
      ‖∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖) := hsum_int.norm
  calc (∫ y : ℝ, ‖∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖)
      ≤ ∫ y : ℝ, ∑ α ∈ A, ‖F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖ :=
        integral_mono hlhs hsumint (fun y => norm_sum_le _ _)
    _ = ∑ α ∈ A, ∫ y : ℝ, ‖F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖ :=
        MeasureTheory.integral_finsetSum _ heach
    _ = (A.card : ℝ) * ∫ θ : ℝ, ‖F θ‖ := by
        have hcongr : (∑ α ∈ A, ∫ y : ℝ, ‖F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)‖)
            = ∑ _α ∈ A, ∫ θ : ℝ, ‖F θ‖ :=
          Finset.sum_congr rfl (fun α _ =>
            integral_sub_right_eq_self (fun θ : ℝ => ‖F θ‖) _)
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]

/-- The `L¹` norm of the second derivative of a finite sum of translates of a compactly supported
`C²` function is at most the number of translates times the `L¹` norm of the second derivative. -/
lemma integral_norm_iteratedDeriv_sum_kmtTransl_le (A : Finset Work.Analysis.IonescuWainger.Circle)
    (F : ℝ → ℂ) (hFcd : ContDiff ℝ 2 F) (hFcs : HasCompactSupport F) :
    (∫ y : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
        ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖)
      ≤ (A.card : ℝ) * ∫ θ : ℝ, ‖iteratedDeriv 2 F θ‖ := by
  have hF2eq : iteratedDeriv 2 F = deriv (deriv F) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hF2cs : HasCompactSupport (iteratedDeriv 2 F) := by rw [hF2eq]; exact hFcs.deriv.deriv
  have hF2cont : Continuous (iteratedDeriv 2 F) := hFcd.continuous_iteratedDeriv 2 (by norm_num)
  have hintF2 : Integrable (iteratedDeriv 2 F) := hF2cont.integrable_of_hasCompactSupport hF2cs
  have hshift : ∀ c : ℝ, iteratedDeriv 2 (fun z : ℝ => F (z - c))
      = fun y : ℝ => iteratedDeriv 2 F (y - c) := fun c => iteratedDeriv_comp_sub_const 2 F c
  have hderiv : ∀ y : ℝ, iteratedDeriv 2 (fun y : ℝ =>
        ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y
      = ∑ α ∈ A, iteratedDeriv 2 (fun z : ℝ =>
          F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y := by
    intro y
    have hfun : (∑ α ∈ A, (fun z : ℝ => F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)))
        = fun y : ℝ => ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val) := by
      funext z; rw [Finset.sum_apply]
    rw [← hfun]
    exact iteratedDeriv_sum (n := 2) (x := y) (I := A)
      (f := fun α => fun z : ℝ => F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val))
      (fun α _ => (hFcd.comp (contDiff_id.sub contDiff_const)).contDiffAt)
  have heach : ∀ α ∈ A, Integrable (fun y : ℝ => ‖iteratedDeriv 2 (fun z : ℝ =>
      F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖) := by
    intro α _
    rw [hshift]
    exact (hintF2.comp_sub_right _).norm
  have hpt : ∀ y : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
        ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖
      ≤ ∑ α ∈ A, ‖iteratedDeriv 2 (fun z : ℝ =>
          F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖ := by
    intro y; rw [hderiv y]; exact norm_sum_le _ _
  have hsumint : Integrable (fun y : ℝ => ∑ α ∈ A, ‖iteratedDeriv 2 (fun z : ℝ =>
      F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖) :=
    MeasureTheory.integrable_finsetSum _ heach
  have hsumcd : ContDiff ℝ 2 (fun y : ℝ =>
      ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) :=
    ContDiff.sum (fun α _ => hFcd.comp (contDiff_id.sub contDiff_const))
  have hderiv_int : Integrable (fun y : ℝ => iteratedDeriv 2 (fun y : ℝ =>
      ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y) :=
    Integrable.mono' hsumint (hsumcd.continuous_iteratedDeriv 2 (by norm_num)).aestronglyMeasurable
      (Filter.Eventually.of_forall hpt)
  have hlhs : Integrable (fun y : ℝ => ‖iteratedDeriv 2 (fun y : ℝ =>
      ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖) := hderiv_int.norm
  calc (∫ y : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
        ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖)
      ≤ ∫ y : ℝ, ∑ α ∈ A, ‖iteratedDeriv 2 (fun z : ℝ =>
          F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖ := integral_mono hlhs hsumint hpt
    _ = ∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 (fun z : ℝ =>
          F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖ :=
        MeasureTheory.integral_finsetSum _ heach
    _ = (A.card : ℝ) * ∫ θ : ℝ, ‖iteratedDeriv 2 F θ‖ := by
        have hcongr : (∑ α ∈ A, ∫ y : ℝ, ‖iteratedDeriv 2 (fun z : ℝ =>
              F (z - (AddCircle.equivIco (1 : ℝ) 0 α).val)) y‖)
            = ∑ _α ∈ A, ∫ θ : ℝ, ‖iteratedDeriv 2 F θ‖ := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [hshift]
          exact integral_sub_right_eq_self (fun θ : ℝ => ‖iteratedDeriv 2 F θ‖) _
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]

/-! ## The main statement -/

/-- The convolution kernel of `kmtProj ρ l k` has ℓ¹ norm bounded by a constant `R l k`
depending only on `(l,k)`, uniformly over the Ionescu--Wainger parameter `ρ ∈ (0,1]`.
Suggested route: as in the proof of `Work.KMTContract.kmtKernel_decay` (which one may read and
mirror), the kernel equals `𝓕 G (j)` for `G = ∑_{α ∈ iwArithFreqs ρ l} kmtEta (·/2^k - a_α)`,
a `C²` function with compact support; `Work.KMTContract.fourierDecayRefl` gives the pointwise
decay with the *explicit* constant `4 * max ‖G‖₁ ‖G''‖₁ + 1`, and `‖G‖₁ ≤ card A · 2^{k+1} ‖η‖₁`,
`‖G''‖₁ ≤ card A · 2^{-k} ‖η''‖₁` while `card A ≤ 2^{2^l}` for `ρ ≤ 1`, giving a `ρ`-free bound
after summing `∑_j 1/(1+|j|)^2`. -/
theorem KmtKernelL1Uniform :
    ∃ R : ℕ → ℤ → ℝ, (∀ l k, 0 < R l k) ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (l : ℕ) (k : ℤ),
        Summable (fun j : ℤ =>
          ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖) ∧
        (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖) ≤ R l k := by
  classical
  obtain ⟨Bcard, hBpos, hBcard⟩ := IwArithFreqsCardUniform
  set Ac : ℤ → ℝ := fun k => ∫ θ : ℝ, ‖Work.Analysis.IonescuWainger.etaCut
    Work.KMTContract.kmtEta k θ‖ with hAc
  set Bc : ℤ → ℝ := fun k => ∫ θ : ℝ,
    ‖iteratedDeriv 2 (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) θ‖ with hBc
  set S : ℝ := ∑' j : ℤ, ‖kmtKernWeight j‖ with hS
  have hSpos : 0 < S := by
    rw [hS]
    exact Summable.tsum_pos summable_kmtKernWeight (fun j => norm_nonneg _) 0
      (by rw [norm_kmtKernWeight]; norm_num)
  have hAcnn : ∀ k, 0 ≤ Ac k := by
    intro k; rw [hAc]; exact integral_nonneg (fun _ => norm_nonneg _)
  have hBcnn : ∀ k, 0 ≤ Bc k := by
    intro k; rw [hBc]; exact integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨fun l k => (4 * Bcard l * max (Ac k) (Bc k) + 1) * S, ?_, ?_⟩
  · intro l k
    have h3 : 0 < 4 * Bcard l * max (Ac k) (Bc k) + 1 := by
      nlinarith [hBpos l, hAcnn k, hBcnn k, le_max_left (Ac k) (Bc k)]
    exact mul_pos h3 hSpos
  · intro ρ hρ hρ1 l k
    have hcardle : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ≤ Bcard l :=
      hBcard ρ hρ hρ1 l
    -- the cutoff
    have hFcdtop : ContDiff ℝ (↑(⊤ : ℕ∞))
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) :=
      (Work.KMTContract.etaCutRegular k).1
    have hFcd : ContDiff ℝ 2 (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) :=
      hFcdtop.of_le (WithTop.coe_le_coe.mpr le_top)
    have hFcont : Continuous
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) := hFcd.continuous
    have hFzero : ∀ θ : ℝ, (2:ℝ)^k ≤ |θ| →
        Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ = 0 :=
      fun θ h => (Work.KMTContract.etaCutRegular k).2.2 θ h
    have hFcs : HasCompactSupport
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (-((2:ℝ)^k)) ((2:ℝ)^k)) isCompact_Icc ?_
      intro y hy
      have h : ¬ ((2:ℝ)^k ≤ |y|) := fun hh => hy (hFzero y hh)
      rw [not_le, abs_lt] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    -- the function whose Fourier transform is the kernel
    set G : ℝ → ℂ := fun y => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
        Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (y - kmtFreqRep α) with hGdef
    have hGcont : Continuous G := by
      rw [hGdef]
      exact continuous_finsetSum _ (fun α _ => hFcont.comp (continuous_id.sub continuous_const))
    have hGcd : ContDiff ℝ 2 G := by
      rw [hGdef]
      exact ContDiff.sum (fun α _ => hFcd.comp (contDiff_id.sub contDiff_const))
    have hGzero : ∀ y : ℝ, (2:ℝ)^k + 1 ≤ |y| → G y = 0 := by
      rw [hGdef]; intro y hy
      refine Finset.sum_eq_zero (fun α _ => ?_)
      apply hFzero
      have h1 : |kmtFreqRep α| ≤ 1 := abs_kmtFreqRep_le_one α
      have h2 : |y| - |kmtFreqRep α| ≤ |y - kmtFreqRep α| := abs_sub_abs_le_abs_sub y _
      linarith
    have hGcs : HasCompactSupport G := by
      refine HasCompactSupport.of_support_subset_isCompact
        (K := Set.Icc (-((2:ℝ)^k + 1)) ((2:ℝ)^k + 1)) isCompact_Icc ?_
      intro y hy
      have h : ¬ ((2:ℝ)^k + 1 ≤ |y|) := fun hh => hy (hGzero y hh)
      rw [not_le, abs_lt] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    have hdec := FourierDecayExplicit hGcd hGcs
    -- the two `L¹` bounds
    have hInt1 : ∫ y : ℝ, ‖G y‖
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * Ac k := by
      have h1 := integral_norm_sum_kmtTransl_le (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) hFcont hFcs
      rw [hGdef, hAc]
      exact h1
    have hInt2 : ∫ y : ℝ, ‖iteratedDeriv 2 G y‖
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * Bc k := by
      have h1 := integral_norm_iteratedDeriv_sum_kmtTransl_le
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) hFcd hFcs
      rw [hGdef, hBc]
      exact h1
    -- the kernel decay
    have hkdec : ∀ j : ℤ,
        ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖
        ≤ (4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1)
            / (1 + |(j:ℝ)|) ^ 2 := by
      intro j
      rw [IwKernelEqFourier ρ l k j]
      exact hdec (j : ℝ)
    have hsumm : Summable (fun j : ℤ =>
        ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖) :=
      Work.KMTContract.kernel_l1_of_decay hkdec
    have hcmp : Summable (fun j : ℤ =>
        (4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1) * ‖kmtKernWeight j‖) :=
      summable_kmtKernWeight.mul_left _
    have htsum : (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖)
        ≤ (4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1) * S := by
      have h1 : (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
              (Work.Analysis.IonescuWainger.iwSymbolSet
                (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
                (Work.Analysis.IonescuWainger.periodize
                  (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖)
          ≤ ∑' j : ℤ, (4 * max (∫ y : ℝ, ‖G y‖)
              (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1) * ‖kmtKernWeight j‖ :=
        Summable.tsum_le_tsum (fun j => by
          calc ‖Work.Analysis.IWMultiplier.iwKernel
                  (Work.Analysis.IonescuWainger.iwSymbolSet
                    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
                    (Work.Analysis.IonescuWainger.periodize
                      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖
              ≤ (4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1)
                  / (1 + |(j:ℝ)|) ^ 2 := hkdec j
            _ = (4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1)
                  * ‖kmtKernWeight j‖ := by
                rw [norm_kmtKernWeight j, div_eq_mul_one_div]) hsumm hcmp
      rw [tsum_mul_left] at h1
      rw [hS]
      exact h1
    refine ⟨hsumm, ?_⟩
    have hM : max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖)
        ≤ Bcard l * max (Ac k) (Bc k) := by
      refine max_le ?_ ?_
      · calc ∫ y : ℝ, ‖G y‖
            ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * Ac k := hInt1
          _ ≤ Bcard l * max (Ac k) (Bc k) :=
              mul_le_mul hcardle (le_max_left _ _) (hAcnn k) (hBpos l).le
      · calc ∫ y : ℝ, ‖iteratedDeriv 2 G y‖
            ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) * Bc k := hInt2
          _ ≤ Bcard l * max (Ac k) (Bc k) :=
              mul_le_mul hcardle (le_max_right _ _) (hBcnn k) (hBpos l).le
    have h4 : 4 * max (∫ y : ℝ, ‖G y‖) (∫ y : ℝ, ‖iteratedDeriv 2 G y‖) + 1
        ≤ 4 * Bcard l * max (Ac k) (Bc k) + 1 := by nlinarith [hM]
    exact le_trans htsum (mul_le_mul_of_nonneg_right h4 hSpos.le)

end Work.KMTAreas.A7
