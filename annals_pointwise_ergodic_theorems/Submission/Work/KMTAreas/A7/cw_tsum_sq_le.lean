import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTPlan.A6.PeriodizeFold

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **Poisson summation for the coefficient kernel, in the direction we need it.**
For an integrable `φ : ℝ → ℂ`, the `j`-th Fourier coefficient on the circle of the periodisation
`periodize φ` is the continuous Fourier transform `cw φ j = ∫ θ, φ θ * ee (-(j:ℝ) * θ)`.

This is proved by unfolding the coefficient as a circle integral, folding it back to `ℝ` with
`Work.KMTPlan.A6.PeriodizeFold`, and identifying `fourier (-j) (x : Circ)` with `ee (-(j:ℝ) * x)`. -/
theorem periodize_fourierCoeff_eq_cw {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) j = cw φ j := by
  have h1 : fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) j
      = ∫ t : Circ, Work.Analysis.IonescuWainger.periodize φ t * fourier (T := 1) (-j) t
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    rw [fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards with t
    simp only [smul_eq_mul, mul_comm]
  rw [h1, Work.KMTPlan.A6.PeriodizeFold hφ (fourier (T := 1) (-j)).continuous]
  simp only [cw]
  refine integral_congr_ae ?_
  filter_upwards with x
  congr 1
  rw [fourier_coe_apply]
  norm_num [ee]
  ring_nf

theorem cw_tsum_sq_le (f : ℝ → ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hf : Continuous f) (hsupp : ∀ θ, c < |θ| → f θ = 0) :
    ∑' j : ℤ, ‖cw f j‖ ^ 2 ≤ 4 * ∫ θ, ‖f θ‖ ^ 2 := by
  -- ## Step 0: `f` has compact support and is integrable
  have hsuppsub : Function.support f ⊆ Set.Icc (-c) c := by
    intro x hx
    rw [Set.mem_Icc]
    constructor
    · by_contra h
      rw [not_le] at h
      exact hx (hsupp x (by rw [abs_of_neg (by linarith)]; linarith))
    · by_contra h
      rw [not_le] at h
      exact hx (hsupp x (by rw [abs_of_pos (by linarith)]; linarith))
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsuppsub
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcs
  -- ## Step 1: a uniform bound for `‖f‖`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hC0 : ∀ x : ℝ, ‖f x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (-c) c
    · exact le_trans (hC x hx) (le_max_left _ _)
    · have h0 : f x = 0 := by
        by_contra hne
        exact hx (hsuppsub (by simpa [Function.mem_support] using hne))
      rw [h0, norm_zero]
      exact le_max_right _ _
  -- ## Step 2: the periodisation is in `L^∞`, hence in `L^2`, on the circle
  have hmp : MemLp (Work.Analysis.IonescuWainger.periodize f) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IonescuWainger.memLp_periodize hf.measurable hc.le hsupp hC0
  have hmp2 : MemLp (Work.Analysis.IonescuWainger.periodize f) 2
      Work.Analysis.IonescuWainger.circleMeasure :=
    hmp.mono_exponent le_top
  -- ## Step 3: Parseval on the circle
  have hparse : ∑' i : ℤ, ‖fourierCoeff (hmp2.toLp : Circ → ℂ) i‖ ^ 2
      = ∫ t : Circ, ‖(hmp2.toLp : Circ → ℂ) t‖ ^ 2
          ∂Work.Analysis.IonescuWainger.circleMeasure :=
    tsum_sq_fourierCoeff hmp2.toLp
  have hLHS : ∑' i : ℤ, ‖fourierCoeff (hmp2.toLp : Circ → ℂ) i‖ ^ 2
      = ∑' i : ℤ, ‖cw f i‖ ^ 2 := by
    refine tsum_congr fun i => ?_
    rw [← congr_fun (fourierCoeff_congr_ae hmp2.coeFn_toLp.symm) i,
      periodize_fourierCoeff_eq_cw hfi i]
  have hRHS : ∫ t : Circ, ‖(hmp2.toLp : Circ → ℂ) t‖ ^ 2
        ∂Work.Analysis.IonescuWainger.circleMeasure
      = ∫ t : Circ, ‖Work.Analysis.IonescuWainger.periodize f t‖ ^ 2
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hmp2.coeFn_toLp] with t ht
    rw [ht]
  -- ## Step 4: the pointwise decomposition of the periodisation on `(0,1]`
  have hpt : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x ≠ 1 →
      Work.Analysis.IonescuWainger.periodize f (x : Circ) = f x + f (x - 1) := by
    intro x hx hx1
    rw [Work.KMTContract.periodizeCoeEqTsum f x]
    have hzero : ∀ n : ℤ, n ∉ ({-1, 0} : Finset ℤ) → f (x + (n : ℝ)) = 0 := by
      intro n hn
      apply hsupp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      obtain ⟨hn1, hn0⟩ := hn
      rcases lt_trichotomy n 0 with h | h | h
      · have hn2 : (n : ℝ) ≤ -2 := by
          have : n ≤ (-2 : ℤ) := by omega
          exact_mod_cast this
        have hle : x + (n : ℝ) ≤ -1 := by linarith [hx.2, hn2]
        have hlt : x + (n : ℝ) < -1 := by
          rcases lt_or_eq_of_le hle with h' | h'
          · exact h'
          · exact absurd (by linarith [h', hx.2] : x = 1) hx1
        rw [abs_of_neg (by linarith)]
        linarith
      · exact absurd h hn0
      · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by
          have : (1 : ℤ) ≤ n := by omega
          exact_mod_cast this
        have hpos : 0 < x + (n : ℝ) := by linarith [hx.1]
        rw [abs_of_pos hpos]
        linarith [hx.1, hn1', hc1]
    rw [tsum_eq_sum (s := ({-1, 0} : Finset ℤ)) hzero,
      Finset.sum_pair (by norm_num : (-1 : ℤ) ≠ 0)]
    simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, add_zero]
    rw [show x + (-1 : ℝ) = x - 1 by ring, add_comm]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) 1 →
      Work.Analysis.IonescuWainger.periodize f (x : Circ) = f x + f (x - 1) := by
    rw [MeasureTheory.ae_iff]
    apply measure_mono_null _ (measure_singleton (1 : ℝ))
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact absurd (fun hxs => hpt x hxs h) hx
  have hae2 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc (0 : ℝ) 1 →
      ‖Work.Analysis.IonescuWainger.periodize f (x : Circ)‖ ^ 2 = ‖f x + f (x - 1)‖ ^ 2 := by
    filter_upwards [hae] with x hx
    intro hxs
    rw [hx hxs]
  -- ## Step 4b: the pointwise quadratic bound
  have hpt_bound : ∀ x : ℝ, ‖f x + f (x - 1)‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖f (x - 1)‖ ^ 2 := by
    intro x
    have h1 : ‖f x + f (x - 1)‖ ≤ ‖f x‖ + ‖f (x - 1)‖ := norm_add_le _ _
    have h2 : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ ‖f (x - 1)‖ := norm_nonneg _
    have h4 : (0 : ℝ) ≤ ‖f x + f (x - 1)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖f x‖ - ‖f (x - 1)‖)]
  -- ## Step 5: integrability of the pieces
  have hInt_f : Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
    have hcont : Continuous (fun x : ℝ => ‖f x‖ ^ 2) := hf.norm.pow 2
    have hs : HasCompactSupport (fun x : ℝ => ‖f x‖ ^ 2) :=
      hcs.comp_left (g := fun y : ℂ => ‖y‖ ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport hs
  have hshiftCS : HasCompactSupport (fun x : ℝ => f (x - 1)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun y : ℝ => y + 1) '' tsupport f) ?_ ?_
    · exact hcs.image (by continuity)
    · intro x hx
      have hx' : f (x - 1) ≠ 0 := by simpa [Function.mem_support] using hx
      exact ⟨x - 1, subset_tsupport f hx', by ring⟩
  have hInt_shift : Integrable (fun x : ℝ => ‖f (x - 1)‖ ^ 2) := by
    have hcont : Continuous (fun x : ℝ => ‖f (x - 1)‖ ^ 2) :=
      ((hf.comp (continuous_id.sub continuous_const)).norm).pow 2
    have hs : HasCompactSupport (fun x : ℝ => ‖f (x - 1)‖ ^ 2) :=
      hshiftCS.comp_left (g := fun y : ℂ => ‖y‖ ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport hs
  have hInt_G : Integrable (fun x : ℝ => 2 * ‖f x‖ ^ 2 + 2 * ‖f (x - 1)‖ ^ 2) :=
    (hInt_f.const_mul 2).add (hInt_shift.const_mul 2)
  have hInt_F : Integrable (fun x : ℝ => ‖f x + f (x - 1)‖ ^ 2) := by
    have hcont : Continuous (fun x : ℝ => ‖f x + f (x - 1)‖ ^ 2) := by fun_prop
    refine Integrable.mono' hInt_G hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt_bound x
  -- ## Step 6: the estimate on the fundamental domain
  have hmono : ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x + f (x - 1)‖ ^ 2
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1, (2 * ‖f x‖ ^ 2 + 2 * ‖f (x - 1)‖ ^ 2) :=
    MeasureTheory.setIntegral_mono_on_ae hInt_F.integrableOn hInt_G.integrableOn
      measurableSet_Ioc (Filter.Eventually.of_forall fun x _ => hpt_bound x)
  have hsplit : ∫ x in Set.Ioc (0 : ℝ) 1, (2 * ‖f x‖ ^ 2 + 2 * ‖f (x - 1)‖ ^ 2)
      = 2 * (∫ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ ^ 2)
        + 2 * (∫ x in Set.Ioc (0 : ℝ) 1, ‖f (x - 1)‖ ^ 2) := by
    rw [MeasureTheory.integral_add (f := fun x : ℝ => 2 * ‖f x‖ ^ 2)
        (g := fun x : ℝ => 2 * ‖f (x - 1)‖ ^ 2)
        (hInt_f.const_mul 2).integrableOn (hInt_shift.const_mul 2).integrableOn,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hbound1 : ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ ^ 2 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 :=
    MeasureTheory.setIntegral_le_integral hInt_f (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have htrans : ∫ x : ℝ, ‖f (x - 1)‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 :=
    MeasureTheory.integral_sub_right_eq_self (fun y : ℝ => ‖f y‖ ^ 2) 1
  have hbound2 : ∫ x in Set.Ioc (0 : ℝ) 1, ‖f (x - 1)‖ ^ 2 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 := by
    refine le_trans (MeasureTheory.setIntegral_le_integral hInt_shift
      (Filter.Eventually.of_forall fun x => sq_nonneg _)) ?_
    rw [htrans]
  have hfinal : ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x + f (x - 1)‖ ^ 2
      ≤ 4 * ∫ x : ℝ, ‖f x‖ ^ 2 := by
    calc ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x + f (x - 1)‖ ^ 2
        ≤ ∫ x in Set.Ioc (0 : ℝ) 1, (2 * ‖f x‖ ^ 2 + 2 * ‖f (x - 1)‖ ^ 2) := hmono
      _ = 2 * (∫ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ ^ 2)
            + 2 * (∫ x in Set.Ioc (0 : ℝ) 1, ‖f (x - 1)‖ ^ 2) := hsplit
      _ ≤ 2 * (∫ x : ℝ, ‖f x‖ ^ 2) + 2 * (∫ x : ℝ, ‖f x‖ ^ 2) := by
          linarith [hbound1, hbound2]
      _ = 4 * ∫ x : ℝ, ‖f x‖ ^ 2 := by ring
  -- ## Step 7: unfold the circle integral over the fundamental domain `(0,1]`
  have hunfold : ∫ t : Circ, ‖Work.Analysis.IonescuWainger.periodize f t‖ ^ 2
        ∂Work.Analysis.IonescuWainger.circleMeasure
      = ∫ x in Set.Ioc (0 : ℝ) 1, ‖Work.Analysis.IonescuWainger.periodize f (x : Circ)‖ ^ 2 := by
    rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.integral_haarAddCircle]
    simp only [inv_one, one_smul]
    rw [← AddCircle.integral_preimage (1 : ℝ) 0
      (fun t : Circ => ‖Work.Analysis.IonescuWainger.periodize f t‖ ^ 2)]
    norm_num
  have hcongr : ∫ x in Set.Ioc (0 : ℝ) 1,
        ‖Work.Analysis.IonescuWainger.periodize f (x : Circ)‖ ^ 2
      = ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x + f (x - 1)‖ ^ 2 :=
    MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hae2
  have hcircle : ∫ t : Circ, ‖Work.Analysis.IonescuWainger.periodize f t‖ ^ 2
        ∂Work.Analysis.IonescuWainger.circleMeasure ≤ 4 * ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [hunfold, hcongr]
    exact hfinal
  -- ## Step 8: assemble
  calc ∑' j : ℤ, ‖cw f j‖ ^ 2
      = ∑' i : ℤ, ‖fourierCoeff (hmp2.toLp : Circ → ℂ) i‖ ^ 2 := hLHS.symm
    _ = ∫ t : Circ, ‖(hmp2.toLp : Circ → ℂ) t‖ ^ 2
          ∂Work.Analysis.IonescuWainger.circleMeasure := hparse
    _ = ∫ t : Circ, ‖Work.Analysis.IonescuWainger.periodize f t‖ ^ 2
          ∂Work.Analysis.IonescuWainger.circleMeasure := hRHS
    _ ≤ 4 * ∫ x : ℝ, ‖f x‖ ^ 2 := hcircle

end Work.KMTAreas.A7
