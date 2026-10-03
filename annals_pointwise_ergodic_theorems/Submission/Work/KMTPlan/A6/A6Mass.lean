/-
# The `L¹` mass of the derivatives of the §5 bumps

This module proves the two `L¹`-mass estimates for the derivatives of the bumps
`varphiN N k` and `varphitildeN d N k` of the §5 model approximation, in the form needed by the
single-scale symbol estimate: for `m ≤ 2`,

`∫⁻ ξ, ‖(φ_N)^{(m)}(ξ)‖ ≤ C (2^{Log N}/2^k)^{m-1}`,

and the same with the `d`-fold scale `2^{d(Log N - k)}` for `varphitildeN d N k`.

The proof is the elementary "dilation" computation: a bump is a difference of two dilations
`η(c ξ) − η(2^d c ξ)` of the fixed `C²`-cutoff `η = kmtEta`, and for a dilation the mass of the
`m`-th derivative is `c^{m-1} ∫‖η^{(m)}‖` exactly.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiN_mass_bounds
import Submission.Work.KMTPlan.A6.A6Scale

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

noncomputable section

/-! ## Rescalings of a function of one real variable -/

theorem norm_ofReal_eq_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  simpa [pow_two] using Real.sqrt_sq_eq_abs r

theorem lintegral_norm_comp_mul_left (f : ℝ → ℂ) (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ‖f (c * ξ)‖)
      = ENNReal.ofReal c⁻¹ * ∫⁻ ξ : ℝ, ENNReal.ofReal ‖f ξ‖ := by
  have hmap : MeasureTheory.Measure.map (fun x : ℝ => c * x) MeasureTheory.volume
      = ENNReal.ofReal c⁻¹ • MeasureTheory.volume := by
    rw [Real.map_volume_mul_left (ne_of_gt hc), abs_of_pos (inv_pos.mpr hc)]
  have hmeas : Measurable (fun x : ℝ => c * x) := measurable_const_mul c
  have h1 : (∫⁻ ξ : ℝ, ENNReal.ofReal ‖f ξ‖
        ∂MeasureTheory.Measure.map (fun x : ℝ => c * x) MeasureTheory.volume)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal ‖f (c * ξ)‖ := by
    rw [MeasureTheory.lintegral_map (hf.norm.ennreal_ofReal) hmeas]
  rw [← h1, hmap, MeasureTheory.lintegral_smul_measure, smul_eq_mul]

theorem iteratedDeriv_comp_mul_left_eq (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (c : ℝ) (m : ℕ)
    (hm : m ≤ 2) :
    iteratedDeriv m (fun ξ : ℝ => f (c * ξ))
      = fun ξ : ℝ => (c : ℝ) ^ m • iteratedDeriv m f (c * ξ) := by
  exact iteratedDeriv_comp_const_smul (𝕜 := ℝ) (F := ℂ)
    (hf.of_le (by exact_mod_cast hm)) c

theorem lintegral_norm_deriv_rescale (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) {c : ℝ} (hc : 0 < c)
    (m : ℕ) (hm : m ≤ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => f (c * ξ)) ξ‖)
      = ENNReal.ofReal (c ^ ((m : ℝ) - 1))
          * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m f ξ‖) := by
  rw [iteratedDeriv_comp_mul_left_eq f hf c m hm]
  have hmeas : Measurable (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m f ξ‖) :=
    ((hf.continuous_iteratedDeriv m (by exact_mod_cast hm)).norm).measurable.ennreal_ofReal
  have hmeas2 : Measurable (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m f (c * ξ)‖) :=
    hmeas.comp (measurable_const_mul c)
  have hnorm : ∀ ξ : ℝ, ‖(c : ℝ) ^ m • iteratedDeriv m f (c * ξ)‖
      = c ^ m * ‖iteratedDeriv m f (c * ξ)‖ := by
    intro ξ
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [show (fun ξ : ℝ => ENNReal.ofReal ‖(c : ℝ) ^ m • iteratedDeriv m f (c * ξ)‖)
      = fun ξ : ℝ => ENNReal.ofReal (c ^ m) * ENNReal.ofReal ‖iteratedDeriv m f (c * ξ)‖ from by
    funext ξ
    rw [hnorm ξ, ENNReal.ofReal_mul (by positivity)]]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas2.aemeasurable,
    lintegral_norm_comp_mul_left (iteratedDeriv m f)
      ((hf.continuous_iteratedDeriv m (by exact_mod_cast hm))).measurable hc]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [← Real.rpow_natCast c m, ← Real.rpow_neg_one c, ← Real.rpow_add hc]
  congr 1

/-! ## The mass of the derivatives of the cutoff `η` -/

theorem lintegral_kmtEta_deriv_le :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ (m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m Work.KMTContract.kmtEta ξ‖)
        ≤ ENNReal.ofReal Cη := by
  refine ⟨(∫ ξ : ℝ, ‖Work.KMTContract.kmtEta ξ‖)
      + (∫ ξ : ℝ, ‖iteratedDeriv 1 Work.KMTContract.kmtEta ξ‖)
      + (∫ ξ : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta ξ‖) + 1, by positivity, ?_⟩
  intro m hm
  have hInt : ∀ j : ℕ, j ≤ 2 →
      Integrable (fun ξ : ℝ => ‖iteratedDeriv j Work.KMTContract.kmtEta ξ‖) := by
    intro j hj
    interval_cases j
    · exact (integrable_kmtEta_varphiN).norm
    · have hcs : HasCompactSupport (fun ξ : ℝ => iteratedDeriv 1 Work.KMTContract.kmtEta ξ) := by
        rw [iteratedDeriv_one]
        exact (hasCompactSupport_kmtEta_varphiN).deriv
      have hcont : Continuous (fun ξ : ℝ => iteratedDeriv 1 Work.KMTContract.kmtEta ξ) := by
        rw [iteratedDeriv_one]
        exact (contDiff_kmtEta 2).continuous_deriv (by norm_num)
      exact (hcont.integrable_of_hasCompactSupport hcs).norm
    · exact integrable_iteratedDeriv_two_kmtEta_varphiN
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt m hm)
    (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖iteratedDeriv 1 Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  have h2 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  have h0 : (0:ℝ) ≤ ∫ ξ : ℝ, ‖Work.KMTContract.kmtEta ξ‖ :=
    integral_nonneg (fun x => norm_nonneg _)
  interval_cases m
  · rw [iteratedDeriv_zero]; linarith
  · linarith
  · linarith

/-! ## The mass of a difference of two dilations -/

theorem lintegral_deriv_dilation_sub_le (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {c₁ c₂ Cg : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hCg : 0 < Cg)
    (hgmass : ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) ≤ ENNReal.ofReal Cg) :
    ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ‖)
        ≤ ENNReal.ofReal ((c₁ ^ ((m : ℝ) - 1) + c₂ ^ ((m : ℝ) - 1)) * Cg) := by
  intro m hm
  have hm' : (m : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hm
  have h1 : ContDiff ℝ 2 (fun ξ : ℝ => g (c₁ * ξ)) := hg.comp (by fun_prop)
  have h2 : ContDiff ℝ 2 (fun ξ : ℝ => g (c₂ * ξ)) := hg.comp (by fun_prop)
  have hsub : ∀ ξ : ℝ, iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ
      = iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ
        - iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ := by
    intro ξ
    rw [show (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ))
        = (fun ξ : ℝ => g (c₁ * ξ)) - (fun ξ : ℝ => g (c₂ * ξ)) from rfl]
    exact iteratedDeriv_sub ((h1.of_le hm').contDiffAt) ((h2.of_le hm').contDiffAt)
  have hm1 : AEMeasurable
      (fun ξ : ℝ => ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖) volume :=
    (((h1.continuous_iteratedDeriv m (by exact_mod_cast hm)).norm).measurable.ennreal_ofReal).aemeasurable
  have hr1 : (0 : ℝ) ≤ c₁ ^ ((m : ℝ) - 1) := Real.rpow_nonneg (le_of_lt hc₁) _
  have hr2 : (0 : ℝ) ≤ c₂ ^ ((m : ℝ) - 1) := Real.rpow_nonneg (le_of_lt hc₂) _
  calc (∫⁻ ξ : ℝ, ENNReal.ofReal
          ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ) - g (c₂ * ξ)) ξ‖)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal
          ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ
            - iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖ := by
        refine lintegral_congr (fun ξ => ?_)
        rw [hsub ξ]
    _ ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖
            + ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) := by
        refine lintegral_mono (fun ξ => ?_)
        exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
    _ = ∫⁻ ξ : ℝ, (ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖
            + ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) := by
        refine lintegral_congr (fun ξ => ?_)
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    _ = (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₁ * ξ)) ξ‖)
          + (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c₂ * ξ)) ξ‖) :=
        MeasureTheory.lintegral_add_left' hm1 _
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1)) * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖)
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1))
            * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) := by
        rw [lintegral_norm_deriv_rescale g hg hc₁ m hm,
          lintegral_norm_deriv_rescale g hg hc₂ m hm]
    _ ≤ ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_right (hgmass m hm) _
        · exact mul_le_mul_right (hgmass m hm) _
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1) * Cg)
          + ENNReal.ofReal (c₂ ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_mul hr1, ENNReal.ofReal_mul hr2]
    _ = ENNReal.ofReal (c₁ ^ ((m : ℝ) - 1) * Cg + c₂ ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal ((c₁ ^ ((m : ℝ) - 1) + c₂ ^ ((m : ℝ) - 1)) * Cg) := by
        congr 1; ring

theorem lintegral_deriv_dilation_le (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) {c Cg : ℝ}
    (hc : 0 < c) (hCg : 0 < Cg)
    (hgmass : ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖) ≤ ENNReal.ofReal Cg) :
    ∀ m : ℕ, m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (fun ξ : ℝ => g (c * ξ)) ξ‖)
        ≤ ENNReal.ofReal (c ^ ((m : ℝ) - 1) * Cg) := by
  intro m hm
  rw [lintegral_norm_deriv_rescale g hg hc m hm]
  calc ENNReal.ofReal (c ^ ((m : ℝ) - 1)) * (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m g ξ‖)
      ≤ ENNReal.ofReal (c ^ ((m : ℝ) - 1)) * ENNReal.ofReal Cg :=
        mul_le_mul_right (hgmass m hm) _
    _ = ENNReal.ofReal (c ^ ((m : ℝ) - 1) * Cg) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hc) _)]

/-! ## The two bump masses -/

/-- `2^{m-1} ≤ 2` for `m ≤ 2`. -/
theorem rpow_sub_one_le_two {m : ℕ} (hm : m ≤ 2) :
    (2 : ℝ) ^ ((m : ℝ) - 1) ≤ 2 := by
  have h1 : ((m : ℝ) - 1) ≤ 1 := by
    have : (m : ℝ) ≤ 2 := by exact_mod_cast hm
    linarith
  calc (2 : ℝ) ^ ((m : ℝ) - 1) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 := Real.rpow_one 2

theorem varphiN_mass_deriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (N k m : ℕ), m ≤ 2 →
    (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphiN N k) ξ‖)
      ≤ ENNReal.ofReal (C * (thN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1)) := by
  obtain ⟨Cη, hCη, hη⟩ := lintegral_kmtEta_deriv_le
  refine ⟨3 * Cη, by positivity, ?_⟩
  intro N k m hm
  have hrpow : (2 : ℝ) ^ ((m : ℝ) - 1) ≤ 2 := rpow_sub_one_le_two hm
  by_cases hk : k = 0
  · subst hk
    have ha : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hEq : varphiN N 0
        = fun ξ : ℝ => Work.KMTContract.kmtEta (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ) := by
      funext ξ
      unfold varphiN
      rw [if_pos rfl]
    rw [hEq]
    have hmain := lintegral_deriv_dilation_le Work.KMTContract.kmtEta (contDiff_kmtEta 2) ha hCη hη m hm
    have hA : (0 : ℝ) ≤ ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ ((m : ℝ) - 1) :=
      Real.rpow_nonneg (by positivity) _
    have hstep : ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ ((m : ℝ) - 1) * Cη
        ≤ 3 * Cη * ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ ((m : ℝ) - 1) := by
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ ((m : ℝ) - 1) * Cη :=
        mul_nonneg hA (le_of_lt hCη)
      linarith [h0]
    have hfin : 3 * Cη * ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ ((m : ℝ) - 1)
        = 3 * Cη * (thN N / (2 : ℝ) ^ 0) ^ ((m : ℝ) - 1) := by
      rw [pow_zero, div_one]
      rfl
    exact hmain.trans ((ENNReal.ofReal_le_ofReal hstep).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq hfin)))
  · have ha : (0 : ℝ) < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hb : (0 : ℝ) < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hEq : varphiN N k = fun ξ : ℝ =>
        Work.KMTContract.kmtEta (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
          - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) := by
      funext ξ
      unfold varphiN
      rw [if_neg hk]
    rw [hEq]
    have hmain := lintegral_deriv_dilation_sub_le Work.KMTContract.kmtEta (contDiff_kmtEta 2)
      ha hb hCη hη m hm
    have hc1 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) = thN N / (2 : ℝ) ^ k := by
      rw [thN, ← Real.rpow_natCast (2 : ℝ) k, Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    have hc2 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
        = 2 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    have hAr : (0 : ℝ) ≤ ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) :=
      Real.rpow_nonneg (by positivity) _
    have hBr : ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) ^ ((m : ℝ) - 1)
        = (2 : ℝ) ^ ((m : ℝ) - 1)
          * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) := by
      rw [hc2, Real.mul_rpow (by norm_num) (by positivity)]
    have hstep : (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1)
          + ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) ^ ((m : ℝ) - 1)) * Cη
        ≤ 3 * Cη * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) := by
      rw [hBr]
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) * Cη :=
        mul_nonneg hAr (le_of_lt hCη)
      have h1 : (2 : ℝ) ^ ((m : ℝ) - 1)
            * (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) * Cη)
          ≤ 2 * (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1) * Cη) :=
        mul_le_mul_of_nonneg_right hrpow h0
      linarith [h1]
    have hfin : 3 * Cη * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) ^ ((m : ℝ) - 1)
        = 3 * Cη * (thN N / (2 : ℝ) ^ k) ^ ((m : ℝ) - 1) := by
      rw [hc1]
    exact hmain.trans ((ENNReal.ofReal_le_ofReal hstep).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq hfin)))

theorem varphitildeN_mass_deriv_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k m : ℕ), m ≤ 2 →
      (∫⁻ ξ : ℝ, ENNReal.ofReal ‖iteratedDeriv m (varphitildeN d N k) ξ‖)
        ≤ ENNReal.ofReal
          (C * ((((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (d * k))
            ^ ((m : ℝ) - 1)) := by
  obtain ⟨Cη, hCη, hη⟩ := lintegral_kmtEta_deriv_le
  refine ⟨(1 + (2 : ℝ) ^ d) * Cη, by positivity, ?_⟩
  intro N k m hm
  have h1d : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hdR : ((2 : ℝ) ^ d) = (2 : ℝ) ^ (((d : ℕ) : ℝ)) := (Real.rpow_natCast (2 : ℝ) d).symm
  have hm1 : ((m : ℝ) - 1) ≤ 1 := by
    have : (m : ℝ) ≤ 2 := by exact_mod_cast hm
    linarith
  have h2dm : ((2 : ℝ) ^ d) ^ ((m : ℝ) - 1) ≤ (2 : ℝ) ^ d := by
    calc ((2 : ℝ) ^ d) ^ ((m : ℝ) - 1)
        = ((2 : ℝ) ^ (((d : ℕ) : ℝ))) ^ ((m : ℝ) - 1) := by rw [hdR]
      _ = (2 : ℝ) ^ (((d : ℕ) : ℝ) * ((m : ℝ) - 1)) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
      _ ≤ (2 : ℝ) ^ (((d : ℕ) : ℝ) * 1) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith [hdnn, hm1]
      _ = (2 : ℝ) ^ d := by rw [mul_one, Real.rpow_natCast]
  by_cases hk : k = 0
  · subst hk
    have ha : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hEq : varphitildeN d N 0 = fun ξ : ℝ =>
        Work.KMTContract.kmtEta (((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) * ξ) := by
      funext ξ
      unfold varphitildeN
      rw [if_pos rfl]
    rw [hEq]
    have hmain := lintegral_deriv_dilation_le Work.KMTContract.kmtEta (contDiff_kmtEta 2) ha hCη hη m hm
    have hA : (0 : ℝ) ≤ ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1) :=
      Real.rpow_nonneg (by positivity) _
    have hstep : ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1) * Cη
        ≤ (1 + (2 : ℝ) ^ d) * Cη
          * ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1) := by
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1) * Cη :=
        mul_nonneg hA (le_of_lt hCη)
      have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ d * (((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1) * Cη) :=
        mul_nonneg (by positivity) h0
      linarith [h0, h1]
    have hbase : (((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (d * 0)
        = (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) := by
      rw [Nat.mul_zero, pow_zero, div_one]
      calc ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
          = ((2 : ℝ) ^ (((d : ℕ) : ℝ))) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by rw [hdR]
        _ = (2 : ℝ) ^ (((d : ℕ) : ℝ) * ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    have hfin : (1 + (2 : ℝ) ^ d) * Cη
          * ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) ^ ((m : ℝ) - 1)
        = (1 + (2 : ℝ) ^ d) * Cη
          * ((((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (d * 0))
            ^ ((m : ℝ) - 1) := by
      rw [hbase]
    exact hmain.trans ((ENNReal.ofReal_le_ofReal hstep).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq hfin)))
  · have ha : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hb : (0 : ℝ) <
        (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hEq : varphitildeN d N k = fun ξ : ℝ =>
        Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) * ξ)
          - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) * ξ) := by
      funext ξ
      unfold varphitildeN
      rw [if_neg hk]
    rw [hEq]
    have hmain := lintegral_deriv_dilation_sub_le Work.KMTContract.kmtEta (contDiff_kmtEta 2)
      ha hb hCη hη m hm
    have hc2 : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
        = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := by
      rw [show (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
          = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + (d : ℝ) from by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      ring
    have hAr : (0 : ℝ) ≤
        ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) :=
      Real.rpow_nonneg (by positivity) _
    have hBr : ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)))
          ^ ((m : ℝ) - 1)
        = ((2 : ℝ) ^ d) ^ ((m : ℝ) - 1)
          * ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) := by
      rw [hc2, Real.mul_rpow (by positivity) (by positivity)]
    have hstep : (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1)
          + ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) ^ ((m : ℝ) - 1))
          * Cη
        ≤ (1 + (2 : ℝ) ^ d) * Cη
          * ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) := by
      rw [hBr]
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) * Cη :=
        mul_nonneg hAr (le_of_lt hCη)
      have h1 : ((2 : ℝ) ^ d) ^ ((m : ℝ) - 1)
            * (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) * Cη)
          ≤ (2 : ℝ) ^ d
            * (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1) * Cη) :=
        mul_le_mul_of_nonneg_right h2dm h0
      linarith [h1]
    have hbase : (((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (d * k)
        = (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := by
      have h1 : ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
          = (2 : ℝ) ^ (((d : ℕ) : ℝ) * ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by
        rw [hdR, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : (2 : ℝ) ^ (d * k) = (2 : ℝ) ^ (((d : ℕ) : ℝ) * ((k : ℕ) : ℝ)) := by
        calc (2 : ℝ) ^ (d * k) = (2 : ℝ) ^ (((d * k : ℕ)) : ℝ) := (Real.rpow_natCast (2 : ℝ) (d * k)).symm
          _ = (2 : ℝ) ^ (((d : ℕ) : ℝ) * ((k : ℕ) : ℝ)) := by
              congr 1
              push_cast
              ring
      rw [h1, h2, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    have hfin : (1 + (2 : ℝ) ^ d) * Cη
          * ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) ^ ((m : ℝ) - 1)
        = (1 + (2 : ℝ) ^ d) * Cη
          * ((((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) / (2 : ℝ) ^ (d * k))
            ^ ((m : ℝ) - 1) := by
      rw [hbase]
    exact hmain.trans ((ENNReal.ofReal_le_ofReal hstep).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq hfin)))

end

end Work.KMTPlan.A6
