import Mathlib
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Commons.Analysis.Lp.eLpNorm_pairing_le
import Submission.Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
import Submission.Work.Analysis.Fourier.band_projection_schwartz_lp
import Submission.Work.BourgainPlan.Maximal.interval_projection_schwartz_lp
import Submission.Work.BourgainPlan.Maximal.interval_projection_memLp
import Submission.Work.BourgainPlan.Maximal.plancherel_fourier_inner
import Submission.Work.BourgainPlan.Maximal.truncated_pairing_identity
import Submission.Work.BourgainPlan.Maximal.truncated_mikhlin_of_schwartz

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology
open Work.Analysis.Fourier
open Commons.Analysis.CalderonZygmund

noncomputable section

set_option maxHeartbeats 1000000

/-- `‖czE x ξ‖ = 1`. -/
private lemma norm_czE (x ξ : ℝ) : ‖czE x ξ‖ = 1 := by
  rw [czE, Complex.norm_exp]
  simp

/-- Converse of the `Lᵖ`-to-lintegral conversion: an integral bound gives an `eLpNorm` bound. -/
private lemma eLpNorm_le_of_lintegral_le {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) {f g : ℝ → ℂ}
    (h : ∫⁻ x : ℝ, ‖f x‖ₑ ^ r ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ r)
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume) :
    eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) (volume : Measure ℝ) := by
  have hrne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf : eLpNorm f (ENNReal.ofReal r) (volume : Measure ℝ)
      = (∫⁻ x : ℝ, ‖f x‖ₑ ^ r) ^ (1/r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrne hrtop hfm, ENNReal.toReal_ofReal hr.le]
  have hg : eLpNorm g (ENNReal.ofReal r) (volume : Measure ℝ)
      = (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hrne hrtop hgm, ENNReal.toReal_ofReal hr.le]
  have hCr : (C ^ r) ^ (1/r) = C := by
    rw [← Real.rpow_mul hC r (1/r), mul_one_div, div_self hr.ne', Real.rpow_one]
  rw [hf, hg]
  calc (∫⁻ x : ℝ, ‖f x‖ₑ ^ r) ^ (1/r)
      ≤ (ENNReal.ofReal (C ^ r) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal C * (∫⁻ x : ℝ, ‖g x‖ₑ ^ r) ^ (1/r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/r),
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC r) (by positivity : (0:ℝ) ≤ 1/r),
          hCr]

/-- The interval-truncated Fourier transform of an integrable function is integrable. -/
private lemma integrable_indicator_Ioo_mul_fourier {g : ℝ → ℂ} (hg : Integrable g) (a b : ℝ) :
    Integrable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1 : ℂ) else 0) *
      FourierTransform.fourier g ξ) (volume : Measure ℝ) := by
  have hFgbd : ∀ ξ : ℝ, ‖FourierTransform.fourier g ξ‖ ≤ ∫ x : ℝ, ‖g x‖ :=
    fun ξ => Commons.Analysis.CalderonZygmund.norm_fourier_le g ξ
  have hdom : Integrable (fun ξ : ℝ => (Set.Icc a b).indicator (fun _ : ℝ => (∫ x : ℝ, ‖g x‖)) ξ)
      (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  refine hdom.mono' ?_ ?_
  · exact ((Measurable.ite measurableSet_Ioo measurable_const measurable_const).mul
      (Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable hg).measurable).aestronglyMeasurable
  · filter_upwards with ξ
    by_cases hξ : ξ ∈ Set.Ioo a b
    · rw [if_pos hξ, Set.indicator_of_mem (Set.Ioo_subset_Icc_self hξ)]
      simpa using hFgbd ξ
    · rw [if_neg hξ]
      simp only [zero_mul, norm_zero]
      by_cases h2 : ξ ∈ Set.Icc a b
      · rw [Set.indicator_of_mem h2]
        exact integral_nonneg (fun y => norm_nonneg (g y))
      · rw [Set.indicator_of_notMem h2]

/-- The Mikhlin-truncated symbol times the Fourier transform of a Schwartz function is integrable. -/
private lemma integrable_mul_fourier_of_bound {G : SchwartzMap ℝ ℂ} {m : ℝ → ℂ} {A : ℝ}
    (hA : 0 ≤ A) (h0 : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (hmm : AEStronglyMeasurable m (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ)
      (volume : Measure ℝ) := by
  refine ((integrable_schwartz_fourier G).norm.const_mul A).mono' ?_ ?_
  · exact hmm.mul (Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable
      (SchwartzMap.integrable G)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h0 ξ) (norm_nonneg _)

/-- **The `Schwartz`-level truncated Mikhlin bound**, assembled from the Mikhlin theorem
(`hC1`), the uniform interval-projection bound (`hC2`) and the pairing identity (`hpair_id`).

The proof follows the pattern "truncated multiplier = Mikhlin multiplier ∘ interval projection"
at the level of the pairing: for a Schwartz `G` and an `L¹ ∩ L^{p'}` test function `g`,
`hpair_id` rewrites the pairing `⟨T_Φ G, g⟩` as the (conjugated) pairing of the two individual
multipliers, and Hölder (`eLpNorm_pairing_le`) together with the two bounds finishes. -/
theorem truncated_mikhlin_schwartz_aux (p : ℝ) (hp : 1 < p) {C1 C2 : ℝ}
    (hC1pos : 0 < C1) (hC2pos : 0 < C2)
    (hC1 : ∀ (m : ℝ → ℂ) (A : ℝ), 0 ≤ A → ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A) → (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) →
      ∀ G : SchwartzMap ℝ ℂ,
        eLpNorm (fun x : ℝ => ∫ ξ : ℝ,
            (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))) •
              FourierTransform.fourier (G : ℝ → ℂ) ξ)
          (ENNReal.ofReal p) (volume : Measure ℝ)
          ≤ ENNReal.ofReal (C1 * A) * eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ))
    (hC2 : ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℂ), Integrable f →
      MemLp f (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) →
      ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1 : ℂ) else 0) *
            FourierTransform.fourier f ξ) x‖ₑ ^ (p / (p - 1))
        ≤ ENNReal.ofReal (C2 ^ (p / (p - 1))) *
            ∫⁻ x : ℝ, ‖f x‖ₑ ^ (p / (p - 1)))
    (hpair_id : ∀ (m : ℝ → ℂ) (A : ℝ), 0 ≤ A → (∀ ξ : ℝ, ‖m ξ‖ ≤ A) →
      AEStronglyMeasurable m (volume : Measure ℝ) → ∀ {a b : ℝ}, a < b →
      ∀ (G : SchwartzMap ℝ ℂ) (g : ℝ → ℂ), Integrable g →
      (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (g x))
        = star (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1 : ℂ) else 0) *
              FourierTransform.fourier g ξ) x) (FourierTransformInv.fourierInv
            (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)))
    (m : ℝ → ℂ) (A a b : ℝ) (hA : 0 ≤ A) (hab : a < b) (hcd : ContDiff ℝ 2 m)
    (h0 : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (h1 : ∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A)
    (h2 : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) (G : SchwartzMap ℝ ℂ) :
    ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
          FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p
      ≤ ENNReal.ofReal ((C1 * C2 * A) ^ p) *
        ∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    have hm0 : m = 0 := funext fun ξ => norm_le_zero_iff.mp (by simpa using h0 ξ)
    have hz : ∀ x : ℝ, FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
          FourierTransform.fourier (G : ℝ → ℂ) ξ) x = 0 := by
      intro x
      rw [fourierInv_czE]
      have hsym0 : ∀ ξ : ℝ, (if ξ ∈ Set.Ioo a b then m ξ else 0) = 0 := by
        intro ξ
        rw [hm0]
        simp
      simp only [hsym0, zero_mul, smul_zero, MeasureTheory.integral_zero]
    have hfun : (fun x : ℝ => ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p)
        = fun x : ℝ => ‖(0 : ℂ)‖ₑ ^ p := by
      funext x
      show ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p = ‖(0 : ℂ)‖ₑ ^ p
      rw [hz x]
    rw [hfun]
    simp [ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp),
      Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hp))]
  · have hmm : AEStronglyMeasurable m (volume : Measure ℝ) := hcd.continuous.aestronglyMeasurable
    have hp' : 1 < p / (p - 1) := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < p - 1)]
      linarith
    have hpq : 1 / (p / (p - 1)) + 1 / p = 1 := by
      field_simp
      ring
    have hFGcont : Continuous (fun ξ : ℝ => FourierTransform.fourier (G : ℝ → ℂ) ξ) :=
      Commons.Analysis.CalderonZygmund.continuous_fourier_of_integrable (SchwartzMap.integrable G)
    have hbdΦG : ∀ ξ : ℝ, ‖(if ξ ∈ Set.Ioo a b then m ξ else 0) *
        FourierTransform.fourier (G : ℝ → ℂ) ξ‖
        ≤ A * ‖FourierTransform.fourier (G : ℝ → ℂ) ξ‖ := by
      intro ξ
      rw [norm_mul]
      by_cases hξ : ξ ∈ Set.Ioo a b
      · rw [if_pos hξ]
        exact mul_le_mul_of_nonneg_right (h0 ξ) (norm_nonneg _)
      · rw [if_neg hξ, norm_zero, zero_mul]
        exact mul_nonneg hA (norm_nonneg _)
    have hΦmeas : Measurable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0)) :=
      Measurable.ite measurableSet_Ioo hcd.continuous.measurable measurable_const
    have hΦGint : Integrable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
        FourierTransform.fourier (G : ℝ → ℂ) ξ) (volume : Measure ℝ) :=
      ((integrable_schwartz_fourier G).norm.const_mul A).mono'
        ((hΦmeas.mul hFGcont.measurable).aestronglyMeasurable)
        (Filter.Eventually.of_forall hbdΦG)
    by_cases hGz : eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ) = 0
    · have hGae : (G : ℝ → ℂ) =ᵐ[volume] 0 :=
        (MeasureTheory.eLpNorm_eq_zero_iff
          (ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hp))).mp hGz
      have hFG0 : FourierTransform.fourier (G : ℝ → ℂ) = 0 := by
        funext ξ
        show FourierTransform.fourier (G : ℝ → ℂ) ξ = (0 : ℂ)
        rw [Real.fourier_eq']
        refine MeasureTheory.integral_eq_zero_of_ae ?_
        filter_upwards [hGae] with x hx
        rw [hx]; simp
      have hsym : (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
          FourierTransform.fourier (G : ℝ → ℂ) ξ) = fun _ : ℝ => 0 := by
        funext ξ; rw [hFG0]; simp
      have hh0 : ∀ x : ℝ, FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x = 0 := by
        intro x
        rw [hsym, fourierInv_czE]
        simp
      have hfun : (fun x : ℝ => ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
              FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p)
          = fun x : ℝ => ‖(0 : ℂ)‖ₑ ^ p := by
        funext x
        show ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
              FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p = ‖(0 : ℂ)‖ₑ ^ p
        rw [hh0 x]
      rw [hfun]
      simp [ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp)]
    · have hEne : ENNReal.ofReal (C1 * C2 * A) *
          eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ) ≠ 0 := by
        intro h
        rcases mul_eq_zero.mp h with h1 | h1
        · rw [ENNReal.ofReal_eq_zero] at h1
          exact absurd h1 (not_le.mpr (mul_pos (mul_pos hC1pos hC2pos) hApos))
        · exact hGz h1
      have key : eLpNorm (fun x : ℝ => FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
            (ENNReal.ofReal p) (volume : Measure ℝ)
          ≤ ENNReal.ofReal (C1 * C2 * A) *
            eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ) := by
        refine Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
          (fun x : ℝ => FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
              FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
          hp ?_ ?_
          (ENNReal.ofReal (C1 * C2 * A) *
            eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)) ?_ ?_
        · exact (fourierInv_continuous_of_integrable hΦGint).aestronglyMeasurable
        · exact ⟨∫ ξ : ℝ, ‖(if ξ ∈ Set.Ioo a b then m ξ else 0) *
              FourierTransform.fourier (G : ℝ → ℂ) ξ‖, fun x => by
            rw [fourierInv_czE]
            refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
            apply MeasureTheory.integral_congr_ae
            filter_upwards with ξ
            rw [norm_smul, norm_czE, one_mul]⟩
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ne_of_lt (SchwartzMap.memLp G (ENNReal.ofReal p) (volume : Measure ℝ)).eLpNorm_lt_top)
        · intro g hg
          by_cases htop : eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) = ⊤
          · rw [htop, ENNReal.mul_top hEne]
            exact le_top
          · have hgm : MemLp g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) :=
              lt_top_iff_ne_top.mpr htop
            rw [hpair_id m A hA h0 hmm hab G g hg]
            set U : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
                (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1 : ℂ) else 0) *
                  FourierTransform.fourier g ξ) x with hU
            set V : ℝ → ℂ := fun x => FourierTransformInv.fourierInv
                (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x with hV
            rw [show enorm (star (∫ x : ℝ, inner ℂ (U x) (V x)))
                = enorm (∫ x : ℝ, inner ℂ (U x) (V x)) from by simp]
            have hle := Commons.Analysis.Lp.eLpNorm_pairing_le (u := U) (v := V) hp' hp hpq
              (by
                rw [hU]
                exact (fourierInv_continuous_of_integrable
                  (integrable_indicator_Ioo_mul_fourier hg a b)).aestronglyMeasurable)
              (by
                rw [hV]
                exact (fourierInv_continuous_of_integrable
                  (integrable_mul_fourier_of_bound hA h0 hmm (G := G))).aestronglyMeasurable)
            refine hle.trans ?_
            have hu_bd : eLpNorm U (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ)
                ≤ ENNReal.ofReal C2 *
                  eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) :=
              eLpNorm_le_of_lintegral_le (lt_trans zero_lt_one hp') hC2pos.le (hC2 a b hab g hg hgm)
                (by
                  rw [hU]
                  exact (fourierInv_continuous_of_integrable
                    (integrable_indicator_Ioo_mul_fourier hg a b)).aestronglyMeasurable)
                hgm.aestronglyMeasurable
            have hv_bd : eLpNorm V (ENNReal.ofReal p) (volume : Measure ℝ)
                ≤ ENNReal.ofReal (C1 * A) *
                  eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ) := by
              refine le_of_eq_of_le ?_ (hC1 m A hA hcd h0 h1 h2 G)
              have hVm : AEStronglyMeasurable V volume := by
                rw [hV]
                exact (fourierInv_continuous_of_integrable
                  (integrable_mul_fourier_of_bound hA h0 hmm (G := G))).aestronglyMeasurable
              have hWm : AEStronglyMeasurable (fun x : ℝ => ∫ ξ : ℝ,
                  (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))) •
                  FourierTransform.fourier (G : ℝ → ℂ) ξ) volume := by
                refine hVm.congr (Filter.Eventually.of_forall fun x => ?_)
                rw [hV]
                simp only []
                rw [fourierInv_czE]
                apply MeasureTheory.integral_congr_ae
                filter_upwards with ξ
                simp only [czE, smul_eq_mul]
                ring
              refine MeasureTheory.eLpNorm_congr_norm_ae hVm hWm ?_
              filter_upwards with x
              show ‖FourierTransformInv.fourierInv
                  (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ =
                ‖∫ ξ : ℝ, (m ξ * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))) •
                  FourierTransform.fourier (G : ℝ → ℂ) ξ‖
              rw [fourierInv_czE]
              congr 1
              apply MeasureTheory.integral_congr_ae
              filter_upwards with ξ
              simp only [czE, smul_eq_mul]
              ring
            have hXY : eLpNorm U (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) *
                eLpNorm V (ENNReal.ofReal p) (volume : Measure ℝ)
                ≤ (ENNReal.ofReal C2 * eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ)) *
                  (ENNReal.ofReal (C1 * A) *
                    eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)) :=
              mul_le_mul hu_bd hv_bd bot_le bot_le
            refine hXY.trans (le_of_eq ?_)
            have hc : ENNReal.ofReal C2 * ENNReal.ofReal (C1 * A)
                = ENNReal.ofReal (C1 * C2 * A) := by
              rw [← ENNReal.ofReal_mul hC2pos.le]
              congr 1
              ring
            calc (ENNReal.ofReal C2 * eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ)) *
                  (ENNReal.ofReal (C1 * A) *
                    eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ))
                = (ENNReal.ofReal C2 * ENNReal.ofReal (C1 * A)) *
                  (eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) *
                    eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)) := by ring
              _ = ENNReal.ofReal (C1 * C2 * A) *
                  (eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) *
                    eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)) := by rw [hc]
              _ = (ENNReal.ofReal (C1 * C2 * A) *
                    eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)) *
                  eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume : Measure ℝ) := by ring
      exact eLpNorm_to_lintegral_local (r := p) (C := C1 * C2 * A)
        (f := fun x : ℝ => FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier (G : ℝ → ℂ) ξ) x)
        (g := (G : ℝ → ℂ)) (lt_trans zero_lt_one hp) (by positivity) key
        G.continuous.aestronglyMeasurable

theorem truncated_mikhlin_multiplier (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (A a b : ℝ), 0 ≤ A → a < b →
      ContDiff ℝ 2 m → (∀ ξ : ℝ, ‖m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| * ‖deriv m ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 m ξ‖ ≤ A) →
      ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0)
              * FourierTransform.fourier g ξ) x‖ₑ ^ p ∂MeasureTheory.volume
          ≤ ENNReal.ofReal ((C * A) ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume := by
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  have hp1 : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < p - 1)]
    linarith
  obtain ⟨C2, hC2pos, hC2⟩ := interval_projection_memLp (p / (p - 1)) hp1
  refine ⟨C1 * C2, by positivity, ?_⟩
  intro m A a b hA hab hcd h0 h1 h2 g hg
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · subst hA0
    have hm0 : m = 0 := funext fun ξ => norm_le_zero_iff.mp (by simpa using h0 ξ)
    have hz : ∀ x : ℝ, FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
          FourierTransform.fourier g ξ) x = 0 := by
      intro x
      rw [fourierInv_czE]
      have hsym0 : ∀ ξ : ℝ, (if ξ ∈ Set.Ioo a b then m ξ else 0) = 0 := by
        intro ξ
        rw [hm0]
        simp
      simp only [hsym0, zero_mul, smul_zero, MeasureTheory.integral_zero]
    have hfun : (fun x : ℝ => ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier g ξ) x‖ₑ ^ p)
        = fun x : ℝ => ‖(0 : ℂ)‖ₑ ^ p := by
      funext x
      show ‖FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
            FourierTransform.fourier g ξ) x‖ₑ ^ p = ‖(0 : ℂ)‖ₑ ^ p
      rw [hz x]
    rw [hfun]
    simp [ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hp),
      Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hp))]
  · have hΦmeas : AEStronglyMeasurable (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0))
        (volume : Measure ℝ) :=
      (Measurable.ite measurableSet_Ioo hcd.continuous.measurable measurable_const).aestronglyMeasurable
    have hΦbd : ∀ ξ : ℝ, ‖(if ξ ∈ Set.Ioo a b then m ξ else 0)‖ ≤ A := by
      intro ξ
      by_cases hξ : ξ ∈ Set.Ioo a b
      · rw [if_pos hξ]; exact h0 ξ
      · rw [if_neg hξ, norm_zero]; exact hA
    have hΦsupp : ∀ ξ : ℝ, max |a| |b| < |ξ| → (if ξ ∈ Set.Ioo a b then m ξ else 0) = 0 := by
      intro ξ hξ
      rw [if_neg]
      intro hmem
      have habs : |ξ| ≤ max |a| |b| := by
        rw [abs_le]
        constructor
        · have h3 : -max |a| |b| ≤ a := by
            have h4 := neg_le_neg (le_max_left |a| |b|)
            have h5 := neg_abs_le a
            linarith
          linarith [hmem.1]
        · have h3 : b ≤ max |a| |b| := le_trans (le_abs_self b) (le_max_right |a| |b|)
          linarith [hmem.2]
      exact absurd hξ (not_lt.mpr habs)
    have hsch : ∀ G : SchwartzMap ℝ ℂ,
        ∫⁻ x : ℝ, ‖FourierTransformInv.fourierInv
            (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) *
              FourierTransform.fourier (G : ℝ → ℂ) ξ) x‖ₑ ^ p
          ≤ ENNReal.ofReal ((C1 * C2 * A) ^ p) * ∫⁻ x : ℝ, ‖(G : ℝ → ℂ) x‖ₑ ^ p :=
      fun G => truncated_mikhlin_schwartz_aux (p := p) (C1 := C1) (C2 := C2) hp hC1pos hC2pos
        hC1 hC2 (fun m A hA h0 hmm {a b} hab G g hg =>
          truncated_pairing_identity hA h0 hmm hab G g hg)
        m A a b hA hab hcd h0 h1 h2 G
    exact truncated_mikhlin_of_schwartz (p := p) hp
      (Φ := fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0))
      (A := A) (E := C1 * C2 * A) (R := max |a| |b|) hA (by positivity)
      (le_trans (abs_nonneg a) (le_max_left |a| |b|)) hΦbd hΦsupp hΦmeas hsch g hg

end

end Work.BourgainPlan.Maximal
