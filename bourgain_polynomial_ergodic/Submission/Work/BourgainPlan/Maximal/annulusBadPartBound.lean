import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusKernel_translation
import Submission.Work.BourgainPlan.Maximal.annulusKernel_size
import Submission.Work.BourgainPlan.Maximal.lintegral_outer_rpow
import Submission.Work.BourgainPlan.Maximal.annulusKernel_translation_uniform
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq

/-!
# The Calderón--Zygmund bad-part bound for the annulus square function

Proof of `AnnulusBadPartBound b` (step 4 of piece (ii-e) of
`WINDOW_WEAK_TYPE_STATUS_S10.md` §10) from the sharp translation estimate
`annulusKernel_translation_uniform` and the elementary outer radial integral
`lintegral_outer_rpow`.

The three ingredients are

* (Minkowski) `sqrt_tsum_lintegral_sq_le`: `(∑_n (∫⁻ f_n)²)^{1/2} ≤ ∫⁻ (∑_n f_n²)^{1/2}`,
  proved from `minkowski_lintegral_sum` by exhausting the `ℤ`-sum along finite subsets;
* (shifted outer integral) `lintegral_outer_rpow_shift`: the `s`-independent bound
  `∫⁻_{|x-c| > 2s} ofReal (s^{b-1}|x-c|^{-b}) ≤ ofReal C` for `b > 1`, obtained from
  `lintegral_outer_rpow` by translation invariance;
* the mean-zero identity for the convolution: since `h` has vanishing integral, the
  difference of the kernel at the pivot replaces the kernel itself.
-/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-! ## 0. The annulus kernels are continuous -/

lemma continuous_fourierInv_of_integrable {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (FourierTransform.fourierInv f) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner hf.comp_neg

lemma continuous_annulusK (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    Continuous (annulusK b m) := by
  have hbint : Integrable (b m) volume := by
    simpa only [iteratedDeriv_zero] using annulusK_integrable b hb hsmooth m 0
  simpa only [annulusK] using continuous_fourierInv_of_integrable hbint

/-! ## 1. Minkowski's inequality for the `ℝ≥0∞`-valued ℓ²-integral -/

theorem sqrt_tsum_lintegral_sq_le (f : ℤ → ℝ → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) volume) :
    (∑' n : ℤ, (∫⁻ y, f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ∫⁻ y, (∑' n : ℤ, (f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hL : (∑' n : ℤ, (∫⁻ y, f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = ⨆ T : Finset ℤ, (∑ n ∈ T, (∫⁻ y, f n y) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact Commons.Analysis.MeasureTheory.iSup_rpow_eq (by norm_num) _
  rw [hL]
  refine iSup_le fun T => ?_
  refine (Commons.Analysis.MeasureTheory.minkowski_lintegral_sum (μ := volume) T
    (fun n y => f n y) 2 (by norm_num) (fun n => hf n)).trans ?_
  exact lintegral_mono fun y => ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum T) (by norm_num)

/-- `(b ^ 2)^{1/2} = b` in `ℝ≥0∞`. -/
lemma rpow_two_half (b : ℝ≥0∞) : (b ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = b := by
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num, ENNReal.rpow_one]

lemma sqrt_tsum_mul_sq (A : ℤ → ℝ≥0∞) (b : ℝ≥0∞) :
    (∑' n : ℤ, (A n * b) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = (∑' n : ℤ, (A n) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * b := by
  have h1 : (∑' n : ℤ, (A n * b) ^ (2 : ℝ))
      = (∑' n : ℤ, (A n) ^ (2 : ℝ)) * b ^ (2 : ℝ) := by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun n => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), rpow_two_half]

/-! ## 2. The shifted outer radial integral -/

theorem lintegral_outer_rpow_shift (b : ℝ) (hb : 1 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s c : ℝ, 0 < s →
      ∫⁻ x in {x : ℝ | 2 * s < |x - c|},
          ENNReal.ofReal (s ^ (b - 1) * |x - c| ^ (-b)) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbnd⟩ := lintegral_outer_rpow b hb
  refine ⟨C, hC, fun s c hs => ?_⟩
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (s ^ (b - 1) * |t| ^ (-b)) with hF
  have hmeasR : MeasurableSet {x : ℝ | 2 * s < |x - c|} :=
    measurableSet_lt measurable_const (measurable_id.sub measurable_const).abs
  have hmeasR' : MeasurableSet {t : ℝ | 2 * s < |t|} :=
    measurableSet_lt measurable_const measurable_id.abs
  have hmain : ∫⁻ x in {x : ℝ | 2 * s < |x - c|}, F (x - c)
      = ∫⁻ t in {t : ℝ | 2 * s < |t|}, F t := by
    rw [← lintegral_indicator hmeasR (fun x => F (x - c))]
    rw [← lintegral_add_right_eq_self
      (({x : ℝ | 2 * s < |x - c|}).indicator (fun x => F (x - c))) c]
    have hcongr : ∫⁻ t, ({x : ℝ | 2 * s < |x - c|}).indicator (fun x => F (x - c)) (t + c)
        = ∫⁻ t in {t : ℝ | 2 * s < |t|}, F t := by
      rw [← lintegral_indicator hmeasR' F]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ {t : ℝ | 2 * s < |t|}
      · have ht2 : t + c ∈ {x : ℝ | 2 * s < |x - c|} := by
          simp only [Set.mem_ofPred_eq] at ht ⊢
          rwa [show t + c - c = t by ring]
        rw [Set.indicator_of_mem ht2, Set.indicator_of_mem ht]
        simp only [hF]
        congr 1
        rw [show t + c - c = t by ring]
      · have ht2 : t + c ∉ {x : ℝ | 2 * s < |x - c|} := by
          simp only [Set.mem_ofPred_eq] at ht ⊢
          rwa [show t + c - c = t by ring]
        rw [Set.indicator_of_notMem ht2, Set.indicator_of_notMem ht]
    rw [hcongr]
  rw [hmain]
  exact hbnd s hs

/-! ## 3. The dyadic cell endpoint bound -/

lemma abs_sub_mul_zpow_le_of_mem_dyCell {n k : ℤ} {y : ℝ} (hy : y ∈ dyCell n k) :
    |y - (k : ℝ) * (2 : ℝ) ^ n| ≤ (2 : ℝ) ^ n := by
  simp only [dyCell, Set.mem_Ico] at hy
  obtain ⟨h1, h2⟩ := hy
  have h3 : ((k : ℝ) + 1) * (2 : ℝ) ^ n = (k : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n := by ring
  rw [h3] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ## 4. The mean-zero identity for the convolution -/

lemma annulusConv_pivot_diff (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (m : ℤ) (h : ℝ → ℂ) (hh : Integrable h volume) (hzero : ∫ y, h y = 0) (x c : ℝ) :
    annulusConv b m h x = ∫ y, (annulusK b m (x - y) - annulusK b m (x - c)) * h y := by
  obtain ⟨C, hCpos, hCbnd⟩ := annulusKernel_size b hb hsmooth 0
  have hKbdd : ∀ z : ℝ, ‖annulusK b m z‖ ≤ C * (2 : ℝ) ^ (-m) := by
    intro z
    have h := hCbnd m z
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h
    simpa only [annulusK] using h
  have hcont : Continuous (fun y : ℝ => annulusK b m (x - y) - annulusK b m (x - c)) :=
    ((continuous_annulusK b hb hsmooth m).comp (continuous_const.sub continuous_id)).sub
      continuous_const
  have hbdd : ∀ᵐ y ∂volume, ‖annulusK b m (x - y) - annulusK b m (x - c)‖
      ≤ 2 * (C * (2 : ℝ) ^ (-m)) := by
    filter_upwards with y
    calc ‖annulusK b m (x - y) - annulusK b m (x - c)‖
        ≤ ‖annulusK b m (x - y)‖ + ‖annulusK b m (x - c)‖ := norm_sub_le _ _
      _ ≤ C * (2 : ℝ) ^ (-m) + C * (2 : ℝ) ^ (-m) := add_le_add (hKbdd _) (hKbdd _)
      _ = 2 * (C * (2 : ℝ) ^ (-m)) := by ring
  have hint1 : Integrable (fun y : ℝ => (annulusK b m (x - y) - annulusK b m (x - c)) * h y) :=
    hh.bdd_mul hcont.aestronglyMeasurable hbdd
  have hint2 : Integrable (fun y : ℝ => annulusK b m (x - c) * h y) := hh.const_mul _
  have hsplit : ∀ y : ℝ, annulusK b m (x - y) * h y
      = (annulusK b m (x - y) - annulusK b m (x - c)) * h y + annulusK b m (x - c) * h y := by
    intro y; ring
  have h1 : ∫ y, annulusK b m (x - y) * h y
      = ∫ y, ((annulusK b m (x - y) - annulusK b m (x - c)) * h y
          + annulusK b m (x - c) * h y) :=
    integral_congr_ae (Eventually.of_forall hsplit)
  show (∫ y, annulusK b m (x - y) * h y)
      = ∫ y, (annulusK b m (x - y) - annulusK b m (x - c)) * h y
  rw [h1, integral_add hint1 hint2, integral_const_mul, hzero, mul_zero, add_zero]

/-! ## 5. The bad-part bound -/

theorem annulusBadPartBound (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) :
    Work.BourgainPlan.Maximal.AnnulusBadPartBound b := by
  obtain ⟨C₁, hC₁, htrans⟩ := annulusKernel_translation_uniform b hb hsmooth
  obtain ⟨C₂, hC₂, houter⟩ := lintegral_outer_rpow_shift 2 (by norm_num)
  refine ⟨C₁ * (C₂ + 1), by positivity, ?_⟩
  intro j n k h hh hsupp hmean
  have hhint : Integrable h volume := memLp_one_iff_integrable.mp hh
  have hhae : AEMeasurable (fun y : ℝ => ‖h y‖ₑ) volume := hhint.aestronglyMeasurable.enorm
  have hMtop : (∫⁻ y, ‖h y‖ₑ) ≠ ⊤ := by
    have h1 : eLpNorm h 1 volume < ∞ := hh.eLpNorm_lt_top
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm hh.aestronglyMeasurable] at h1
    exact h1.ne
  set c : ℝ := (k : ℝ) * (2 : ℝ) ^ n with hc
  set s : ℝ := (2 : ℝ) ^ n with hs
  have hspos : 0 < s := by rw [hs]; exact zpow_pos (by norm_num) n
  have hzero : ∫ y, h y = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := h)
      (s := dyCell n k) hsupp).symm.trans hmean
  have hmeasR : MeasurableSet {x : ℝ | 2 * s < |x - c|} :=
    measurableSet_lt measurable_const (measurable_id.sub measurable_const).abs
  -- the translation estimate in terms of `annulusK`
  have htransK : ∀ y z : ℝ, 2 * |y| < |z| →
      (∑' m : ℤ, ‖annulusK b (j + m) (z - y) - annulusK b (j + m) z‖ₑ ^ (2 : ℝ))
          ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (C₁ * |y| / |z| ^ 2) := by
    intro y z hyz
    have heq : (∑' m : ℤ, ‖annulusK b (j + m) (z - y) - annulusK b (j + m) z‖ₑ ^ (2 : ℝ))
        = (∑' m : ℤ, ‖FourierTransform.fourierInv (b (j + m)) (z - y)
            - FourierTransform.fourierInv (b (j + m)) z‖ₑ ^ (2 : ℝ)) :=
      tsum_congr fun m => by simp only [annulusK]
    rw [heq]
    exact htrans j y z hyz
  -- the pointwise bound on the square function
  have hpt : ∀ x ∈ {x : ℝ | 2 * s < |x - c|},
      annulusSqfun b j h x ≤ ENNReal.ofReal (C₁ * s / |x - c| ^ 2) * (∫⁻ y, ‖h y‖ₑ) := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have hcomp : ∀ m : ℤ, ‖annulusConv b (j + m) h x‖ₑ ≤
        ∫⁻ y, ‖annulusK b (j + m) (x - y) - annulusK b (j + m) (x - c)‖ₑ * ‖h y‖ₑ := by
      intro m
      rw [annulusConv_pivot_diff b hb hsmooth (j + m) h hhint hzero x c]
      exact (enorm_integral_le_lintegral_enorm _).trans
        (le_of_eq (lintegral_congr fun y => enorm_mul _ _))
    have hm : ∀ m : ℤ, AEMeasurable
        (fun y : ℝ => ‖annulusK b (j + m) (x - y) - annulusK b (j + m) (x - c)‖ₑ
          * ‖h y‖ₑ) volume := by
      intro m
      have hcont : Continuous
          (fun y : ℝ => annulusK b (j + m) (x - y) - annulusK b (j + m) (x - c)) :=
        ((continuous_annulusK b hb hsmooth (j + m)).comp
          (continuous_const.sub continuous_id)).sub continuous_const
      exact (hcont.measurable.enorm.aemeasurable).mul hhae
    have hmink := sqrt_tsum_lintegral_sq_le
      (fun m y => ‖annulusK b (j + m) (x - y) - annulusK b (j + m) (x - c)‖ₑ
        * ‖h y‖ₑ) hm
    have hbound : ∀ y : ℝ, (∑' m : ℤ, ‖annulusK b (j + m) (x - y)
            - annulusK b (j + m) (x - c)‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * ‖h y‖ₑ
        ≤ ENNReal.ofReal (C₁ * s / |x - c| ^ 2) * ‖h y‖ₑ := by
      intro y
      by_cases hy : h y = 0
      · rw [hy, enorm_zero, mul_zero, mul_zero]
      · have hymem : y ∈ dyCell n k := by
          by_contra hcon
          exact hy (hsupp y hcon)
        have hyb : |y - c| ≤ s := by
          rw [hc, hs]
          exact abs_sub_mul_zpow_le_of_mem_dyCell hymem
        have hyz : 2 * |y - c| < |x - c| := by
          have h2s : 2 * |y - c| ≤ 2 * s := by linarith
          linarith
        have hb1 := htransK (y - c) (x - c) hyz
        rw [show (x - c) - (y - c) = x - y by ring] at hb1
        refine (mul_le_mul_left hb1 ‖h y‖ₑ).trans ?_
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hyb hC₁.le
    calc annulusSqfun b j h x
        = (∑' m : ℤ, ‖annulusConv b (j + m) h x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := rfl
      _ ≤ (∑' m : ℤ, (∫⁻ y, ‖annulusK b (j + m) (x - y)
              - annulusK b (j + m) (x - c)‖ₑ * ‖h y‖ₑ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun m =>
            ENNReal.rpow_le_rpow (hcomp m) (by norm_num)) (by norm_num)
      _ ≤ ∫⁻ y, (∑' m : ℤ, (‖annulusK b (j + m) (x - y)
              - annulusK b (j + m) (x - c)‖ₑ * ‖h y‖ₑ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := hmink
      _ = ∫⁻ y, (∑' m : ℤ, ‖annulusK b (j + m) (x - y)
              - annulusK b (j + m) (x - c)‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * ‖h y‖ₑ := by
          apply lintegral_congr; intro y
          exact sqrt_tsum_mul_sq (fun m => ‖annulusK b (j + m) (x - y)
            - annulusK b (j + m) (x - c)‖ₑ) ‖h y‖ₑ
      _ ≤ ∫⁻ y, ENNReal.ofReal (C₁ * s / |x - c| ^ 2) * ‖h y‖ₑ := lintegral_mono hbound
      _ = ENNReal.ofReal (C₁ * s / |x - c| ^ 2) * ∫⁻ y, ‖h y‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- the outer integral
  have houter' : ∫⁻ x in {x : ℝ | 2 * s < |x - c|}, ENNReal.ofReal (C₁ * s / |x - c| ^ 2)
      ≤ ENNReal.ofReal (C₁ * C₂) := by
    have heq : ∀ x : ℝ, ENNReal.ofReal (C₁ * s / |x - c| ^ 2)
        = ENNReal.ofReal C₁ * ENNReal.ofReal (s * |x - c| ^ (-(2 : ℝ))) := by
      intro x
      have h1 : (|x - c| ^ 2)⁻¹ = |x - c| ^ (-(2 : ℝ)) := by
        rw [show -(2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg (abs_nonneg (x - c)), Real.rpow_natCast]
      have h2 : C₁ * s / |x - c| ^ 2 = C₁ * (s * |x - c| ^ (-(2 : ℝ))) := by
        rw [div_eq_mul_inv, h1]; ring
      rw [h2, ENNReal.ofReal_mul hC₁.le]
    have h2 : ∫⁻ x in {x : ℝ | 2 * s < |x - c|},
          ENNReal.ofReal C₁ * ENNReal.ofReal (s * |x - c| ^ (-(2 : ℝ)))
        = ENNReal.ofReal C₁ * ∫⁻ x in {x : ℝ | 2 * s < |x - c|},
            ENNReal.ofReal (s * |x - c| ^ (-(2 : ℝ))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [setLIntegral_congr_fun hmeasR (fun x _ => heq x), h2]
    have hout := houter s c hspos
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hout
    calc ENNReal.ofReal C₁ * ∫⁻ x in {x : ℝ | 2 * s < |x - c|},
            ENNReal.ofReal (s * |x - c| ^ (-(2 : ℝ)))
        ≤ ENNReal.ofReal C₁ * ENNReal.ofReal C₂ := mul_le_mul_right hout _
      _ = ENNReal.ofReal (C₁ * C₂) := (ENNReal.ofReal_mul hC₁.le).symm
  calc ∫⁻ x in {x : ℝ | 2 * s < |x - c|}, annulusSqfun b j h x
      ≤ ∫⁻ x in {x : ℝ | 2 * s < |x - c|},
          ENNReal.ofReal (C₁ * s / |x - c| ^ 2) * (∫⁻ y, ‖h y‖ₑ) :=
        setLIntegral_mono (by measurability) (fun x hx => hpt x hx)
    _ = (∫⁻ x in {x : ℝ | 2 * s < |x - c|}, ENNReal.ofReal (C₁ * s / |x - c| ^ 2))
            * (∫⁻ y, ‖h y‖ₑ) := lintegral_mul_const' _ _ hMtop
    _ ≤ ENNReal.ofReal (C₁ * C₂) * (∫⁻ y, ‖h y‖ₑ) := mul_le_mul_left houter' _
    _ ≤ ENNReal.ofReal (C₁ * (C₂ + 1)) * (∫⁻ y, ‖h y‖ₑ) := by
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        nlinarith [hC₁.le, hC₂]

end Work.BourgainPlan.Maximal
