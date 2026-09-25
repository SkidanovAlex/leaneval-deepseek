import Mathlib
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.CalderonZygmund.lacunary_shifted_kernel_sum_le
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

noncomputable section

/-! ## The linear reproducing bound

Every `L¹`, continuous, `[-1/2,1/2]`-band-limited function `g` satisfies
`‖g x‖ ≤ C * ∫ y, ‖g y‖ * (1 + (x - y) ^ 2)⁻¹` with the constant `C` taken from the
reproducing kernel. -/

private lemma norm_le_integral_weighted {C : ℝ} (hC : 0 < C) {K : ℝ → ℂ}
    (hKb : ∀ x : ℝ, ‖K x‖ ≤ C / (1 + x ^ 2))
    (g : ℝ → ℂ) (hg : Integrable g) (hcont : Continuous g)
    (hrep : ∀ x : ℝ, ContinuousAt g x → g x = ∫ y : ℝ, g y * K (x - y)) (x : ℝ) :
    ‖g x‖ ≤ C * ∫ y : ℝ, ‖g y‖ * (1 + (x - y) ^ 2)⁻¹ := by
  have hk : Continuous (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) :=
    Continuous.inv₀ (continuous_const.add ((continuous_const.sub continuous_id).pow 2))
      (fun y => by positivity)
  have hgi : Integrable (fun y : ℝ => C * (‖g y‖ * (1 + (x - y) ^ 2)⁻¹)) := by
    refine Integrable.mono' (g := fun y : ℝ => C * ‖g y‖) (hg.norm.const_mul C) ?_ ?_
    · exact (hg.aestronglyMeasurable.norm.mul hk.aestronglyMeasurable).const_mul C
    · filter_upwards with y
      rw [Real.norm_of_nonneg (by positivity)]
      have hk1 : (1 + (x - y) ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]; nlinarith [sq_nonneg (x - y)]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hk1) hC.le
  have h1 : ‖g x‖ ≤ ∫ y : ℝ, ‖g y * K (x - y)‖ := by
    rw [hrep x hcont.continuousAt]
    exact norm_integral_le_integral_norm _
  have h2 : (∫ y : ℝ, ‖g y * K (x - y)‖)
      ≤ ∫ y : ℝ, C * (‖g y‖ * (1 + (x - y) ^ 2)⁻¹) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => by positivity)) hgi ?_
    filter_upwards with y
    have h3 : ‖K (x - y)‖ ≤ C * (1 + (x - y) ^ 2)⁻¹ := by
      simpa only [div_eq_mul_inv] using hKb (x - y)
    calc ‖g y * K (x - y)‖ = ‖g y‖ * ‖K (x - y)‖ := norm_mul _ _
      _ ≤ ‖g y‖ * (C * (1 + (x - y) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = C * (‖g y‖ * (1 + (x - y) ^ 2)⁻¹) := by ring
  have h3 : (∫ y : ℝ, C * (‖g y‖ * (1 + (x - y) ^ 2)⁻¹))
      = C * ∫ y : ℝ, ‖g y‖ * (1 + (x - y) ^ 2)⁻¹ := integral_const_mul C _
  linarith [h1, h2, h3]

/-! ## The `ENNReal` Jensen/Hölder inequality -/

private lemma lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    (hp : 1 < p) {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ p ≤ (∫⁻ a, g a ∂μ) ^ (p - 1) * ∫⁻ a, f a ^ p * g a ∂μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hα : 0 ≤ 1 / p := by positivity
  have hβ : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]; linarith
  have hαβ : 1 / p + (1 - 1 / p) = 1 := by ring
  have hF : AEMeasurable (fun a => f a ^ p * g a) μ := (hf.pow_const p).mul hg
  have hkey := ENNReal.lintegral_mul_norm_pow_le hF hg hα hβ hαβ
  have hpt : ∀ a : α, (f a ^ p * g a) ^ (1 / p) * g a ^ (1 - 1 / p) = f a * g a := by
    intro a
    have h3 : p * (1 / p) = 1 := by
      rw [one_div, mul_inv_cancel₀ (ne_of_gt hp0)]
    have step1 : (f a ^ p * g a) ^ (1 / p) = f a * g a ^ (1 / p) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hα, ← ENNReal.rpow_mul, h3, ENNReal.rpow_one]
    have step2 : g a ^ (1 / p) * g a ^ (1 - 1 / p) = g a := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / p) (1 - 1 / p) hα hβ, hαβ, ENNReal.rpow_one]
    calc (f a ^ p * g a) ^ (1 / p) * g a ^ (1 - 1 / p)
        = (f a * g a ^ (1 / p)) * g a ^ (1 - 1 / p) := by rw [step1]
      _ = f a * (g a ^ (1 / p) * g a ^ (1 - 1 / p)) := by rw [mul_assoc]
      _ = f a * g a := by rw [step2]
  have hkey2 : ∫⁻ a, f a * g a ∂μ
      ≤ (∫⁻ a, f a ^ p * g a ∂μ) ^ (1 / p) * (∫⁻ a, g a ∂μ) ^ (1 - 1 / p) := by
    simpa only [hpt] using hkey
  have h4 : 1 / p * p = 1 := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hp0)]
  have h5 : (1 - 1 / p) * p = p - 1 := by
    rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp0)]
  calc (∫⁻ a, f a * g a ∂μ) ^ p
      ≤ ((∫⁻ a, f a ^ p * g a ∂μ) ^ (1 / p) * (∫⁻ a, g a ∂μ) ^ (1 - 1 / p)) ^ p :=
        ENNReal.rpow_le_rpow hkey2 hp0.le
    _ = ((∫⁻ a, f a ^ p * g a ∂μ) ^ (1 / p)) ^ p
          * ((∫⁻ a, g a ∂μ) ^ (1 - 1 / p)) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp0.le
    _ = (∫⁻ a, f a ^ p * g a ∂μ) ^ ((1 / p) * p)
          * (∫⁻ a, g a ∂μ) ^ ((1 - 1 / p) * p) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ = (∫⁻ a, f a ^ p * g a ∂μ) * (∫⁻ a, g a ∂μ) ^ (p - 1) := by
        rw [h4, h5, ENNReal.rpow_one]
    _ = (∫⁻ a, g a ∂μ) ^ (p - 1) * ∫⁻ a, f a ^ p * g a ∂μ := mul_comm _ _

/-! ## The lattice weight on `ℤ` -/

private lemma summable_inv_one_add_sq_sub (t : ℝ) :
    Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((Commons.Analysis.Fourier.summable_one_add_sq_int).mul_left (2 * (1 + t ^ 2)))
  have hkey : 1 + (m : ℝ) ^ 2 ≤ (2 * (1 + t ^ 2)) * (1 + ((m : ℝ) - t) ^ 2) := by
    nlinarith [sq_nonneg ((m : ℝ) - 2 * t), sq_nonneg t]
  rw [show (2 * (1 + t ^ 2)) * (1 + (m : ℝ) ^ 2)⁻¹
      = ((1 + (m : ℝ) ^ 2) / (2 * (1 + t ^ 2)))⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [hkey]

private lemma tsum_ofReal_inv_one_add_sq_sub_le :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      (∑' m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - t) ^ 2)⁻¹)) ≤ ENNReal.ofReal B := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Real.tsum_int_inv_one_add_sq_sub_le
  refine ⟨B, hBpos, fun t => ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (summable_inv_one_add_sq_sub t)]
  exact ENNReal.ofReal_le_ofReal (hB t)

private lemma lintegral_ofReal_inv_one_add_sq_sub_le (x : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹)) ≤ ENNReal.ofReal Real.pi := by
  have htrans : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + (y + (-x)) ^ 2)⁻¹))
      = ∫⁻ y : ℝ, ENNReal.ofReal ((1 + y ^ 2)⁻¹) :=
    lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => ENNReal.ofReal ((1 + y ^ 2)⁻¹)) (-x)
  have hfun : (fun y : ℝ => ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹))
      = fun y : ℝ => ENNReal.ofReal ((1 + (y + (-x)) ^ 2)⁻¹) := by
    funext y
    rw [show (1 + (x - y) ^ 2 : ℝ) = 1 + (y + (-x)) ^ 2 by ring]
  rw [hfun, htrans, ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
    (Filter.Eventually.of_forall (fun y => by positivity)), integral_univ_inv_one_add_sq]

/-! ## The main theorem -/

theorem lattice_sup_le_integral_sup_band_limited_rpow {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → ℝ → ℂ),
      (∀ j : ℕ, MeasureTheory.Integrable (h j)) →
      (∀ j : ℕ, Continuous (h j)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier (h j) ξ = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂MeasureTheory.volume := by
  obtain ⟨K, hKint, ⟨Ck, hCkpos, hCkdec⟩, hKrep⟩ := band_limited_reproducing_kernel
  obtain ⟨B', hB'pos, hB'⟩ := tsum_ofReal_inv_one_add_sq_sub_le
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0:ℝ) ≤ p - 1 := by linarith
  have hApos : 0 < Ck ^ p * Real.pi ^ (p - 1) :=
    mul_pos (Real.rpow_pos_of_pos hCkpos p) (Real.rpow_pos_of_pos Real.pi_pos (p - 1))
  refine ⟨Ck ^ p * Real.pi ^ (p - 1) * B', mul_pos hApos hB'pos, ?_⟩
  intro h hint hcont hbl
  set F : ℝ → ENNReal := fun x => ⨆ j : ℕ, ENNReal.ofReal ‖h j x‖ with hF
  have hFmeas : Measurable F := by
    rw [hF]
    exact Measurable.iSup (fun j => ENNReal.measurable_ofReal.comp ((hcont j).norm.measurable))
  have hFae : AEMeasurable F (volume : Measure ℝ) := hFmeas.aemeasurable
  -- pointwise bound at a single lattice point
  have hbound : ∀ x : ℝ,
      F x ≤ ENNReal.ofReal Ck *
        ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
    intro x
    refine iSup_le (fun j => ?_)
    have hb := norm_le_integral_weighted hCkpos hCkdec (h j) (hint j) (hcont j)
      (hKrep (h j) (hint j) (hbl j)) x
    have hcφ : Continuous (fun y : ℝ => ‖h j y‖ * (1 + (x - y) ^ 2)⁻¹) := by
      refine Continuous.mul ((hcont j).norm) ?_
      exact Continuous.inv₀ (continuous_const.add ((continuous_const.sub continuous_id).pow 2))
        (fun y => by positivity)
    have hnnφ : ∀ y : ℝ, 0 ≤ ‖h j y‖ * (1 + (x - y) ^ 2)⁻¹ := fun y => by positivity
    have hstep2 : ENNReal.ofReal (∫ y : ℝ, ‖h j y‖ * (1 + (x - y) ^ 2)⁻¹) ≤
        ∫⁻ y : ℝ, ENNReal.ofReal (‖h j y‖ * (1 + (x - y) ^ 2)⁻¹) := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnnφ)
        hcφ.aestronglyMeasurable]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal ‖h j x‖
        ≤ ENNReal.ofReal Ck *
            ENNReal.ofReal (∫ y : ℝ, ‖h j y‖ * (1 + (x - y) ^ 2)⁻¹) := by
          rw [← ENNReal.ofReal_mul hCkpos.le]
          exact ENNReal.ofReal_le_ofReal hb
      _ ≤ ENNReal.ofReal Ck *
            ∫⁻ y : ℝ, ENNReal.ofReal (‖h j y‖ * (1 + (x - y) ^ 2)⁻¹) :=
          mul_le_mul_right hstep2 _
      _ ≤ ENNReal.ofReal Ck *
            ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
          apply mul_le_mul_right
          apply lintegral_mono
          intro y
          change ENNReal.ofReal (‖h j y‖ * (1 + (x - y) ^ 2)⁻¹)
            ≤ F y * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹)
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
          exact mul_le_mul_left (le_iSup (fun j => ENNReal.ofReal ‖h j y‖) j) _
  have hstep : ∀ m : ℤ, F (m : ℝ) ^ p ≤ ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
      ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
    intro m
    have hb := hbound (m : ℝ)
    have hVmeas : Measurable
        (fun y : ℝ => ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) :=
      ENNReal.measurable_ofReal.comp
        (Continuous.measurable (Continuous.inv₀
          (continuous_const.add ((continuous_const.sub continuous_id).pow 2))
          (fun y => by positivity)))
    have hjensen := lintegral_mul_rpow_le hp hFae hVmeas.aemeasurable
    have hVpi : (∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
        ≤ ENNReal.ofReal Real.pi := lintegral_ofReal_inv_one_add_sq_sub_le _
    calc F (m : ℝ) ^ p
        ≤ (ENNReal.ofReal Ck *
            ∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p :=
          ENNReal.rpow_le_rpow hb hp0.le
      _ = ENNReal.ofReal (Ck ^ p) *
            (∫⁻ y : ℝ, F y * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
            ENNReal.ofReal_rpow_of_nonneg hCkpos.le hp0.le]
      _ ≤ ENNReal.ofReal (Ck ^ p) *
            ((∫⁻ y : ℝ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) ^ (p - 1) *
              ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) :=
          mul_le_mul_right hjensen _
      _ ≤ ENNReal.ofReal (Ck ^ p) *
            (ENNReal.ofReal Real.pi ^ (p - 1) *
              ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) := by
          apply mul_le_mul_right
          exact mul_le_mul_left (ENNReal.rpow_le_rpow hVpi hp1) _
      _ = ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_rpow_of_nonneg Real.pi_pos.le hp1, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hCkpos p).le]
  have hVmeasZ : ∀ y : ℝ, Measurable
      (fun m : ℤ => ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)) := fun y =>
    measurable_of_countable _
  have hcount : ∀ y : ℝ,
      (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) ∂Measure.count)
        ≤ ENNReal.ofReal B' := by
    intro y
    rw [lintegral_count]
    exact hB' y
  have hpair : Measurable (Function.uncurry (fun (m : ℤ) (y : ℝ) =>
      F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))) := by
    show Measurable (fun q : ℤ × ℝ =>
      F q.2 ^ p * ENNReal.ofReal ((1 + ((q.1 : ℝ) - q.2) ^ 2)⁻¹))
    refine Measurable.mul ?_ ?_
    · exact (hFmeas.comp measurable_snd).pow_const p
    · refine ENNReal.measurable_ofReal.comp ?_
      have h2 : Measurable (fun q : ℤ × ℝ => (1 + ((q.1 : ℝ) - q.2) ^ 2 : ℝ)) := by fun_prop
      exact measurable_inv.comp h2
  have hmain : (∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count)
      ≤ ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1) * B') *
          ∫⁻ x : ℝ, F x ^ p ∂volume := by
    calc (∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count)
        ≤ ∫⁻ m : ℤ, ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            (∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
              ∂Measure.count := lintegral_mono hstep
      _ = ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ m : ℤ, (∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹))
              ∂Measure.count := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, (∫⁻ m : ℤ, F y ^ p * ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)
              ∂Measure.count) ∂volume := by
          congr 1
          rw [lintegral_lintegral_swap]
          exact hpair.aemeasurable
      _ = ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p *
              (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹) ∂Measure.count)
              ∂volume := by
          congr 1
          apply lintegral_congr
          intro y
          rw [lintegral_const_mul (F y ^ p) (hVmeasZ y)]
      _ ≤ ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1)) *
            ∫⁻ y : ℝ, F y ^ p * ENNReal.ofReal B' ∂volume := by
          apply mul_le_mul_right
          apply lintegral_mono
          intro y
          change F y ^ p * (∫⁻ m : ℤ, ENNReal.ofReal ((1 + ((m : ℝ) - y) ^ 2)⁻¹)
              ∂Measure.count) ≤ F y ^ p * ENNReal.ofReal B'
          exact mul_le_mul_right (hcount y) _
      _ = ENNReal.ofReal (Ck ^ p * Real.pi ^ (p - 1) * B') *
            ∫⁻ y : ℝ, F y ^ p ∂volume := by
          rw [lintegral_mul_const _ (hFmeas.pow_const p),
            mul_comm (∫⁻ y : ℝ, F y ^ p ∂volume) (ENNReal.ofReal B'), ← mul_assoc,
            ← ENNReal.ofReal_mul hApos.le]
  have hL : (∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ p ∂Measure.count)
      = ∫⁻ m : ℤ, F (m : ℝ) ^ p ∂Measure.count := by
    apply lintegral_congr
    intro m
    rw [hF]
    simp only [← ofReal_norm]
  have hR : (∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂volume)
      = ∫⁻ x : ℝ, F x ^ p ∂volume := by
    apply lintegral_congr
    intro x
    rw [hF]
    simp only [← ofReal_norm]
  rw [hL, hR]
  exact hmain

end

end Commons.Analysis.Fourier
