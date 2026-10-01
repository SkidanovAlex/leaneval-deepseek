import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound

open MeasureTheory Complex Filter Set
open scoped Real Topology BigOperators

namespace Commons.Analysis.Integral

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section


private def regExp (a L : ℝ) (u τ : ℝ) : ℂ :=
  Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * τ : ℝ) : ℂ)))
private def regK (a L : ℝ) (u τ : ℝ) : ℂ :=
  (regExp a L u τ - 1) / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)

private lemma regK_eq_gK (a L u τ : ℝ) : regK a L u τ = PsiKernelBound.gK a (L * τ) u := by
  simp only [regK, regExp, PsiKernelBound.gK, div_eq_mul_inv]

private lemma continuous_regK (a L : ℝ) (ha : 0 < a) :
    Continuous (fun p : ℝ × ℝ => regK a L p.1 p.2) := by
  unfold regK regExp
  apply Continuous.div
  · apply Continuous.sub _ continuous_const
    apply Complex.continuous_exp.comp
    fun_prop
  · fun_prop
  · intro p
    refine pow_ne_zero 2 ?_
    intro hh
    have h := congrArg Complex.re hh
    simp at h
    linarith

private lemma integrable_log_two_add_abs (b : ℝ) :
    Integrable (fun u : ℝ => (Real.log (2 + |b - u|) + 1) / (1 + u^2)) volume := by
  have hdom : Integrable (fun u : ℝ =>
      (Real.log (2 + |b|) + Real.log 3 + 1) * (1 + u^2)⁻¹ + Real.log (1 + u^2) / (1 + u^2)) volume :=
    (integrable_inv_one_add_sq.const_mul _).add PsiKernelBound.integrable_log_one_add_sq
  refine hdom.mono' ?_ ?_
  · exact ((by fun_prop : Measurable (fun u : ℝ => (Real.log (2 + |b - u|) + 1) / (1 + u^2)))).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by
      have h1 : (1:ℝ) ≤ 2 + |b - u| := by linarith [abs_nonneg (b - u)]
      linarith [Real.log_nonneg h1]) (by positivity))]
    have hbu : |b - u| ≤ |b| + |u| := abs_sub_le_iff.mpr
      ⟨by linarith [le_abs_self b, neg_le_abs u], by linarith [le_abs_self u, neg_le_abs b]⟩
    have h1 : 2 + |b - u| ≤ (2 + |b|) * (2 + |u|) := by
      nlinarith [abs_nonneg b, abs_nonneg u]
    have h2 : (0:ℝ) < 2 + |b - u| := by linarith [abs_nonneg (b - u)]
    have hlogb : Real.log (2 + |b - u|) ≤ Real.log (2 + |b|) + Real.log (2 + |u|) := by
      calc Real.log (2 + |b - u|) ≤ Real.log ((2 + |b|) * (2 + |u|)) := Real.log_le_log h2 h1
        _ = Real.log (2 + |b|) + Real.log (2 + |u|) := Real.log_mul (by positivity) (by positivity)
    have h4 : 2 + |u| ≤ 3 * (1 + u^2) := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg u]
    have h5 : (0:ℝ) < 2 + |u| := by linarith [abs_nonneg u]
    have h6 : (0:ℝ) < 3 * (1 + u^2) := by nlinarith [sq_nonneg u]
    have hlogu : Real.log (2 + |u|) ≤ Real.log 3 + Real.log (1 + u^2) := by
      calc Real.log (2 + |u|) ≤ Real.log (3 * (1 + u^2)) := Real.log_le_log h5 h4
        _ = Real.log 3 + Real.log (1 + u^2) := Real.log_mul (by norm_num) (by positivity)
    have hnum : Real.log (2 + |b - u|) + 1 ≤ Real.log (2 + |b|) + Real.log 3 + 1 + Real.log (1 + u^2) := by
      linarith [hlogb, hlogu]
    have hpos : (0:ℝ) < 1 + u^2 := by positivity
    rw [div_le_iff₀ hpos]
    have hrhs : ((Real.log (2 + |b|) + Real.log 3 + 1) * (1 + u^2)⁻¹ + Real.log (1 + u^2) / (1 + u^2)) * (1 + u^2)
        = (Real.log (2 + |b|) + Real.log 3 + 1) + Real.log (1 + u^2) := by
      field_simp
    rw [hrhs]
    linarith [hnum]

private lemma integrable_slice {h : ℝ → ℂ} {Ch : ℝ} (hCh : 0 ≤ Ch) (hhm : Measurable h)
    (hh : ∀ t : ℝ, ‖h t‖ ≤ Ch * (Real.log (2 + |t|) + 1))
    {a L b τ : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => h (b - u) * regK a L u τ) volume := by
  rw [show (fun u : ℝ => h (b - u) * regK a L u τ)
        = (fun u : ℝ => h (b - u) * PsiKernelBound.gK a (L * τ) u) from by
      funext u; rw [regK_eq_gK]]
  have hdom : Integrable (fun u : ℝ =>
      (2 * Ch) * ((Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a (L * τ) u‖)) volume :=
    (PsiKernelBound.integrable_log_gK a (L * τ) b ha).const_mul (2 * Ch)
  refine hdom.mono' ?_ ?_
  · exact ((hhm.comp (by fun_prop)).aestronglyMeasurable).mul
      ((PsiKernelBound.continuous_gK a (L * τ) ha).aestronglyMeasurable)
  · filter_upwards with u
    rw [norm_mul]
    have hb := hh (b - u)
    have habs : (0:ℝ) < 2 + |b - u| := by linarith [abs_nonneg (b - u)]
    have hle : 2 + |b - u| ≤ 2 * (2 + |b - u| / 2) := by linarith
    have hlog : Real.log (2 + |b - u|) ≤ Real.log 2 + Real.log (2 + |b - u| / 2) := by
      calc Real.log (2 + |b - u|) ≤ Real.log (2 * (2 + |b - u| / 2)) := Real.log_le_log habs hle
        _ = Real.log 2 + Real.log (2 + |b - u| / 2) := Real.log_mul (by norm_num) (by positivity)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hLu : 0 ≤ Real.log (2 + |b - u| / 2) := Real.log_nonneg (by linarith [abs_nonneg (b - u)])
    have hkey : Real.log (2 + |b - u|) + 1 ≤ 2 * (Real.log (2 + |b - u| / 2) + 7) := by
      linarith [hlog, hlog2, hLu]
    calc ‖h (b - u)‖ * ‖PsiKernelBound.gK a (L * τ) u‖
        ≤ (Ch * (Real.log (2 + |b - u|) + 1)) * ‖PsiKernelBound.gK a (L * τ) u‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ ≤ (Ch * (2 * (Real.log (2 + |b - u| / 2) + 7))) * ‖PsiKernelBound.gK a (L * τ) u‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left hkey hCh
      _ = (2 * Ch) * ((Real.log (2 + |b - u| / 2) + 7) * ‖PsiKernelBound.gK a (L * τ) u‖) := by ring

private lemma norm_gK_bound_nonneg {a L u τ : ℝ} (ha : 0 < a) (hL : 0 < L) (hτ : 0 ≤ τ) :
    ‖regK a L u τ‖ ≤ 2 * (1 + 1/a^2) / (1 + u^2) := by
  rw [regK_eq_gK]
  have h := PsiKernelBound.norm_gK_bound a (L*τ) u ha
  have hexp : Real.exp (-(L*τ)*a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ L * τ := mul_nonneg (le_of_lt hL) hτ
    nlinarith [h1, ha, hL, hτ]
  calc ‖PsiKernelBound.gK a (L*τ) u‖ ≤ (Real.exp (-(L*τ)*a) + 1) * (1 + 1/a^2) / (1 + u^2) := h
    _ ≤ 2 * (1 + 1/a^2) / (1 + u^2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hpos : (0:ℝ) ≤ 1 + 1/a^2 := by positivity
        nlinarith [hexp, hpos]

private lemma integrable_prod_diffs {h g : ℝ → ℂ} {Ch B : ℝ} (hCh : 0 ≤ Ch) (hhm : Measurable h)
    (hh : ∀ t : ℝ, ‖h t‖ ≤ Ch * (Real.log (2 + |t|) + 1)) (hcm : Measurable g) (hB : 0 ≤ B)
    {a L b x₀ : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) (hL : 0 < L)
    (hg : ∀ σ ∈ Set.Ioo (0:ℝ) x₀, ‖g σ‖ ≤ B) :
    Integrable (fun p : ℝ × ℝ =>
        (h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀) * g p.2)
      (volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) x₀)) := by
    rw [isFiniteMeasure_restrict]; rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hGint : Integrable (fun u : ℝ =>
      (4 * B * (1 + 1/a^2) * Ch) * ((Real.log (2 + |b - u|) + 1) / (1 + u^2))) volume :=
    (integrable_log_two_add_abs b).const_mul _
  have hGprod : Integrable (fun p : ℝ × ℝ =>
      (4 * B * (1 + 1/a^2) * Ch) * ((Real.log (2 + |b - p.1|) + 1) / (1 + p.1^2)))
      (volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))) := hGint.comp_fst _
  refine hGprod.mono' ?_ ?_
  · have hmp : Measurable (fun p : ℝ × ℝ => h (b - p.1)) :=
      hhm.comp (continuous_const.sub continuous_fst).measurable
    have hmpK : Measurable (fun p : ℝ × ℝ => regK a L p.1 p.2) := (continuous_regK a L ha).measurable
    have hmpKx : Measurable (fun p : ℝ × ℝ => regK a L p.1 x₀) :=
      ((continuous_regK a L ha).comp (continuous_fst.prodMk continuous_const)).measurable
    have hgp : Measurable (fun p : ℝ × ℝ => g p.2) := hcm.comp measurable_snd
    exact (((hmp.mul hmpK).sub (hmp.mul hmpKx)).mul hgp).aestronglyMeasurable
  · have hae_mem : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)), σ ∈ Set.Ioc (0:ℝ) x₀ :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    have hae_g : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)), ‖g σ‖ ≤ B := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
      apply measure_mono_null _ (measure_singleton x₀)
      intro σ hσ
      rw [Set.mem_singleton_iff]
      by_contra hne
      push Not at hσ
      obtain ⟨hmem, hgnot⟩ := hσ
      exact (not_lt_of_ge (hg σ ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩)) hgnot
    have hae : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (0:ℝ) x₀)), σ ∈ Set.Ioc (0:ℝ) x₀ ∧ ‖g σ‖ ≤ B :=
      hae_mem.and hae_g
    have hmeas_set : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc (0:ℝ) x₀ ∧ ‖g p.2‖ ≤ B} :=
      (measurableSet_Ioc.preimage measurable_snd).inter
        ((measurableSet_Iic.preimage (hcm.norm)).preimage measurable_snd)
    have hprodae : ∀ᵐ p ∂(volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))),
        p.2 ∈ Set.Ioc (0:ℝ) x₀ ∧ ‖g p.2‖ ≤ B :=
      (Measure.ae_prod_iff_ae_ae hmeas_set).2 (Filter.Eventually.of_forall (fun u => hae))
    filter_upwards [hprodae] with p hp
    obtain ⟨hpIoc, hpg⟩ := hp
    have hbound : ∀ τ : ℝ, 0 ≤ τ → ‖regK a L p.1 τ‖ ≤ 2 * (1 + 1/a^2) / (1 + p.1^2) :=
      fun τ hτ => norm_gK_bound_nonneg ha hL hτ
    have h1 : ‖h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀‖ ≤
        ‖h (b - p.1)‖ * (‖regK a L p.1 p.2‖ + ‖regK a L p.1 x₀‖) := by
      rw [show h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀
            = h (b - p.1) * (regK a L p.1 p.2 - regK a L p.1 x₀) by ring]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    have hb := hh (b - p.1)
    have hb1 : ‖regK a L p.1 p.2‖ ≤ 2 * (1 + 1/a^2) / (1 + p.1^2) := hbound p.2 (le_of_lt hpIoc.1)
    have hb2 : ‖regK a L p.1 x₀‖ ≤ 2 * (1 + 1/a^2) / (1 + p.1^2) := hbound x₀ (le_of_lt hx₀)
    have hsum : ‖regK a L p.1 p.2‖ + ‖regK a L p.1 x₀‖ ≤
        2 * (2 * (1 + 1/a^2) / (1 + p.1^2)) := by linarith
    have hlog1 : (0:ℝ) ≤ Real.log (2 + |b - p.1|) := Real.log_nonneg (by linarith [abs_nonneg (b-p.1)])
    calc ‖(h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀) * g p.2‖
        = ‖h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀‖ * ‖g p.2‖ := norm_mul _ _
      _ ≤ (‖h (b - p.1)‖ * (‖regK a L p.1 p.2‖ + ‖regK a L p.1 x₀‖)) * B :=
          mul_le_mul h1 hpg (norm_nonneg _) (by positivity)
      _ ≤ (Ch * (Real.log (2 + |b - p.1|) + 1) * (2 * (2 * (1 + 1/a^2) / (1 + p.1^2)))) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          apply mul_le_mul hb hsum (by positivity) (by nlinarith [hCh, hlog1])
      _ = (4 * B * (1 + 1/a^2) * Ch) * ((Real.log (2 + |b - p.1|) + 1) / (1 + p.1^2)) := by
          field_simp; ring

private lemma integral_intervalIntegral_swap {f : ℝ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Set.Ioc a b)))) :
    (∫ u : ℝ, ∫ σ in a..b, f u σ) = ∫ σ in a..b, ∫ u : ℝ, f u σ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    rw [isFiniteMeasure_restrict]; rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have h1 : (∫ u : ℝ, ∫ σ in a..b, f u σ)
      = ∫ u : ℝ, ∫ σ : ℝ, f u σ ∂(volume.restrict (Set.Ioc a b)) := by
    apply integral_congr_ae; filter_upwards with u
    exact intervalIntegral.integral_of_le hab
  rw [h1, MeasureTheory.integral_integral_swap hf, ← intervalIntegral.integral_of_le hab]

private lemma swap_abstract {P : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {c : ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hint₀ : Integrable (fun u => P u x₀) volume)
    (hintσ : ∀ σ, Integrable (fun u => P u σ) volume)
    (hprod : Integrable (fun p : ℝ × ℝ => (P p.1 p.2 - P p.1 x₀) * g p.2)
      (volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀)))) :
    (∫ u : ℝ, (-c * P u x₀ + ∫ σ in (0:ℝ)..x₀, (P u σ - P u x₀) * g σ))
      = (-c) * (∫ u : ℝ, P u x₀)
        + ∫ σ in (0:ℝ)..x₀, g σ * ((∫ u : ℝ, P u σ) - (∫ u : ℝ, P u x₀)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) x₀)) := by
    rw [isFiniteMeasure_restrict]; rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hA : Integrable (fun u => -c * P u x₀) volume := hint₀.const_mul (-c)
  have hB : Integrable (fun u => ∫ σ in (0:ℝ)..x₀, (P u σ - P u x₀) * g σ) volume := by
    have h := hprod.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact (intervalIntegral.integral_of_le (le_of_lt hx₀)).symm
  have hsplit : (∫ u, (-c * P u x₀ + ∫ σ in (0:ℝ)..x₀, (P u σ - P u x₀) * g σ))
      = (∫ u, -c * P u x₀) + (∫ u, ∫ σ in (0:ℝ)..x₀, (P u σ - P u x₀) * g σ) :=
    integral_add hA hB
  have hswap : (∫ u, ∫ σ in (0:ℝ)..x₀, (P u σ - P u x₀) * g σ)
      = ∫ σ in (0:ℝ)..x₀, ∫ u, (P u σ - P u x₀) * g σ :=
    integral_intervalIntegral_swap (le_of_lt hx₀) hprod
  have hpt : ∀ σ, (∫ u, (P u σ - P u x₀) * g σ) = g σ * ((∫ u, P u σ) - (∫ u, P u x₀)) := by
    intro σ
    rw [show (∫ u, (P u σ - P u x₀) * g σ) = ∫ u, g σ * (P u σ - P u x₀) from
          integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))]
    rw [integral_const_mul, integral_sub (hintσ σ) hint₀]
  have hcongr : (∫ σ in (0:ℝ)..x₀, ∫ u, (P u σ - P u x₀) * g σ)
      = ∫ σ in (0:ℝ)..x₀, g σ * ((∫ u, P u σ) - (∫ u, P u x₀)) :=
    intervalIntegral.integral_congr (fun σ _ => hpt σ)
  rw [hsplit, integral_const_mul, hswap, hcongr]

private lemma core_eq (a L : ℝ) (c : ℂ) (g : ℝ → ℂ) (x₀ u : ℝ) (ha : 0 < a) :
    (c * (1 - regExp a L u x₀)
        + ∫ σ in (0:ℝ)..x₀, (regExp a L u σ - regExp a L u x₀) * g σ)
        / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)
      = -c * regK a L u x₀
        + ∫ σ in (0:ℝ)..x₀, (regK a L u σ - regK a L u x₀) * g σ := by
  have hD : (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) ≠ 0 := by
    refine pow_ne_zero 2 ?_
    intro hh
    have h := congrArg Complex.re hh
    simp at h
    linarith
  have hkey : ∀ τ : ℝ, regExp a L u τ - 1 = regK a L u τ * (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) := by
    intro τ
    rw [regK, div_mul_cancel₀ _ hD]
  have hint : (∫ σ in (0:ℝ)..x₀, (regExp a L u σ - regExp a L u x₀) * g σ)
      = ∫ σ in (0:ℝ)..x₀,
          (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) * ((regK a L u σ - regK a L u x₀) * g σ) := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    have h1 : regExp a L u σ - regExp a L u x₀
        = (regK a L u σ - regK a L u x₀) * (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) := by
      rw [sub_mul, ← hkey σ, ← hkey x₀]; ring
    show (regExp a L u σ - regExp a L u x₀) * g σ
        = (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2) * ((regK a L u σ - regK a L u x₀) * g σ)
    rw [h1]; ring
  rw [hint, intervalIntegral.integral_const_mul]
  have h2 : c * (1 - regExp a L u x₀)
      = -c * (regK a L u x₀ * (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)) := by
    have hh : (1:ℂ) - regExp a L u x₀
        = -(regK a L u x₀ * (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)) := by
      rw [← hkey x₀]; ring
    rw [hh]; ring
  rw [h2, div_eq_iff hD]
  ring

private lemma lhs_pointwise (a L : ℝ) (h : ℝ → ℂ) (g : ℝ → ℂ) (c : ℂ) (b x₀ u : ℝ) (ha : 0 < a) :
    h (b - u) * ((c * (1 - regExp a L u x₀)
        + ∫ σ in (0:ℝ)..x₀, (regExp a L u σ - regExp a L u x₀) * g σ)
        / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))
      = -c * (h (b - u) * regK a L u x₀)
        + ∫ σ in (0:ℝ)..x₀, ((h (b - u) * regK a L u σ) - (h (b - u) * regK a L u x₀)) * g σ := by
  rw [core_eq a L c g x₀ u ha, mul_add]
  congr 1
  · ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro σ hσ
    ring

/-- The main swap identity. -/
theorem regK_cplx_const_diff_integral_swap {h : ℝ → ℂ} {g : ℝ → ℂ} {Ch B : ℝ} {c : ℂ}
    (hcm : Measurable g) (hCh : 0 ≤ Ch) (hhm : Measurable h)
    (hh : ∀ t : ℝ, ‖h t‖ ≤ Ch * (Real.log (2 + |t|) + 1))
    {a x₀ L b : ℝ} (ha : 0 < a) (hx₀ : 0 < x₀) (hL : 0 < L) (hB : 0 ≤ B)
    (hg : ∀ σ ∈ Set.Ioo (0:ℝ) x₀, ‖g σ‖ ≤ B) :
    (∫ u : ℝ, h (b - u) *
        ((c * (1 - Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * x₀ : ℝ) : ℂ))))
          + ∫ σ : ℝ in (0:ℝ)..x₀,
              (Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * σ : ℝ) : ℂ)))
                - Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * x₀ : ℝ) : ℂ)))) * g σ)
          / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))) =
      (-c) * (∫ u : ℝ, h (b - u) *
            ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * x₀ : ℝ) : ℂ))) - 1)
              / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)))
      + (∫ σ : ℝ in (0:ℝ)..x₀, g σ *
            ((∫ u : ℝ, h (b - u) *
                ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * σ : ℝ) : ℂ))) - 1)
                  / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)))
             - (∫ u : ℝ, h (b - u) *
                ((Complex.exp (-(((a : ℂ) + (u : ℂ) * Complex.I) * ((L * x₀ : ℝ) : ℂ))) - 1)
                  / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2))))) := by
  have hint₀ : Integrable (fun u : ℝ => h (b - u) * regK a L u x₀) volume :=
    integrable_slice hCh hhm hh ha
  have hintσ : ∀ σ : ℝ, Integrable (fun u : ℝ => h (b - u) * regK a L u σ) volume :=
    fun σ => integrable_slice hCh hhm hh ha
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (h (b - p.1) * regK a L p.1 p.2 - h (b - p.1) * regK a L p.1 x₀) * g p.2)
      (volume.prod (volume.restrict (Set.Ioc (0:ℝ) x₀))) :=
    integrable_prod_diffs hCh hhm hh hcm hB ha hx₀ hL hg
  have key := swap_abstract (P := fun u τ => h (b - u) * regK a L u τ) (g := g) (c := c)
      (x₀ := x₀) hx₀ hint₀ hintσ hprod
  have hLHS : (∫ u : ℝ, h (b - u) * ((c * (1 - regExp a L u x₀)
        + ∫ σ in (0:ℝ)..x₀, (regExp a L u σ - regExp a L u x₀) * g σ)
        / (((a : ℂ) + (u : ℂ) * Complex.I) ^ 2)))
      = ∫ u : ℝ, (-c * (h (b - u) * regK a L u x₀)
        + ∫ σ in (0:ℝ)..x₀, ((h (b - u) * regK a L u σ) - (h (b - u) * regK a L u x₀)) * g σ) := by
    apply integral_congr_ae
    filter_upwards with u
    exact lhs_pointwise a L h g c b x₀ u ha
  simp only [regExp] at hLHS
  rw [hLHS]
  simpa only [regK, regExp] using key

end
end Commons.Analysis.Integral
