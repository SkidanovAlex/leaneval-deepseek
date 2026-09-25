import Mathlib
import Submission.Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm_complex
import Submission.Commons.Analysis.Convolution.lintegral_rpow_le_of_forall_mul_le

namespace Commons.MeasureTheory.Function

open _root_.MeasureTheory ENNReal
open scoped ENNReal

/-- The extended norm of a real number, viewed as a complex number, is unchanged. -/
private lemma enorm_complex_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  simp only [enorm_eq_nnnorm]
  norm_cast

/-- `ENNReal.ofReal ‖z‖ = ‖z‖ₑ` for a complex number `z`. -/
private lemma ofReal_norm_eq_enorm (z : ℂ) : ENNReal.ofReal ‖z‖ = ‖z‖ₑ := by
  simp [enorm_eq_nnnorm]

/-- Every almost-everywhere finite `ℝ≥0∞`-valued a.e. measurable function is the extended
norm of a complex-valued a.e. measurable function. -/
lemma exists_aemeasurable_complex_enorm_eq_ae {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hgf : ∀ᵐ x ∂μ, g x ≠ ∞) :
    ∃ γ : α → ℂ, AEMeasurable γ μ ∧ ∀ᵐ x ∂μ, ‖γ x‖ₑ = g x := by
  refine ⟨fun x => ((g x).toReal : ℂ), ?_, ?_⟩
  · exact Complex.measurable_ofReal.comp_aemeasurable hg.ennreal_toReal
  · filter_upwards [hgf] with x hx
    rw [enorm_complex_ofReal, Real.enorm_toReal hx]

/-- Scaling identity for Lebesgue integrals of `ℝ≥0∞`-valued functions: multiplying the
integrand by `t⁻¹` and then the integral by `t` returns the original integral. -/
private lemma lintegral_eq_lintegral_mul_inv_mul {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : α → ℝ≥0∞} (hu : AEMeasurable u μ) {t : ℝ≥0∞}
    (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    ∫⁻ x, u x ∂μ = (∫⁻ x, u x * t⁻¹ ∂μ) * t := by
  rw [lintegral_mul_const'' t⁻¹ hu, mul_assoc, ENNReal.inv_mul_cancel ht0 httop, mul_one]

/-- The "sharpness" half of the `Lᵖ`–`Lᵠ` duality: any `ℝ≥0∞`-valued function whose `Lᵠ`
norm (in extended exponent form) is at most `1` is dominated, against a fixed nonnegative
weight `F`, by some complex-valued a.e. measurable function in the `Lᵠ` unit ball. -/
theorem lintegral_mul_le_iSup_lintegral_mul_of_rpow_le_one {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    {F : α → ℝ≥0∞} {g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hg1 : (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal) ≤ 1) :
    ∫⁻ x, F x * g x ∂μ ≤
      ⨆ (γ : {γ : α → ℂ // AEMeasurable γ μ ∧ MeasureTheory.eLpNorm γ q μ ≤ 1}),
        ∫⁻ x, F x * ‖γ.1 x‖ₑ ∂μ := by
  have hq'pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hA : (∫⁻ x, g x ^ q.toReal ∂μ)
      = ((∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq'pos.ne', ENNReal.rpow_one]
  have hAle : (∫⁻ x, g x ^ q.toReal ∂μ) ≤ 1 := by
    rw [hA]
    calc ((∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal
        ≤ 1 ^ q.toReal := ENNReal.rpow_le_rpow hg1 hq'pos.le
      _ = 1 := ENNReal.one_rpow _
  have hint_lt : (∫⁻ x, g x ^ q.toReal ∂μ) < ∞ := lt_of_le_of_lt hAle ENNReal.one_lt_top
  have hgf : ∀ᵐ x ∂μ, g x ≠ ∞ := by
    have h1 : ∀ᵐ x ∂μ, g x ^ q.toReal < ∞ :=
      ae_lt_top' (hg.pow_const q.toReal) hint_lt.ne
    filter_upwards [h1] with x hx
    exact ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos hq'pos).mp hx)
  obtain ⟨γ, hγaem, hγeq⟩ := exists_aemeasurable_complex_enorm_eq_ae hg hgf
  have hγnorm : MeasureTheory.eLpNorm γ q μ ≤ 1 := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hγaem.aestronglyMeasurable]
    have h2 : ∫⁻ x, ‖γ x‖ₑ ^ q.toReal ∂μ = ∫⁻ x, g x ^ q.toReal ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hγeq] with x hx
      rw [hx]
    rw [h2]
    exact hg1
  have heq : ∫⁻ x, F x * g x ∂μ = ∫⁻ x, F x * ‖γ x‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hγeq] with x hx
    rw [hx]
  rw [heq]
  exact le_iSup (fun γ : {γ : α → ℂ // AEMeasurable γ μ ∧ MeasureTheory.eLpNorm γ q μ ≤ 1} =>
      ∫⁻ x, F x * ‖γ.1 x‖ₑ ∂μ) ⟨γ, hγaem, hγnorm⟩

theorem eLpNorm_eq_iSup_lintegral_mul_sigmaFinite {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] {p q : ENNReal} (hpq : p⁻¹ + q⁻¹ = 1)
    (hp : 1 < p) (hq : 1 < q) {f : α → ℂ} (hf : AEMeasurable f μ) :
    MeasureTheory.eLpNorm f p μ
      = ⨆ (g : {g : α → ℂ // AEMeasurable g μ ∧ MeasureTheory.eLpNorm g q μ ≤ 1}),
          MeasureTheory.lintegral μ (fun x => ENNReal.ofReal ‖f x * g.1 x‖) := by
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hq0 : q ≠ 0 := (lt_trans zero_lt_one hq).ne'
  have hpne_top : p ≠ ∞ := by
    intro hpinf
    have hqinv : q⁻¹ = 1 := by
      have h := hpq
      rw [hpinf, ENNReal.inv_top, zero_add] at h
      exact h
    have hq1 : q = 1 := by
      have := congrArg (fun x : ℝ≥0∞ => x⁻¹) hqinv
      simpa using this
    rw [hq1] at hq
    exact absurd hq (lt_irrefl (1 : ℝ≥0∞))
  have hqne_top : q ≠ ∞ := by
    intro hqinf
    have hpinv : p⁻¹ = 1 := by
      have h := hpq
      rw [hqinf, ENNReal.inv_top, add_zero] at h
      exact h
    have hp1 : p = 1 := by
      have := congrArg (fun x : ℝ≥0∞ => x⁻¹) hpinv
      simpa using this
    rw [hp1] at hp
    exact absurd hp (lt_irrefl (1 : ℝ≥0∞))
  have hp'1 : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (show (1 : ℝ≥0∞) ≠ ∞ by simp) hpne_top).mpr hp
    simpa using this
  have hq'1 : 1 < q.toReal := by
    have := (ENNReal.toReal_lt_toReal (show (1 : ℝ≥0∞) ≠ ∞ by simp) hqne_top).mpr hq
    simpa using this
  have hp'pos : 0 < p.toReal := lt_trans zero_lt_one hp'1
  have hq'pos : 0 < q.toReal := lt_trans zero_lt_one hq'1
  have hconj : (p.toReal)⁻¹ + (q.toReal)⁻¹ = 1 := by
    have h2 := congrArg ENNReal.toReal hpq
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h2
    simpa [one_div] using h2
  have hmul' : (p.toReal - 1) * q.toReal = p.toReal := by
    have h : (p.toReal)⁻¹ + (q.toReal)⁻¹ = 1 := hconj
    have hp'n : p.toReal ≠ 0 := hp'pos.ne'
    have hq'n : q.toReal ≠ 0 := hq'pos.ne'
    field_simp at h
    nlinarith [h]
  have hdiv1 : p.toReal / (p.toReal - 1) = q.toReal := by
    rw [div_eq_iff (by linarith : p.toReal - 1 ≠ 0)]
    nlinarith [hmul']
  have hdiv2 : (p.toReal - 1) / p.toReal = 1 / q.toReal := by
    rw [div_eq_div_iff (by linarith : p.toReal ≠ 0) (by linarith : q.toReal ≠ 0)]
    linarith [hmul']
  set F : α → ℝ≥0∞ := fun x => ‖f x‖ₑ with hF
  have hF_meas : AEMeasurable F μ := by rw [hF]; exact hf.enorm
  have hterm : ∀ g : {g : α → ℂ // AEMeasurable g μ ∧ MeasureTheory.eLpNorm g q μ ≤ 1},
      MeasureTheory.lintegral μ (fun x => ENNReal.ofReal ‖f x * g.1 x‖)
        = ∫⁻ x, F x * ‖g.1 x‖ₑ ∂μ := by
    intro g
    apply lintegral_congr
    intro x
    rw [hF, ofReal_norm_eq_enorm, enorm_mul]
  have hcongr : (⨆ (g : {g : α → ℂ // AEMeasurable g μ ∧ MeasureTheory.eLpNorm g q μ ≤ 1}),
        MeasureTheory.lintegral μ (fun x => ENNReal.ofReal ‖f x * g.1 x‖))
      = ⨆ (g : {g : α → ℂ // AEMeasurable g μ ∧ MeasureTheory.eLpNorm g q μ ≤ 1}),
          ∫⁻ x, F x * ‖g.1 x‖ₑ ∂μ := iSup_congr hterm
  rw [hcongr]
  apply le_antisymm
  · -- Hard direction: `‖f‖ₚ ≤ ⨆_g ∫ F ‖g‖`.
    by_contra hcon
    obtain ⟨C, hSC, hCL⟩ := exists_between (not_le.mp hcon)
    have hCne0 : C ≠ 0 := (lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) hSC).ne'
    have hkey : ∀ g : α → ℝ≥0∞, AEMeasurable g μ →
        ∫⁻ x, F x * g x ∂μ ≤
          C * (∫⁻ x, g x ^ (p.toReal / (p.toReal - 1)) ∂μ) ^ ((p.toReal - 1) / p.toReal) := by
      intro g hg
      rw [hdiv1, hdiv2]
      set t : ℝ≥0∞ := (∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal) with ht
      rcases eq_or_ne t 0 with ht0 | ht0
      · have hInt0 : ∫⁻ x, g x ^ q.toReal ∂μ = 0 := by
          have h3 : ((∫⁻ x, g x ^ q.toReal ∂μ) ^ (1 / q.toReal)) ^ q.toReal
              = (0 : ℝ≥0∞) ^ q.toReal := by rw [← ht, ht0]
          rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq'pos.ne', ENNReal.rpow_one,
            ENNReal.zero_rpow_of_pos hq'pos] at h3
        have hg0 : g =ᵐ[μ] 0 := by
          have h1 : g ^ q.toReal =ᵐ[μ] 0 :=
            (lintegral_eq_zero_iff' (hg.pow_const q.toReal)).mp hInt0
          filter_upwards [h1] with x hx
          rcases (ENNReal.rpow_eq_zero_iff).mp hx with ⟨hx0, _⟩ | ⟨_, hneg⟩
          · exact hx0
          · exact absurd hneg (not_lt.mpr hq'pos.le)
        rw [ht0, mul_zero]
        suffices ∫⁻ x, F x * g x ∂μ = 0 by rw [this]
        rw [← lintegral_zero_fun]
        apply lintegral_congr_ae
        filter_upwards [hg0] with x hx
        simp [hx]
      · rcases eq_or_ne t ∞ with htinf | htfin
        · rw [htinf, ENNReal.mul_top hCne0]
          exact le_top
        · have ht'0 : t ≠ 0 := ht0
          have ht'top : t ≠ ∞ := htfin
          set h : α → ℝ≥0∞ := fun x => g x * t⁻¹ with hh
          have hval : ∀ x, h x = g x * t⁻¹ := fun x => rfl
          have hh_meas : AEMeasurable h μ := by
            rw [hh]; exact hg.mul_const _
          have htq : t ^ q.toReal = ∫⁻ x, g x ^ q.toReal ∂μ := by
            rw [ht]
            rw [← ENNReal.rpow_mul, one_div_mul_cancel hq'pos.ne', ENNReal.rpow_one]
          have hhq : (∫⁻ x, h x ^ q.toReal ∂μ) ^ (1 / q.toReal) ≤ 1 := by
            have hInt : ∫⁻ x, h x ^ q.toReal ∂μ = 1 := by
              have h1 : ∀ x, h x ^ q.toReal = g x ^ q.toReal * (t⁻¹) ^ q.toReal := by
                intro x
                rw [hval x]
                exact ENNReal.mul_rpow_of_nonneg (g x) t⁻¹ hq'pos.le
              rw [lintegral_congr h1]
              rw [lintegral_mul_const'' ((t⁻¹) ^ q.toReal) (hg.pow_const q.toReal)]
              rw [ENNReal.inv_rpow, htq]
              have htpos : 0 < t := lt_of_le_of_ne (zero_le) (Ne.symm ht'0)
              have hA0 : (∫⁻ x, g x ^ q.toReal ∂μ) ≠ 0 := by
                rw [← htq]; exact (ENNReal.rpow_pos htpos ht'top).ne'
              have hAtop : (∫⁻ x, g x ^ q.toReal ∂μ) ≠ ∞ := by
                rw [← htq]
                exact ne_of_lt ((ENNReal.rpow_lt_top_iff_of_pos hq'pos).mpr
                  (lt_of_le_of_ne le_top ht'top))
              exact ENNReal.mul_inv_cancel hA0 hAtop
            rw [hInt, ENNReal.one_rpow]
          have hhle : ∫⁻ x, F x * h x ∂μ ≤ C :=
            le_trans (lintegral_mul_le_iSup_lintegral_mul_of_rpow_le_one hq0 hqne_top hh_meas hhq)
              hSC.le
          have hFG : ∫⁻ x, F x * g x ∂μ = ∫⁻ x, (F * g) x ∂μ := by
            apply lintegral_congr; intro x; rw [Pi.mul_apply]
          have hFH : ∫⁻ x, F x * h x ∂μ = ∫⁻ x, (F * g) x * t⁻¹ ∂μ := by
            apply lintegral_congr
            intro x
            rw [hval x, Pi.mul_apply, mul_assoc]
          have hg_eq : ∫⁻ x, F x * g x ∂μ = (∫⁻ x, F x * h x ∂μ) * t := by
            rw [hFG, hFH]
            exact lintegral_eq_lintegral_mul_inv_mul (hF_meas.mul hg) ht'0 ht'top
          rw [hg_eq]
          exact mul_le_mul_left hhle t
    have hdual := Commons.Analysis.Convolution.lintegral_rpow_le_of_forall_mul_le
      (μ := μ) (q := p.toReal) hp'1 hF_meas (C := C) hkey
    have hL_eq : MeasureTheory.eLpNorm f p μ = (∫⁻ x, F x ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpne_top hf.aestronglyMeasurable, hF]
    exact absurd (hL_eq ▸ hdual) (not_le.mpr hCL)
  · -- Easy direction: Hölder's inequality.
    refine iSup_le (fun g => ?_)
    have hholder := eLpNorm_mul_le_eLpNorm_mul_eLpNorm_complex
      (p := 1) (q := p) (r := q) (hpq := by rw [inv_one]; exact hpq.symm) hf g.2.1
    calc ∫⁻ x, F x * ‖g.1 x‖ₑ ∂μ
        = ∫⁻ x, ‖f x * g.1 x‖ₑ ∂μ := by
          rw [hF]
          apply lintegral_congr
          intro x
          rw [enorm_mul]
      _ = MeasureTheory.eLpNorm (fun x => f x * g.1 x) 1 μ := by
          rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (f := fun x => f x * g.1 x)
            (hf.mul g.2.1).aestronglyMeasurable]
      _ ≤ MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g.1 q μ := hholder
      _ ≤ MeasureTheory.eLpNorm f p μ * 1 := mul_le_mul_right g.2.2 _
      _ = MeasureTheory.eLpNorm f p μ := mul_one _

end Commons.MeasureTheory.Function
