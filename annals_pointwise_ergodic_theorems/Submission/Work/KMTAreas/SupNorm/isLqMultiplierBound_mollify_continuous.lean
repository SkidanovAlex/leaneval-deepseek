import Mathlib
import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite
import Submission.Work.KMTAreas.SupNorm.IsLqMultiplierBound_comp_add

namespace Work.KMTAreas.SupNorm

open scoped FourierTransform ENNReal NNReal
open MeasureTheory
open Work.Analysis.IWMultiplier

/-- The complex-valued Fourier character `t ↦ 𝐞 t` is continuous. -/
lemma continuous_fourierChar_coe : Continuous fun t : ℝ => (Real.fourierChar t : ℂ) := by
  rw [show (fun t : ℝ => (Real.fourierChar t : ℂ))
      = fun t => Complex.exp (↑(2 * Real.pi * t) * Complex.I) from by
    funext t; rw [Real.fourierChar_apply]]
  fun_prop

/-- The continuous Fourier multiplier `T_Ψ` with symbol `Ψ`, written as an integral of the symbol
against the inverse Fourier character. -/
lemma contMulOp_apply_eq_integral (Ψ : ℝ → ℂ) (g : ℝ → ℂ) (x : ℝ) :
    contMulOp Ψ g x = ∫ v, (Real.fourierChar (v * x) : ℂ) * (Ψ v * 𝓕 g v) := by
  rw [contMulOp, Real.fourierInv_eq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [Real.inner_apply, Circle.smul_def, smul_eq_mul]

/-- Mollification of the symbol preserves the `L^p` multiplier bound, for a continuous symbol.

This is the corrected form of `Work.KMTAreas.SupNorm.isLqMultiplierBound_mollify`: the extra
hypothesis `Continuous φ` is what makes the mollified symbol
`ψ ξ = ∫ b, ρ b * φ (ξ + b)` a genuine Bochner integral for every `ξ` and what makes the joint
integrand `(ξ,b) ↦ ρ b * φ (ξ+b) * 𝓕f ξ` integrable, so that Fubini gives the averaging identity
`T_ψ f = ∫ b, ρ b • T_{φ(·+b)} f`.  Minkowski's integral inequality for `eLpNorm`
(`Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite`, proved in the commons,
needs an extra `import Submission.Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite`)
together with `Work.KMTAreas.SupNorm.IsLqMultiplierBound_comp_add` (proved) then gives the bound
with the same constant `M`. -/
theorem isLqMultiplierBound_mollify_continuous {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    {φ : ℝ → ℂ} (hφc : Continuous φ) {M : NNReal} (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M)
    {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρnn : ∀ b, 0 ≤ ρ b)
    (hρ1 : ∫ b, ρ b = 1)
    {f : SchwartzMap ℝ ℂ} (hf : HasCompactSupport (fun ξ => FourierTransform.fourier (f : ℝ → ℂ) ξ)) :
    MeasureTheory.eLpNorm
        (Work.Analysis.IWMultiplier.contMulOp (fun ξ => ∫ b, (ρ b : ℂ) * φ (ξ + b)) (f : ℝ → ℂ))
        p MeasureTheory.volume
      ≤ ENNReal.ofReal (M : ℝ) * MeasureTheory.eLpNorm (f : ℝ → ℂ) p MeasureTheory.volume := by
  classical
  set Ψ : ℝ → ℂ := fun ξ => ∫ b, (ρ b : ℂ) * φ (ξ + b) with hΨ
  have hFfcont : Continuous fun ξ : ℝ => FourierTransform.fourier (f : ℝ → ℂ) ξ := by
    have hcont := (𝓕 f).continuous
    simpa only [SchwartzMap.fourier_coe] using hcont
  -- ## The averaging identity `T_Ψ f = ∫ b, ρ b • T_{φ(·+b)} f`
  have hkey : ∀ x : ℝ, contMulOp Ψ (f : ℝ → ℂ) x
      = ∫ b, (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x := by
    intro x
    -- write the multiplier as a double integral over the mollifying variable
    have hA : contMulOp Ψ (f : ℝ → ℂ) x
        = ∫ v, ∫ b, (Real.fourierChar (v * x) : ℂ)
            * ((ρ b : ℂ) * φ (v + b) * 𝓕 (f : ℝ → ℂ) v) := by
      rw [contMulOp_apply_eq_integral]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      simp only [hΨ]
      rw [← MeasureTheory.integral_mul_const (𝓕 (f : ℝ → ℂ) v)
            (fun b => (ρ b : ℂ) * φ (v + b))]
      rw [← MeasureTheory.integral_const_mul (Real.fourierChar (v * x) : ℂ)
            (fun b => ((ρ b : ℂ) * φ (v + b)) * 𝓕 (f : ℝ → ℂ) v)]
    -- Fubini, using that the integrand is continuous with compact support
    have hB : (∫ v, ∫ b, (Real.fourierChar (v * x) : ℂ)
            * ((ρ b : ℂ) * φ (v + b) * 𝓕 (f : ℝ → ℂ) v))
        = ∫ b, ∫ v, (Real.fourierChar (v * x) : ℂ)
            * ((ρ b : ℂ) * φ (v + b) * 𝓕 (f : ℝ → ℂ) v) := by
      apply integral_integral_swap_of_hasCompactSupport
      · have h1 : Continuous fun p : ℝ × ℝ => (Real.fourierChar (p.1 * x) : ℂ) :=
          continuous_fourierChar_coe.comp (by fun_prop)
        have h2 : Continuous fun p : ℝ × ℝ => ((ρ p.2 : ℝ) : ℂ) * φ (p.1 + p.2) :=
          (Complex.continuous_ofReal.comp (hρc.comp (by fun_prop))).mul
            (hφc.comp (by fun_prop))
        have h3 : Continuous fun p : ℝ × ℝ => 𝓕 (f : ℝ → ℂ) p.1 :=
          hFfcont.comp (by fun_prop)
        exact h1.mul (h2.mul h3)
      · apply HasCompactSupport.of_support_subset_isCompact
          (K := tsupport (fun ξ : ℝ => FourierTransform.fourier (f : ℝ → ℂ) ξ) ×ˢ tsupport ρ)
        · exact (show IsCompact
              (tsupport (fun ξ : ℝ => FourierTransform.fourier (f : ℝ → ℂ) ξ)) from hf).prod
            (show IsCompact (tsupport ρ) from hρs)
        · intro p hp
          rw [Set.mem_prod]
          refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
          · simp only [Function.mem_support] at hp ⊢
            intro h
            refine hp ?_
            change (Real.fourierChar (p.1 * x) : ℂ)
              * ((ρ p.2 : ℂ) * φ (p.1 + p.2) * 𝓕 (f : ℝ → ℂ) p.1) = 0
            simp [h]
          · simp only [Function.mem_support] at hp ⊢
            intro h
            refine hp ?_
            change (Real.fourierChar (p.1 * x) : ℂ)
              * ((ρ p.2 : ℂ) * φ (p.1 + p.2) * 𝓕 (f : ℝ → ℂ) p.1) = 0
            simp [h]
    -- identify the inner integral with the translated multiplier and pull out `ρ b`
    have hC : (∫ b, ∫ v, (Real.fourierChar (v * x) : ℂ)
            * ((ρ b : ℂ) * φ (v + b) * 𝓕 (f : ℝ → ℂ) v))
        = ∫ b, (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with b
      rw [contMulOp_apply_eq_integral]
      rw [show (fun v => (Real.fourierChar (v * x) : ℂ)
              * ((ρ b : ℂ) * φ (v + b) * 𝓕 (f : ℝ → ℂ) v))
          = fun v => (ρ b : ℂ)
              * ((Real.fourierChar (v * x) : ℂ) * (φ (v + b) * 𝓕 (f : ℝ → ℂ) v)) from by
        funext v; ring]
      rw [MeasureTheory.integral_const_mul]
    exact hA.trans (hB.trans hC)
  -- ## The joint measurability of `(b,x) ↦ ρ b * T_{φ(·+b)} f x`
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun b x : ℝ => (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x)
      (volume.prod volume) := by
    let G : ℝ × (ℝ × ℝ) → ℂ := fun q =>
      (Real.fourierChar (q.1 * q.2.2) : ℂ) * (φ (q.1 + q.2.1) * 𝓕 (f : ℝ → ℂ) q.1)
    have hGc : Continuous G := by
      have h1 : Continuous fun t : ℝ => (Real.fourierChar t : ℂ) := continuous_fourierChar_coe
      have h2 : Continuous fun q : ℝ × (ℝ × ℝ) => q.1 * q.2.2 := by fun_prop
      have h3 : Continuous fun q : ℝ × (ℝ × ℝ) => q.1 + q.2.1 := by fun_prop
      have h4 : Continuous fun q : ℝ × (ℝ × ℝ) => q.1 := by fun_prop
      have h5 : Continuous fun q : ℝ × (ℝ × ℝ) => (Real.fourierChar (q.1 * q.2.2) : ℂ) :=
        h1.comp h2
      have h6 : Continuous fun q : ℝ × (ℝ × ℝ) => φ (q.1 + q.2.1) := hφc.comp h3
      have h7 : Continuous fun q : ℝ × (ℝ × ℝ) => 𝓕 (f : ℝ → ℂ) q.1 := hFfcont.comp h4
      exact h5.mul (h6.mul h7)
    have hsm : StronglyMeasurable (fun p : ℝ × ℝ =>
        ∫ v, (Real.fourierChar (v * p.2) : ℂ) * (φ (v + p.1) * 𝓕 (f : ℝ → ℂ) v)) :=
      hGc.stronglyMeasurable.integral_prod_left'
    have hsm2 : StronglyMeasurable (fun p : ℝ × ℝ =>
        (ρ p.1 : ℂ)
          * ∫ v, (Real.fourierChar (v * p.2) : ℂ) * (φ (v + p.1) * 𝓕 (f : ℝ → ℂ) v)) :=
      ((Complex.continuous_ofReal.comp (hρc.comp (by fun_prop))).stronglyMeasurable).mul hsm
    rw [show (Function.uncurry fun b x : ℝ =>
            (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x)
        = fun p : ℝ × ℝ => (ρ p.1 : ℂ) * contMulOp (fun ξ => φ (ξ + p.1)) (f : ℝ → ℂ) p.2
        from rfl]
    rw [show (fun p : ℝ × ℝ =>
            (ρ p.1 : ℂ) * contMulOp (fun ξ => φ (ξ + p.1)) (f : ℝ → ℂ) p.2)
        = fun p : ℝ × ℝ => (ρ p.1 : ℂ)
            * ∫ v, (Real.fourierChar (v * p.2) : ℂ) * (φ (v + p.1) * 𝓕 (f : ℝ → ℂ) v) from by
      funext p; rw [contMulOp_apply_eq_integral]]
    exact hsm2.aestronglyMeasurable
  -- ## Minkowski's integral inequality
  have hMink := Commons.Analysis.Integral.eLpNorm_integral_le_lintegral_eLpNorm_sfinite
    (μ := volume) (ν := volume) (p := p) hp1
    (f := fun b x : ℝ => (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x) hmeas
  -- ## The total mass of the mollifier is `1`
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hlin : ∫⁻ b, ‖(ρ b : ℂ)‖ₑ = 1 := by
    have h1 : ∫⁻ b, ENNReal.ofReal (ρ b) = ENNReal.ofReal (∫ b, ρ b) :=
      (ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all volume hρnn)).symm
    have h2 : (fun b : ℝ => ‖(ρ b : ℂ)‖ₑ) = fun b => ENNReal.ofReal (ρ b) := by
      funext b
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hρnn b)]
    rw [h2, h1, hρ1, ENNReal.ofReal_one]
  have haemeas : AEMeasurable (fun b : ℝ => ‖(ρ b : ℂ)‖ₑ) volume :=
    ((Complex.continuous_ofReal.comp hρc).aemeasurable).enorm
  calc eLpNorm (contMulOp Ψ (f : ℝ → ℂ)) p volume
      = eLpNorm (fun x : ℝ => ∫ b, (ρ b : ℂ)
          * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x) p volume := by
        rw [show contMulOp Ψ (f : ℝ → ℂ)
            = fun x : ℝ => ∫ b, (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x
            from funext hkey]
    _ ≤ ∫⁻ b, eLpNorm (fun x : ℝ => (ρ b : ℂ)
          * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x) p volume := hMink
    _ = ∫⁻ b, ‖(ρ b : ℂ)‖ₑ
          * eLpNorm (contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ)) p volume := by
        apply lintegral_congr; intro b
        rw [show (fun x : ℝ => (ρ b : ℂ) * contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x)
            = (ρ b : ℂ) • contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) from by
          funext x; rw [Pi.smul_apply, smul_eq_mul]]
        rw [eLpNorm_const_smul]
    _ ≤ ∫⁻ b, ‖(ρ b : ℂ)‖ₑ
          * (ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) p volume) := by
        apply lintegral_mono; intro b
        exact mul_le_mul_right (IsLqMultiplierBound_comp_add hp1 hp2 h b f) _
    _ = (∫⁻ b, ‖(ρ b : ℂ)‖ₑ)
          * (ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) p volume) :=
        lintegral_mul_const'' _ haemeas
    _ = ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) p volume := by
        rw [hlin, one_mul]

end Work.KMTAreas.SupNorm
