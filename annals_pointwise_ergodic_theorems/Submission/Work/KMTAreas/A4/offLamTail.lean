import Mathlib
import Submission.Work.KMTAreas.A7.EtaMult
import Submission.Work.KMTAreas.A4.offTail
import Submission.Commons.Analysis.Fourier.dyadic_linearized_l3

set_option autoImplicit false

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Elementary `enorm` facts for complex numbers -/

theorem enorm_complex_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

theorem enorm_complex_of_nonneg {m : ℝ} (hm : 0 ≤ m) : ‖(m : ℂ)‖ₑ = ENNReal.ofReal m := by
  rw [enorm_complex_eq_ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]

theorem enorm_complex_pow_of_nonneg {m : ℝ} (hm : 0 ≤ m) (i : ℕ) :
    ‖((m : ℂ) ^ i)‖ₑ = ENNReal.ofReal (m ^ i) := by
  rw [enorm_complex_eq_ofReal_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hm]

/-! ## The explicit dilation form of the rescaled kernel -/

/-- `K_k = 𝓕⁻ η_{≤k}` is the dilation `x ↦ 2^k • ψ (2^k x)` of `ψ = 𝓕⁻ η`. -/
theorem etaMult_K_coe (k : ℤ) :
    ⇑(Work.KMTAreas.A7.etaMult_K k) = fun x : ℝ =>
      (((2 : ℝ) ^ k : ℝ) : ℂ) * (⇑(Work.KMTAreas.A7.etaMult_psiSch) ((2 : ℝ) ^ k * x)) := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h1 : ⇑(Work.KMTAreas.A7.etaMult_K k) = fun x : ℝ =>
      (((2 : ℝ) ^ k : ℝ) : ℂ) •
        FourierTransformInv.fourierInv Work.KMTContract.kmtEta ((2 : ℝ) ^ k * x) := by
    rw [show ⇑(Work.KMTAreas.A7.etaMult_K k)
        = FourierTransformInv.fourierInv (⇑(Work.KMTAreas.A7.etaMult_etaCutSch k)) from
      SchwartzMap.fourierInv_coe (Work.KMTAreas.A7.etaMult_etaCutSch k)]
    rw [show ⇑(Work.KMTAreas.A7.etaMult_etaCutSch k)
        = (fun θ : ℝ => Work.KMTContract.kmtEta (θ / (2 : ℝ) ^ k)) from
      funext (Work.KMTAreas.A7.etaMult_etaCutSch_coe k)]
    exact Work.KMTAreas.A7.fourierInv_comp_div Work.KMTContract.kmtEta hc
  rw [h1]
  funext x
  rw [← Work.KMTAreas.A7.etaMult_psiSch_coe, smul_eq_mul]

/-- The `i`-th derivative of a dilation picks up the factor `m ^ i`. -/
theorem iteratedDeriv_dilate (i : ℕ) (Ψ : ℝ → ℂ) (hΨ : ContDiff ℝ (i : ℕ∞) Ψ)
    (m : ℝ) (x : ℝ) :
    iteratedDeriv i (fun x : ℝ => (m : ℂ) * Ψ (m * x)) x
      = (m : ℂ) * ((m : ℂ) ^ i) * iteratedDeriv i Ψ (m * x) := by
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_smul (f := Ψ) hΨ m]
  simp only [Complex.real_smul, Complex.ofReal_pow]
  ring

/-! ## The iterated derivative of a Schwartz function is a Schwartz function -/

/-- The coercion of the `i`-fold iterate of `derivCLM` is the `i`-th iterated derivative. -/
theorem coe_iterate_derivCLM (i : ℕ) (f : SchwartzMap ℝ ℂ) :
    ⇑((SchwartzMap.derivCLM ℂ ℂ)^[i] f) = iteratedDeriv i ⇑f := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [show ⇑(SchwartzMap.derivCLM ℂ ℂ ((SchwartzMap.derivCLM ℂ ℂ)^[n] f))
          = deriv ⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] f) from rfl]
      rw [ih, iteratedDeriv_eq_iterate (n := n + 1) (f := ⇑f), Function.iterate_succ_apply',
        ← iteratedDeriv_eq_iterate (n := n) (f := ⇑f)]

/-! ## The tail integral of the dilated kernel -/

/-- Change of variables: the tail integral of the `i`-th derivative of the dilated kernel
`x ↦ m • Ψ (m x)` equals `m ^ i` times the tail integral of `Ψ^{(i)}`. -/
theorem setLIntegral_iteratedDeriv_dilate (i : ℕ) (Ψ : ℝ → ℂ) (hΨ : ContDiff ℝ (i : ℕ∞) Ψ)
    {m : ℝ} (hm : 0 < m) (R : ℝ) :
    ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|},
        ‖iteratedDeriv i (fun x : ℝ => (m : ℂ) * Ψ (m * x)) x‖ₑ
      = ENNReal.ofReal (m ^ i) *
        ∫⁻ u : ℝ in {u : ℝ | m * R ≤ |u|}, ‖iteratedDeriv i Ψ u‖ₑ := by
  have hmeas : Measurable (fun u : ℝ => ‖iteratedDeriv i Ψ u‖ₑ) :=
    (continuous_enorm.comp (ContDiff.continuous_iteratedDeriv' i hΨ)).measurable
  have hpt : ∀ x : ℝ,
      ‖iteratedDeriv i (fun x : ℝ => (m : ℂ) * Ψ (m * x)) x‖ₑ
        = (ENNReal.ofReal m * ENNReal.ofReal (m ^ i)) * ‖iteratedDeriv i Ψ (m * x)‖ₑ := by
    intro x
    rw [iteratedDeriv_dilate i Ψ hΨ m x]
    simp only [enorm_mul, enorm_complex_of_nonneg hm.le, enorm_complex_pow_of_nonneg hm.le]
  have hmulconst : ENNReal.ofReal m * ENNReal.ofReal (m ^ i) * ENNReal.ofReal (m⁻¹)
      = ENNReal.ofReal (m ^ i) := by
    rw [← ENNReal.ofReal_mul hm.le, ← ENNReal.ofReal_mul (mul_nonneg hm.le (pow_nonneg hm.le i))]
    congr 1
    rw [mul_comm m (m ^ i), mul_inv_cancel_right₀ hm.ne']
  calc ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|},
        ‖iteratedDeriv i (fun x : ℝ => (m : ℂ) * Ψ (m * x)) x‖ₑ
      = ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|},
          (ENNReal.ofReal m * ENNReal.ofReal (m ^ i)) * ‖iteratedDeriv i Ψ (m * x)‖ₑ :=
        lintegral_congr hpt
    _ = (ENNReal.ofReal m * ENNReal.ofReal (m ^ i)) *
          ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|}, ‖iteratedDeriv i Ψ (m * x)‖ₑ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = (ENNReal.ofReal m * ENNReal.ofReal (m ^ i)) *
          (ENNReal.ofReal (m⁻¹) *
            ∫⁻ u : ℝ in {u : ℝ | R * m ≤ |u|}, ‖iteratedDeriv i Ψ u‖ₑ) := by
        rw [Commons.Analysis.Fourier.dl3_setLIntegral_comp_mul_left m R hm _ hmeas]
    _ = ENNReal.ofReal (m ^ i) *
          ∫⁻ u : ℝ in {u : ℝ | R * m ≤ |u|}, ‖iteratedDeriv i Ψ u‖ₑ := by
        rw [← mul_assoc, hmulconst]
    _ = ENNReal.ofReal (m ^ i) *
          ∫⁻ u : ℝ in {u : ℝ | m * R ≤ |u|}, ‖iteratedDeriv i Ψ u‖ₑ := by
        rw [mul_comm R m]

/-! ## The main estimate -/

theorem offLamTail_of_tailBound
    (hTail : ∀ (f : SchwartzMap ℝ ℂ) (N : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      ∫⁻ y : ℝ in {y : ℝ | R ≤ |y|}, ‖f y‖ₑ
        ≤ ENNReal.ofReal (C * (max R 1) ^ (-(N : ℝ))))
    (i N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (R : ℝ), 0 ≤ R →
      ∫⁻ x : ℝ in {x | R ≤ |x|},
          ‖iteratedDeriv i ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ
        ≤ ENNReal.ofReal (C * (((2 : ℝ) ^ k) ^ i) *
            (max ((2 : ℝ) ^ k * R) 1) ^ (-(N : ℝ))) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    hTail ((SchwartzMap.derivCLM ℂ ℂ)^[i] Work.KMTAreas.A7.etaMult_psiSch) N
  refine ⟨C₁, hC₁pos, ?_⟩
  intro k R hR
  have hmpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hψ : ContDiff ℝ (i : ℕ∞) (⇑(Work.KMTAreas.A7.etaMult_psiSch)) :=
    Work.KMTAreas.A7.etaMult_psiSch.smooth i
  have hkey : ∫⁻ x : ℝ in {x : ℝ | R ≤ |x|},
        ‖iteratedDeriv i ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ
      = ENNReal.ofReal (((2 : ℝ) ^ k) ^ i) *
        ∫⁻ u : ℝ in {u : ℝ | (2 : ℝ) ^ k * R ≤ |u|},
          ‖iteratedDeriv i (⇑(Work.KMTAreas.A7.etaMult_psiSch)) u‖ₑ := by
    rw [show (fun x : ℝ =>
          ‖iteratedDeriv i ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ)
        = (fun x : ℝ => ‖iteratedDeriv i (fun x : ℝ =>
            (((2 : ℝ) ^ k : ℝ) : ℂ) *
              (⇑(Work.KMTAreas.A7.etaMult_psiSch) ((2 : ℝ) ^ k * x))) x‖ₑ) from by
      rw [etaMult_K_coe]]
    exact setLIntegral_iteratedDeriv_dilate i (⇑(Work.KMTAreas.A7.etaMult_psiSch)) hψ hmpos R
  rw [hkey]
  have hb := hC₁ ((2 : ℝ) ^ k * R) (by positivity)
  rw [coe_iterate_derivCLM] at hb
  calc ENNReal.ofReal (((2 : ℝ) ^ k) ^ i) *
        ∫⁻ u : ℝ in {u : ℝ | (2 : ℝ) ^ k * R ≤ |u|},
          ‖iteratedDeriv i (⇑(Work.KMTAreas.A7.etaMult_psiSch)) u‖ₑ
      ≤ ENNReal.ofReal (((2 : ℝ) ^ k) ^ i) *
          ENNReal.ofReal (C₁ * (max ((2 : ℝ) ^ k * R) 1) ^ (-(N : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal ((((2 : ℝ) ^ k) ^ i) *
          (C₁ * (max ((2 : ℝ) ^ k * R) 1) ^ (-(N : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (C₁ * (((2 : ℝ) ^ k) ^ i) *
          (max ((2 : ℝ) ^ k * R) 1) ^ (-(N : ℝ))) := by
        congr 1
        ring

theorem offLamTail (i N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (R : ℝ), 0 ≤ R →
      ∫⁻ x : ℝ in {x | R ≤ |x|},
          ‖iteratedDeriv i ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ
        ≤ ENNReal.ofReal (C * (((2 : ℝ) ^ k) ^ i) *
            (max ((2 : ℝ) ^ k * R) 1) ^ (-(N : ℝ))) :=
  offLamTail_of_tailBound (fun f N => offTail f N) i N

end

end Work.KMTAreas.A4
