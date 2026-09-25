import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs

/-!
# Analytic facts about the general-`P` window model

`𝓕⁻φ(D·)(w) = D⁻¹ 𝓕⁻φ(w/D)`, the explicit formula

`𝓕⁻(genBetaAmp)(w) = Σ_{j ≡ -z (q)} g_j · D⁻¹ · 𝓕⁻φ((w+j+z)/D)`

for the inverse transform of the slice amplitude, the resulting decay and integrability, and the
dilation identity for `genBlock`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- Dilation of the inverse Fourier transform: `𝓕⁻(φ(D·))(w) = D⁻¹ 𝓕⁻φ(w/D)`. -/
theorem fourierInv_phi_dilate (D : ℝ) (hD : 0 < D) (φ : ℝ → ℂ) (u : ℝ) :
    FourierTransformInv.fourierInv (fun β : ℝ => φ (D * β)) u
      = ((D : ℂ))⁻¹ * FourierTransformInv.fourierInv φ (u / D) := by
  rw [Commons.Analysis.ExponentialSums.fourierInv_eq_integral,
    Commons.Analysis.ExponentialSums.fourierInv_eq_integral]
  have hDc : ((D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hstep : (∫ β : ℝ, φ (D * β) * Complex.exp (2 * Real.pi * Complex.I * u * β))
      = ∫ β : ℝ, (fun γ : ℝ => φ γ *
          Complex.exp (2 * Real.pi * Complex.I * (u/D) * γ)) (D * β) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun β => ?_))
    simp only []
    congr 1
    rw [show D * β = β * D by ring]
    congr 1
    push_cast
    field_simp
  rw [hstep]
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun γ : ℝ =>
    φ γ * Complex.exp (2 * Real.pi * Complex.I * (u/D) * γ)) D]
  rw [show |(D:ℝ)⁻¹| = D⁻¹ by rw [abs_of_pos (inv_pos.mpr hD)], Complex.real_smul]
  push_cast
  ring

/-- The slice amplitude is integrable (it is continuous and compactly supported). -/
theorem integrable_genBetaAmp (q : ℕ) {D : ℝ} (hD : 0 < D) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) : Integrable (genBetaAmp q D φ g s z) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_genBetaAmp q D hφ g s z) ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/(2*D))) (1/(2*D)))
    isCompact_Icc (fun β hβ => ?_)
  rw [Function.mem_support] at hβ
  by_contra hcon
  exact hβ (genBetaAmp_eq_zero_of_notMem q hD hφs g s z hcon)

/-- The full amplitude of the `k`-th block is integrable. -/
theorem integrable_genAmpF (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) : Integrable (genAmpF P k q D φ g s z) := by
  have hbdd : ∀ β : ℝ, ‖starRingEnd ℂ (polyProfile P (2^k) β)‖ ≤ 1 := by
    intro β
    rw [starRingEnd_apply, norm_star]
    exact norm_polyProfile_le_one P (2^k) β
  refine Integrable.mono' ((integrable_genBetaAmp q hD hφ hφs g s z).norm)
    ((continuous_genAmpF P k q D hφ g s z).aestronglyMeasurable) ?_
  filter_upwards with β
  rw [genAmpF, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hbdd β)

/-- Explicit formula for the inverse transform of the slice amplitude. -/
theorem fourierInv_genBetaAmp_eq (q : ℕ) (D : ℝ) (hD : 0 < D) {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ)
    (w : ℝ) :
    FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) w
      = ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          g j * (((D : ℂ))⁻¹ *
            FourierTransformInv.fourierInv φ ((w + ((j + z : ℤ) : ℝ)) / (D : ℝ))) := by
  rw [Commons.Analysis.ExponentialSums.fourierInv_eq_integral]
  have hamp : ∀ β : ℝ, genBetaAmp q D φ g s z β
      = ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          φ (D * β) * (g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ)))) := by
    intro β
    rw [genBetaAmp, Finset.mul_sum]
  have hfun : (fun β : ℝ => genBetaAmp q D φ g s z β * Complex.exp (2 * Real.pi * Complex.I * w * β))
      = fun β : ℝ => ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          (φ (D * β) * (g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ))))
            * Complex.exp (2 * Real.pi * Complex.I * w * β)) := by
    funext β; rw [hamp β, Finset.sum_mul]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hkey : ∀ β : ℝ,
        φ (D * β) * (g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ))))
          * Complex.exp (2 * Real.pi * Complex.I * w * β)
        = g j * (φ (D * β) * Complex.exp (2 * Real.pi * Complex.I * ((w + ((j+z : ℤ) : ℝ)) : ℝ) * β)) := by
      intro β
      have h1 : Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ)))
          * Complex.exp (2 * Real.pi * Complex.I * w * β)
          = Complex.exp (2 * Real.pi * Complex.I * (((w + ((j+z : ℤ) : ℝ)) : ℝ) : ℂ) * (β : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [show φ (D * β) * (g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ))))
            * Complex.exp (2 * Real.pi * Complex.I * w * β)
          = g j * (φ (D * β) * (Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ)))
            * Complex.exp (2 * Real.pi * Complex.I * w * β))) by ring, h1]
    rw [show (∫ β : ℝ, φ (D * β) * (g j * Complex.exp (2 * Real.pi * Complex.I * (((j : ℂ) + (z : ℂ)) * (β : ℂ))))
            * Complex.exp (2 * Real.pi * Complex.I * w * β))
        = ∫ β : ℝ, g j * (φ (D * β) *
            Complex.exp (2 * Real.pi * Complex.I * ((w + ((j+z : ℤ) : ℝ)) : ℝ) * β)) from
      integral_congr_ae (Filter.Eventually.of_forall hkey)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ β : ℝ, φ (D * β) * Complex.exp (2 * Real.pi * Complex.I * ((w + ((j+z : ℤ) : ℝ)) : ℝ) * β))
        = FourierTransformInv.fourierInv (fun β : ℝ => φ (D * β)) (w + ((j+z : ℤ) : ℝ)) from by
      rw [Commons.Analysis.ExponentialSums.fourierInv_eq_integral]]
    exact fourierInv_phi_dilate D hD φ (w + ((j+z : ℤ) : ℝ))
  · intro j hj
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(1/(2*D))) (1/(2*D)))
      isCompact_Icc (fun β hβ => ?_)
    rw [Function.mem_support] at hβ
    by_contra hcon
    rw [phi_dilate_eq_zero hD hφs hcon] at hβ
    exact hβ (by ring)


/-! ## Decay and integrability of the inverse transform of the slice amplitude -/

private lemma dilate_window_ineq {D c : ℝ} (hD : 0 < D) (h1D : 1 ≤ D) (w : ℝ) :
    D / (D^2 + (w + c)^2) ≤ (2 + 2*c^2) * (D / (D^2 + w^2)) := by
  have h1 : (0:ℝ) < D^2 + (w+c)^2 := by positivity
  have h2 : (0:ℝ) < D^2 + w^2 := by positivity
  have hw : w^2 ≤ 2*(w+c)^2 + 2*c^2 := by nlinarith [sq_nonneg (w + 2*c)]
  have hD2 : 1 ≤ D^2 := by nlinarith
  have hc : 2*c^2 ≤ D^2 * (2*c^2) := by nlinarith [sq_nonneg c, hD2]
  have hmain : D^2 + w^2 ≤ (2 + 2*c^2) * (D^2 + (w+c)^2) := by
    nlinarith [hw, hc, sq_nonneg c, sq_nonneg (w + c), hD2]
  rw [show (2 + 2*c^2) * (D / (D^2 + w^2)) = ((2 + 2*c^2) * D) / (D^2 + w^2) by ring,
    div_le_div_iff₀ h1 h2]
  nlinarith [hmain, hD]

private lemma inv_one_add_sq_div {D u : ℝ} (hD : 0 < D) :
    D⁻¹ * (1 + (u/D)^2)⁻¹ = D / (D^2 + u^2) := by
  have h : (1 + (u/D)^2) = (D^2 + u^2)/D^2 := by
    field_simp
  rw [h, inv_div, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

/-- A single dilated term of the inverse transform decays like `D/(D²+w²)`. -/
private lemma fourierInv_dilated_term_le {φ : ℝ → ℂ} {C₀ D c w : ℝ} (hD : 0 < D) (h1D : 1 ≤ D)
    (hC₀pos : 0 < C₀)
    (hC₀ : ∀ u : ℝ, ‖FourierTransformInv.fourierInv φ u‖ ≤ C₀ * (1 + u^2)⁻¹) :
    ‖((D : ℂ))⁻¹ * FourierTransformInv.fourierInv φ ((w + c)/D)‖
      ≤ C₀ * (2 + 2*c^2) * (D / (D^2 + w^2)) := by
  have hDnorm : ‖((D : ℂ))⁻¹‖ = D⁻¹ := by
    have hsm : ((D : ℂ))⁻¹ = ((D⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hsm]
    have hsq : ‖(((D⁻¹ : ℝ)) : ℂ)‖^2 = (D⁻¹)^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    have hnn : (0:ℝ) ≤ ‖(((D⁻¹ : ℝ)) : ℂ)‖ := norm_nonneg _
    have hpos : (0:ℝ) < D⁻¹ := inv_pos.mpr hD
    nlinarith
  rw [norm_mul, hDnorm]
  calc D⁻¹ * ‖FourierTransformInv.fourierInv φ ((w + c)/D)‖
      ≤ D⁻¹ * (C₀ * (1 + ((w + c)/D)^2)⁻¹) :=
        mul_le_mul_of_nonneg_left (hC₀ _) (inv_nonneg.mpr hD.le)
    _ = C₀ * (D / (D^2 + (w + c)^2)) := by
        rw [← inv_one_add_sq_div hD]; ring
    _ ≤ C₀ * ((2 + 2*c^2) * (D / (D^2 + w^2))) :=
        mul_le_mul_of_nonneg_left (dilate_window_ineq hD h1D w) hC₀pos.le
    _ = C₀ * (2 + 2*c^2) * (D / (D^2 + w^2)) := by ring

/-- Pointwise decay of the inverse transform of the slice amplitude: it is `O(D/(D²+w²))`. -/
theorem fourierInv_genBetaAmp_le (q : ℕ) {D : ℝ} (hD : 0 < D) (h1D : 1 ≤ D) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ,
      ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) w‖ ≤ C * (D / (D^2 + w^2)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.ExponentialSums.exists_decay_fourierInv
      (Commons.Analysis.ExponentialSums.hasCompactSupport_of_Icc hφs) hφ
  refine ⟨(∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
      ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2))) + 1, by positivity, fun w => ?_⟩
  rw [fourierInv_genBetaAmp_eq q D hD hφ.continuous hφs g s z w]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
      ‖g j * (((D : ℂ))⁻¹ *
        FourierTransformInv.fourierInv φ ((w + ((j + z : ℤ) : ℝ)) / (D : ℝ)))‖
      ≤ ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2)) * (D / (D^2 + w^2)) := by
    intro j hj
    rw [norm_mul]
    calc ‖g j‖ * ‖((D : ℂ))⁻¹ *
          FourierTransformInv.fourierInv φ ((w + ((j + z : ℤ) : ℝ)) / (D : ℝ))‖
        ≤ ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2) * (D / (D^2 + w^2))) :=
          mul_le_mul_of_nonneg_left (fourierInv_dilated_term_le hD h1D hC₀pos hC₀)
            (norm_nonneg _)
      _ = ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2)) * (D / (D^2 + w^2)) := by ring
  calc ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
        ‖g j * (((D : ℂ))⁻¹ *
          FourierTransformInv.fourierInv φ ((w + ((j + z : ℤ) : ℝ)) / (D : ℝ)))‖
      ≤ ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2)) * (D / (D^2 + w^2)) :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2))) * (D / (D^2 + w^2)) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2)) + 1) * (D / (D^2 + w^2)) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · have hnn : (0:ℝ) ≤ ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
              ‖g j‖ * (C₀ * (2 + 2 * (((j + z : ℤ) : ℝ))^2)) := by positivity
          linarith
        · positivity

/-- The inverse transform of the slice amplitude is integrable. -/
theorem integrable_fourierInv_genBetaAmp (q : ℕ) {D : ℝ} (hD : 0 < D) (h1D : 1 ≤ D)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Integrable (FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)) := by
  obtain ⟨C, hCpos, hC⟩ := fourierInv_genBetaAmp_le q hD h1D hφ hφs g s z
  have hDne : (D:ℝ) ≠ 0 := ne_of_gt hD
  have hbase : Integrable (fun t : ℝ => (1 + t^2)⁻¹) := integrable_inv_one_add_sq
  have hscale : Integrable (fun w : ℝ => (1 + (w * D⁻¹)^2)⁻¹) :=
    hbase.comp_mul_right' (inv_ne_zero hDne)
  refine Integrable.mono' (hscale.const_mul (C / D)) ?_ ?_
  · exact (Commons.Analysis.ExponentialSums.continuous_fourierInv
      (integrable_genBetaAmp q hD hφ.continuous hφs g s z)).aestronglyMeasurable
  · filter_upwards with w
    have h := hC w
    have heq : C * (D / (D^2 + w^2)) = C / D * (1 + (w * D⁻¹)^2)⁻¹ := by
      have h2 : (1 + (w * D⁻¹)^2) = (D^2 + w^2)/D^2 := by
        field_simp
      rw [h2, inv_div]
      field_simp
    rw [heq] at h
    exact h

/-! ## The dilation identity for the block, and finiteness of the dilation maximal function -/

/-- The inverse transform of the full block amplitude is the dilation average of `𝓕⁻genBetaAmp`. -/
theorem fourierInv_genAmpF_eq (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (y : ℝ) :
    FourierTransformInv.fourierInv (genAmpF P k q D φ g s z) y
      = ∫ t in (0:ℝ)..1, FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          (y - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t)) := by
  have hG : Integrable (genBetaAmp q D φ g s z) :=
    integrable_genBetaAmp q hD hφ.continuous hφs g s z
  have hGi : Integrable (FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)) :=
    integrable_fourierInv_genBetaAmp q hD h1D hφ hφs g s z
  have hfun : genAmpF P k q D φ g s z
      = fun β => genBetaAmp q D φ g s z β * (starRingEnd ℂ) (polyProfile P (2^k) β) := rfl
  have := polyProfile_fourier_dilation P (2^k) (G := genBetaAmp q D φ g s z) hG hGi y
  rw [hfun]
  exact this

/-- **The dilation identity for the block**: `genBlock` is the `q`-multiple dilation average of
`𝓕⁻genBetaAmp` along the polynomial values `P(2^k s)`. -/
theorem genBlock_dilation (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (x : ℝ) :
    genBlock P k q D φ g s z x
      = (q : ℂ) * ∫ t in (0:ℝ)..1, FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          ((q:ℝ) * x - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * t)) := by
  rw [genBlock, fourierInv_genAmpF_eq P k q hD h1D hφ hφs g s z ((q:ℝ) * x)]

/-- The `D/(D²+u²)` envelope is integrable. -/
private lemma integrable_window_envelope {D : ℝ} (hD : 0 < D) :
    Integrable (fun u : ℝ => D / (D^2 + u^2)) := by
  have hDne : (D:ℝ) ≠ 0 := ne_of_gt hD
  have hfun : (fun u : ℝ => D / (D^2 + u^2))
      = fun u : ℝ => D⁻¹ * (1 + (u * D⁻¹)^2)⁻¹ := by
    funext u
    have h : (1 + (u * D⁻¹)^2) = (D^2 + u^2)/D^2 := by field_simp
    rw [h, inv_div]
    field_simp
  rw [hfun]
  exact (integrable_inv_one_add_sq.comp_mul_right' (inv_ne_zero hDne)).const_mul _

/-- The `L^p`-norm of the decay envelope is finite for `p > 1`. -/
theorem lintegral_enorm_fourierInv_genBetaAmp_rpow_lt_top (q : ℕ) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) {p : ℝ} (hp : 1 < p) :
    ∫⁻ u : ℝ, ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) u‖ₑ ^ p < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := fourierInv_genBetaAmp_le q hD h1D hφ hφs g s z
  have henv : Integrable (fun u : ℝ => D / (D^2 + u^2)) := integrable_window_envelope hD
  have hfin : ∫⁻ u : ℝ, ENNReal.ofReal (D / (D^2 + u^2)) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal henv
      (Filter.Eventually.of_forall (fun u => by positivity))]
    exact ENNReal.ofReal_lt_top
  have h1D' : (0:ℝ) < D := hD
  have hpoint : ∀ u : ℝ, ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) u‖ₑ ^ p
      ≤ ENNReal.ofReal (C^p) * ENNReal.ofReal (D / (D^2 + u^2)) := by
    intro u
    have hy1 : D / (D^2 + u^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have hCy : (0:ℝ) ≤ C * (D / (D^2 + u^2)) := by positivity
    have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
    calc ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) u‖ₑ ^ p
        ≤ ENNReal.ofReal (C * (D / (D^2 + u^2))) ^ p := by
          refine ENNReal.rpow_le_rpow ?_ hp0.le
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hC u)
      _ = ENNReal.ofReal ((C * (D / (D^2 + u^2)))^p) :=
          ENNReal.ofReal_rpow_of_nonneg hCy hp0.le
      _ = ENNReal.ofReal (C^p) * ENNReal.ofReal ((D / (D^2 + u^2))^p) := by
          rw [Real.mul_rpow hCpos.le (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hCpos.le p)]
      _ ≤ ENNReal.ofReal (C^p) * ENNReal.ofReal (D / (D^2 + u^2)) := by
          gcongr
          calc (D / (D^2 + u^2))^p ≤ (D / (D^2 + u^2))^1 :=
                Real.rpow_le_rpow_of_exponent_ge (by positivity) hy1 hp.le
            _ = D / (D^2 + u^2) := Real.rpow_one _
  refine lt_of_le_of_lt (lintegral_mono hpoint) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := C^p)) hfin

/-- The identification underlying Bourgain's (7.22)–(7.28): at `qx`, `𝓕⁻genBetaAmp` is `1/q` times
the lattice-dilated kernel applied to the residue slice. -/
theorem fourierInv_genBetaAmp_qx (q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) (x : ℝ) :
    FourierTransformInv.fourierInv (genBetaAmp q D φ g s z) ((q:ℝ) * x)
      = ((q:ℂ))⁻¹ * ∑ j ∈ s.filter (fun j => (q : ℤ) ∣ (z + j)),
          g j * (((q:ℝ)/D) * FourierTransformInv.fourierInv φ
            (((q:ℝ)/D) * (x + ((j+z : ℤ) : ℝ)/(q:ℝ)))) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hDc : ((D:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hqc : ((q:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hqR
  rw [fourierInv_genBetaAmp_eq q D hD hφ hφs g s z ((q:ℝ) * x), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have harg : ((q:ℝ) * x + ((j+z : ℤ) : ℝ)) / (D:ℝ)
      = ((q:ℝ)/D) * (x + ((j+z : ℤ) : ℝ)/(q:ℝ)) := by
    field_simp
  rw [harg]
  have hcoef : ((D:ℂ))⁻¹ = ((q:ℂ))⁻¹ * ((((q:ℝ)/D : ℝ)) : ℂ) := by
    push_cast
    field_simp
    rw [div_self (Nat.cast_ne_zero.mpr (ne_of_gt hq))]
  rw [hcoef]
  push_cast
  ring

/-- The support of the block amplitude: it vanishes outside the band `|β| ≤ 1/(2D)`. -/
theorem genAmpF_eq_zero_of_notMem (P : Polynomial ℤ) (k : ℕ) (q : ℕ) {D : ℝ} (hD : 0 < D)
    {φ : ℝ → ℂ} (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) {β : ℝ}
    (hβ : β ∉ Set.Icc (-(1/(2*D))) (1/(2*D))) : genAmpF P k q D φ g s z β = 0 := by
  rw [genAmpF, genBetaAmp_eq_zero_of_notMem q hD hφs g s z hβ, zero_mul]




/-- Decay of the inverse transform of the full block amplitude. -/
theorem fourierInv_genAmpF_le (P : Polynomial ℤ) (k q : ℕ) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ‖FourierTransformInv.fourierInv (genAmpF P k q D φ g s z) u‖
        ≤ C * (D / (D^2 + u^2)) := by
  obtain ⟨Cψ, hCψpos, hCψ⟩ := fourierInv_genBetaAmp_le q hD h1D hφ hφs g s z
  obtain ⟨M, hM0, hM⟩ := exists_eval_bound_Ioc P (2^k)
  refine ⟨Cψ * (2 + 2 * M^2), by positivity, fun u => ?_⟩
  rw [fourierInv_genAmpF_eq P k q hD h1D hφ hφs g s z u]
  have hpt : ∀ σ ∈ Set.uIoc (0:ℝ) 1,
      ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
        (u - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))‖
      ≤ Cψ * (2 + 2 * M^2) * (D / (D^2 + u^2)) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hσ
    have hσM := hM σ hσ
    have hineq : D / (D^2 + (u - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2)
        ≤ (2 + 2 * ((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2) * (D / (D^2 + u^2)) := by
      have := dilate_window_ineq (D := D) (c := -((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ)))
        hD h1D u
      rw [show u + -((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))
          = u - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ) by ring] at this
      simpa only [neg_sq] using this
    have hKM : (2 + 2 * ((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2) ≤ 2 + 2 * M^2 := by
      have hs : ((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2 ≤ M^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hσM 2
      linarith
    calc ‖FourierTransformInv.fourierInv (genBetaAmp q D φ g s z)
          (u - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))‖
        ≤ Cψ * (D / (D^2 + (u - (toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2)) := hCψ _
      _ ≤ Cψ * ((2 + 2 * ((toRealPoly P).eval (((2^k : ℕ) : ℝ) * σ))^2) * (D / (D^2 + u^2))) :=
          mul_le_mul_of_nonneg_left hineq hCψpos.le
      _ ≤ Cψ * ((2 + 2 * M^2) * (D / (D^2 + u^2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hKM (by positivity)) hCψpos.le
      _ = Cψ * (2 + 2 * M^2) * (D / (D^2 + u^2)) := by ring
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := Cψ * (2 + 2 * M^2) * (D / (D^2 + u^2))) hpt
  refine le_trans hmain (le_of_eq ?_)
  rw [sub_zero, abs_one, mul_one]




/-- Integrability of the `k`-th block of the `z`-slice. -/
theorem integrable_genBlock (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Integrable (genBlock P k q D φ g s z) := by
  obtain ⟨C, hCpos, hC⟩ := fourierInv_genAmpF_le P k q hD h1D hφ hφs g s z
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hbdd : Integrable (fun x : ℝ => (q:ℝ) * C * (D / (D^2 + ((q:ℝ)*x)^2))) := by
    have hcomp : Integrable (fun x : ℝ => D / (D^2 + ((q:ℝ)*x)^2)) :=
      (integrable_window_envelope hD).comp_mul_left' hqR.ne'
    exact hcomp.const_mul ((q:ℝ) * C)
  have hcont : Continuous (genBlock P k q D φ g s z) := by
    rw [show genBlock P k q D φ g s z
        = fun x : ℝ => (q:ℂ) * FourierTransformInv.fourierInv
            (genAmpF P k q D φ g s z) ((q:ℝ)*x) from rfl]
    exact continuous_const.mul
      ((Commons.Analysis.ExponentialSums.continuous_fourierInv
        (integrable_genAmpF P k q hD hφ.continuous hφs g s z)).comp (by fun_prop))
  refine Integrable.mono' hbdd hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [show genBlock P k q D φ g s z x
      = (q:ℂ) * FourierTransformInv.fourierInv (genAmpF P k q D φ g s z) ((q:ℝ)*x) from rfl,
    norm_mul, norm_natCast]
  calc (q:ℝ) * ‖FourierTransformInv.fourierInv (genAmpF P k q D φ g s z) ((q:ℝ)*x)‖
      ≤ (q:ℝ) * (C * (D / (D^2 + ((q:ℝ)*x)^2))) :=
        mul_le_mul_of_nonneg_left (hC ((q:ℝ)*x)) (by positivity : (0:ℝ) ≤ (q:ℝ))
    _ = (q:ℝ) * C * (D / (D^2 + ((q:ℝ)*x)^2)) := by ring

/-- Continuity of the `k`-th block of the `z`-slice. -/
theorem continuous_genBlock' (P : Polynomial ℤ) (k q : ℕ) (hq : 0 < q) {D : ℝ} (hD : 0 < D)
    (h1D : 1 ≤ D) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0)
    (g : ℤ → ℂ) (s : Finset ℤ) (z : ℤ) :
    Continuous (genBlock P k q D φ g s z) := by
  rw [show genBlock P k q D φ g s z
      = fun x : ℝ => (q:ℂ) * FourierTransformInv.fourierInv
          (genAmpF P k q D φ g s z) ((q:ℝ)*x) from rfl]
  exact continuous_const.mul
    ((Commons.Analysis.ExponentialSums.continuous_fourierInv
      (integrable_genAmpF P k q hD hφ.continuous hφs g s z)).comp (by fun_prop))

end Work.BourgainPlan.Maximal
