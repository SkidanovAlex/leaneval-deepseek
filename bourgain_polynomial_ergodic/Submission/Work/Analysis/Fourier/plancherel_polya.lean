/-
# Plancherel--Pólya as an *equality*: the samples of a band-limited function

For `F ∈ L²(ℝ)` whose (a.e.) support lies in the Nyquist band `[-1/2, 1/2]`, the samples of its
inverse Fourier transform `h = 𝓕⁻ F` satisfy

  `Σ_m ‖h m‖² = ∫_ℝ ‖F‖²`,

**exactly**, with **no `L¹` hypothesis on `h`** (this is the plancherel–Pólya sampling identity; the
published lattice comparisons `lattice_sup_le_integral_sup_band_limited` /
`..._rpow` all need `Integrable (h j)`, which fails for the *sharp* arc cutoff of the corpus's
major-arc model).

Proof:  (i) `F` is compactly supported and `L²`, hence `L¹`, so `h = 𝓕⁻ F` is the *continuous*
inverse Fourier integral and `h m = ∫_ℝ F(ξ)e^{2πi m ξ}dξ`;  (ii) since `F` vanishes a.e. off the
band, that is (the conjugate of) the Fourier coefficient of `F` on the interval `[-1/2,1/2]`, so
Parseval for the Fourier coefficients (`hasSum_sq_fourierCoeffOn`) gives
`Σ_m ‖h m‖² = ∫_{[-1/2,1/2]} ‖F‖²`;  (iii) that equals `∫_ℝ‖F‖²` because `F` vanishes off the band.

⚠ **This settles the `p = 2` lattice comparison only.**  It does *not* give the `ℓ^p` comparison
`Σ_m ‖h m‖^p ≲ ∫_ℝ ‖h‖^p` for `p < 2`: the tempting interpolation
`Σ_m |h m|^p ≤ (sup|h|)^{p-2} Σ_m |h m|²` is **false** for `p < 2` (the map `t ↦ t^{p-2}` is
decreasing, so `|h m| ≤ sup|h|` gives the *opposite* inequality; counterexample `h(0)=1`,
`h(1)=1/2`, `p = 3/2`).  The `ℓ^p` comparison needs instead the *weighted pointwise bound*
`‖h x‖ ≤ A ∫ ‖h y‖ (1+‖x-y‖)^{-N}` — for which the published commons lemma
`Commons.Analysis.Fourier.bandlimited_decaying_kernel_bound` again requires `Integrable f`, i.e. the
very `L¹` hypothesis that fails here.  The missing brick is therefore the `L¹`-free (i.e. `L²`-only)
reproducing/decaying-kernel bound, equivalently the `L²·L¹` Fourier multiplier identity
`𝓕(h * ψ) = 𝓕h · 𝓕ψ` for `h ∈ L²`, `ψ ∈ L¹` (Mathlib has the product formula only for `L¹ * L¹`).
-/

import Mathlib
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

open MeasureTheory Set Finset
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

set_option maxHeartbeats 800000

/-- Plancherel's theorem on `ℝ`, in `ℝ≥0∞`-norm form: `‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ`. -/
lemma enorm_fourierInv_real (Y : Lp ℂ 2 (volume : Measure ℝ)) : ‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ := by
  have h : ‖𝓕⁻ Y‖ = ‖Y‖ := by
    have := MeasureTheory.Lp.norm_fourier_eq (E := ℝ) (𝓕⁻ Y)
    rw [FourierInvPair.fourier_fourierInv_eq] at this
    exact this.symm
  rw [MeasureTheory.Lp.enorm_def, MeasureTheory.Lp.enorm_def]
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def] at h
  rcases (ENNReal.toReal_eq_toReal_iff _ _).mp h with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h'
  · exact absurd h2 (MeasureTheory.Lp.eLpNorm_ne_top Y)
  · exact absurd h1 (MeasureTheory.Lp.eLpNorm_ne_top _)

/-- `‖g‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2` for `g : Lp ℂ 2 (volume : Measure ℝ)`. -/
lemma lp_enorm_sq_eq_lintegral_real (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖g‖ₑ ^ (2 : ℝ) = ∫⁻ x : ℝ, ‖(g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by
  rw [MeasureTheory.Lp.enorm_def,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (MeasureTheory.Lp.aestronglyMeasurable g)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2, show (1 : ℝ) / (2 : ℝ) = 1 / 2 by norm_num, ← ENNReal.rpow_mul]
  norm_num

/-- **Plancherel's theorem** in `lintegral` form on `ℝ`, for an `L¹ ∩ L²` function. -/
lemma lintegral_norm_sq_fourierInv_real {Ψ : ℝ → ℂ} (h1 : MemLp Ψ 1 (volume : Measure ℝ))
    (h2 : MemLp Ψ 2 (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ‖𝓕⁻ Ψ x‖ₑ ^ (2 : ℝ) = ∫⁻ a : ℝ, ‖Ψ a‖ₑ ^ (2 : ℝ) := by
  have hcoe := fourierInv_toLp_ae_eq_fourierInv h1 h2
  have hL : ∫⁻ x : ℝ, ‖𝓕⁻ Ψ x‖ₑ ^ (2 : ℝ) = ‖𝓕⁻ (h2.toLp Ψ)‖ₑ ^ (2 : ℝ) := by
    rw [lp_enorm_sq_eq_lintegral_real (𝓕⁻ (h2.toLp Ψ))]
    apply lintegral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx]
  have hH : ∫⁻ a : ℝ, ‖Ψ a‖ₑ ^ (2 : ℝ) = ‖h2.toLp Ψ‖ₑ ^ (2 : ℝ) := by
    rw [lp_enorm_sq_eq_lintegral_real (h2.toLp Ψ)]
    apply lintegral_congr_ae
    filter_upwards [h2.coeFn_toLp] with a ha
    rw [ha]
  rw [hL, hH, enorm_fourierInv_real]


/-- **Plancherel--Pólya (sampling) identity.**  For `F ∈ L²(ℝ)` vanishing a.e. outside the Nyquist
band `[-1/2,1/2]`, the samples of `𝓕⁻ F` satisfy `Σ_m ‖𝓕⁻ F m‖² = ∫_ℝ ‖F‖²`. -/
theorem tsum_enorm_sq_fourierInv_eq_lintegral {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume : Measure ℝ))
    (hsupp : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → F ξ = 0) :
    ∑' m : ℤ, ‖𝓕⁻ F (m:ℝ)‖ₑ ^ (2:ℝ) = ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ) := by
  have hab : (-(1/2):ℝ) < 1/2 := by norm_num
  have hband := Set.Ioc_subset_Icc_self (a := (-(1/2):ℝ)) (b := 1/2)
  -- (0) `F` is integrable: it is `L²` with a.e. support in a compact set.
  have hF1 : MemLp F 1 (volume : Measure ℝ) := by
    have hfin : (volume : Measure ℝ) (Set.Icc (-(1/2):ℝ) (1/2)) ≠ ∞ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hEq : F =ᵐ[volume] (Set.Icc (-(1/2):ℝ) (1/2)).indicator F := by
      filter_upwards [hsupp] with ξ hξ
      by_cases h : ξ ∈ Set.Icc (-(1/2):ℝ) (1/2)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; exact hξ h
    have h2' : MemLp ((Set.Icc (-(1/2):ℝ) (1/2)).indicator F) 2 (volume : Measure ℝ) :=
      hF.ae_eq hEq
    have h1' : MemLp ((Set.Icc (-(1/2):ℝ) (1/2)).indicator F) 1 (volume : Measure ℝ) :=
      h2'.mono_exponent_of_measure_support_ne_top (fun x hx => Set.indicator_of_notMem hx F)
        hfin (by norm_num)
    exact h1'.ae_eq hEq.symm
  -- (1) the Fourier coefficient at `-m` is an explicit exponential integral on the band
  have hcoeff : ∀ m : ℤ, fourierCoeffOn hab F (-m)
      = ∫ θ in (-(1/2):ℝ)..(1/2),
          F θ * Complex.exp (2 * Real.pi * Complex.I * ((m:ℂ) * (θ:ℂ))) := by
    intro m
    rw [fourierCoeffOn_eq_integral]
    rw [show (1/2:ℝ) - (-(1/2)) = 1 by norm_num, div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [smul_eq_mul]
    rw [fourier_coe_apply]
    simp only [neg_neg]
    rw [mul_comm (Complex.exp _) (F x)]
    congr 1
    push_cast
    rw [div_one]
    ring
  -- (2) that interval integral is the sample of the inverse Fourier transform
  have hint : ∀ m : ℤ,
      (∫ θ in (-(1/2):ℝ)..(1/2),
          F θ * Complex.exp (2 * Real.pi * Complex.I * ((m:ℂ) * (θ:ℂ)))) = 𝓕⁻ F (m:ℝ) := by
    intro m
    have h0 : (fun θ : ℝ => F θ * Complex.exp (2 * Real.pi * Complex.I * ((m:ℂ) * (θ:ℂ))))
        = fun θ : ℝ =>
            F θ * Complex.exp (↑(2 * Real.pi * inner ℝ θ (m:ℝ)) * Complex.I) := by
      funext θ
      congr 2
      rw [Real.inner_apply]
      push_cast
      ring
    rw [h0, Real.fourierInv_eq']
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    rw [← integral_Icc_eq_integral_Ioc]
    rw [← MeasureTheory.integral_indicator (measurableSet_Icc)]
    have hae : (Set.Icc (-(1/2):ℝ) (1/2)).indicator
          (fun θ => F θ * Complex.exp (↑(2 * Real.pi * inner ℝ θ (m:ℝ)) * Complex.I))
        =ᵐ[volume]
        (fun θ => Complex.exp (↑(2 * Real.pi * inner ℝ θ (m:ℝ)) * Complex.I) • F θ) := by
      filter_upwards [hsupp] with θ hθ
      by_cases h : θ ∈ Set.Icc (-(1/2):ℝ) (1/2)
      · rw [Set.indicator_of_mem h, smul_eq_mul, mul_comm]
      · rw [Set.indicator_of_notMem h, hθ h, smul_zero]
    rw [integral_congr_ae hae]
  have hnorm : ∀ m : ℤ, ‖fourierCoeffOn hab F (-m)‖ = ‖𝓕⁻ F (m:ℝ)‖ :=
    fun m => by rw [hcoeff m, hint m]
  -- (3) Parseval for the Fourier coefficients on the band
  have hparseval : ∑' m : ℤ, ‖fourierCoeffOn hab F m‖ ^ 2
      = ∫ θ in (-(1/2):ℝ)..(1/2), ‖F θ‖ ^ 2 := by
    rw [tsum_sq_fourierCoeffOn hab (hF.restrict (Set.Ioc (-(1/2):ℝ) (1/2)))]
    rw [show (1/2:ℝ) - (-(1/2)) = 1 by norm_num, inv_one, one_smul]
  -- (4) the band integral is the whole-line integral
  have hbandint : (∫ θ in (-(1/2):ℝ)..(1/2), ‖F θ‖ ^ 2) = ∫ θ : ℝ, ‖F θ‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    rw [← integral_Icc_eq_integral_Ioc]
    rw [← MeasureTheory.integral_indicator (measurableSet_Icc)]
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with θ hθ
    by_cases h : θ ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hθ h]
      simp
  -- (5) assemble
  have hkey : ∑' m : ℤ, ‖𝓕⁻ F (m:ℝ)‖ ^ 2 = ∫ θ : ℝ, ‖F θ‖ ^ 2 := by
    calc ∑' m : ℤ, ‖𝓕⁻ F (m:ℝ)‖ ^ 2
        = ∑' m : ℤ, ‖fourierCoeffOn hab F (-m)‖ ^ 2 := by
          refine tsum_congr fun m => ?_
          rw [hnorm m]
      _ = ∑' m : ℤ, ‖fourierCoeffOn hab F m‖ ^ 2 :=
          tsum_comp_neg (fun m : ℤ => ‖fourierCoeffOn hab F m‖ ^ 2)
      _ = ∫ θ : ℝ, ‖F θ‖ ^ 2 := by rw [hparseval, hbandint]
  have hsumm1 : Summable (fun m : ℤ => ‖fourierCoeffOn hab F m‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn hab (hF.restrict (Set.Ioc (-(1/2):ℝ) (1/2)))).summable
  have hsumm2 : Summable (fun m : ℤ => ‖fourierCoeffOn hab F (-m)‖ ^ 2) :=
    hsumm1.comp_injective (i := fun m : ℤ => -m) (fun a b hab' => by simpa using hab')
  have hsummable : Summable (fun m : ℤ => ‖𝓕⁻ F (m:ℝ)‖ ^ 2) :=
    hsumm2.congr (fun m => by rw [hnorm m])
  have hLHS : ∑' m : ℤ, ‖𝓕⁻ F (m:ℝ)‖ₑ ^ (2:ℝ) = ENNReal.ofReal (∫ θ : ℝ, ‖F θ‖ ^ 2) := by
    have h1 : ∑' m : ℤ, ‖𝓕⁻ F (m:ℝ)‖ₑ ^ (2:ℝ)
        = ∑' m : ℤ, ENNReal.ofReal (‖𝓕⁻ F (m:ℝ)‖ ^ 2) := by
      refine tsum_congr fun m => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hsummable, hkey]
  have hRHS : ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (∫ θ : ℝ, ‖F θ‖ ^ 2) := by
    have h1 : ∫⁻ x : ℝ, ‖F x‖ₑ ^ (2:ℝ) = ∫⁻ x : ℝ, ENNReal.ofReal (‖F x‖ ^ 2) := by
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
    have hint' : Integrable (fun x : ℝ => ‖F x‖ ^ 2) := by
      simpa using hF.integrable_norm_rpow (by norm_num) (by norm_num)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint'
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  rw [hLHS, hRHS]

end Commons.Analysis.Fourier
