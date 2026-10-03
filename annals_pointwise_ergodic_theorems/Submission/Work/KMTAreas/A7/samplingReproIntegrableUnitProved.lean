import Mathlib
import Submission.Work.KMTAreas.A7.sublatticeShannonReproduction
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound

set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform Topology

noncomputable section

/-- **Unit-lattice Shannon sampling for integrable band-limited functions.**  If `ψ` is a Schwartz
function whose Fourier transform equals `1` on `[-c₀,c₀]` and vanishes outside the Nyquist band
`[-1/2,1/2]`, and if `f` is integrable and continuous with Fourier transform supported in
`[-c₀,c₀]` (`c₀ < 1/2`), then `f` is reproduced from its integer samples by `ψ`:

  `f t = ∑'_m ψ (t - m) * f m`  for every `t`.

The proof uses the aliasing identity (`shannon_decimation_poisson`) and Fourier inversion
(`shannon_bandlimited_inversion`). -/
theorem samplingReproIntegrableUnitProved (c0 : ℝ) (hc0 : 0 < c0) (hc0' : c0 < 1 / 2)
    (ψ : SchwartzMap ℝ ℂ)
    (hψ1 : ∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier ψ ξ = 1)
    (hψs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2:ℝ)) (1/2) → FourierTransform.fourier ψ ξ = 0)
    (f : ℝ → ℂ) (hfint : MeasureTheory.Integrable f) (hfcont : Continuous f)
    (hfs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-c0) c0 → FourierTransform.fourier f ξ = 0) :
    ∀ t : ℝ, f t = ∑' m : ℤ, ψ (t - (m : ℝ)) * f (m : ℝ) := by
  intro t
  obtain ⟨hFint, hinv⟩ := shannon_bandlimited_inversion c0 f hfint hfcont hfs
  obtain ⟨C₁, hC₁, hψd₀⟩ := shannon_schwartz_bound ψ
  obtain ⟨C₂, hC₂, hFd₀⟩ := shannon_schwartz_bound (𝓕 ψ)
  set C : ℝ := max C₁ C₂ with hCdef
  have hC : 0 ≤ C := le_trans hC₁ (le_max_left _ _)
  have hψd : ∀ x : ℝ, ‖ψ x‖ ≤ C * (1 + |x|) ^ (-(2:ℝ)) := fun x =>
    (hψd₀ x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  have hFd : ∀ y : ℝ, ‖𝓕 (ψ : ℝ → ℂ) y‖ ≤ C * (1 + |y|) ^ (-(2:ℝ)) := by
    intro y
    rw [← SchwartzMap.fourier_coe]
    exact (hFd₀ y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
  -- Poisson summation along `ℤ` for the window `ψ`
  have hpois : ∀ ξ ∈ Set.Icc (-c0) c0,
      (∑' m : ℤ, ψ (t - (m : ℝ)) * (𝐞 (-(ξ * (t - (m : ℝ)))) : ℂ)) = 1 := by
    intro ξ hξ
    have hdec := shannon_decimation_poisson (ψ : ℝ → ℂ) ψ.continuous (b := 2) (C := C)
      (by norm_num) hC hψd hFd (a := 1) (by norm_num) t ξ
    have hdec' : (∑' m : ℤ, ψ (t - (m : ℝ)) * (𝐞 (-(ξ * (t - (m : ℝ)))) : ℂ))
        = (∑' j : ℤ, 𝓕 (ψ : ℝ → ℂ) (ξ - (j : ℝ)) * (𝐞 (-((j : ℝ) * t)) : ℂ)) := by
      simpa only [one_mul, mul_one, div_one, inv_one, Complex.ofReal_one] using hdec
    rw [hdec']
    rw [tsum_eq_single (0 : ℤ)]
    · have h0 : (𝐞 ((0 : ℝ)) : ℂ) = 1 := by rw [Real.fourierChar_apply]; simp
      rw [Int.cast_zero, sub_zero, zero_mul, neg_zero, h0, mul_one,
        ← SchwartzMap.fourier_coe]
      exact hψ1 ξ hξ
    · intro j hj
      have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h1 : (0 : ℤ) < |j| := abs_pos.mpr hj
        have h2 : (1 : ℤ) ≤ |j| := by omega
        exact_mod_cast h2
      have hx : ξ - (j : ℝ) ∉ Set.Icc (-(1/2:ℝ)) (1/2) := by
        intro hmem
        have h3 : |ξ - (j : ℝ)| ≤ 1 / 2 := by
          rw [abs_le]; exact ⟨hmem.1, hmem.2⟩
        have h4 : |ξ| ≤ c0 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
        have h6 : |(j : ℝ)| ≤ |ξ - (j : ℝ)| + |ξ| := by
          have h := abs_add_le ξ (-(ξ - (j : ℝ)))
          rw [abs_neg] at h
          have h2 : ξ + -(ξ - (j : ℝ)) = (j : ℝ) := by ring
          rw [h2] at h
          linarith
        linarith
      rw [show 𝓕 (⇑ψ) (ξ - (j : ℝ)) = 0 from by
        rw [← SchwartzMap.fourier_coe]
        exact hψs (ξ - (j : ℝ)) hx, zero_mul]
  -- the same identity after multiplying by `e(ξt)`
  have hpois2 : ∀ ξ ∈ Set.Icc (-c0) c0,
      (∑' m : ℤ, ψ (t - (m : ℝ)) * (𝐞 (ξ * (m : ℝ)) : ℂ)) = (𝐞 (ξ * t) : ℂ) := by
    intro ξ hξ
    have h1 : (∑' m : ℤ, ψ (t - (m : ℝ)) * (𝐞 (ξ * (m : ℝ)) : ℂ))
        = (∑' m : ℤ, ψ (t - (m : ℝ)) * (𝐞 (-(ξ * (t - (m : ℝ)))) : ℂ)) * (𝐞 (ξ * t) : ℂ) := by
      rw [← tsum_mul_right]
      refine tsum_congr (fun m => ?_)
      have harg : -(ξ * (t - (m : ℝ))) + ξ * t = ξ * (m : ℝ) := by ring
      rw [mul_assoc, shannon_fourierChar_mul, harg]
    rw [h1, hpois ξ hξ, one_mul]
  -- the pointwise identity for every `ξ`
  have hall : ∀ ξ : ℝ, (𝐞 (ξ * t) : ℂ) * 𝓕 f ξ
      = ∑' m : ℤ, ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Icc (-c0) c0
    · rw [← hpois2 ξ hξ, ← tsum_mul_right]
      refine tsum_congr (fun m => ?_)
      ring
    · have hξ0 : 𝓕 f ξ = 0 := hfs ξ hξ
      rw [hξ0, mul_zero]
      simp
  -- summability of the lattice weights
  have hψsumm : Summable (fun m : ℤ => ‖ψ (t - (m : ℝ))‖) := by
    have h1 : Summable (fun m : ℤ => (1 + |t - (m : ℝ)|) ^ (-(2:ℝ))) :=
      Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _)
        (Commons.Analysis.Fourier.lattice_decay_pointwise t)
        (Commons.Analysis.Fourier.summable_int_one_div_abs_shift_half_sq ⌊t⌋)
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hψd _) (h1.mul_left C)
  -- integrability of each summand
  have hfamint : ∀ m : ℤ, Integrable (fun ξ : ℝ =>
      ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ)) := by
    intro m
    have hmeas : AEStronglyMeasurable (fun ξ : ℝ => (𝐞 (ξ * (m : ℝ)) : ℂ)) volume :=
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
    have hbd : ∀ᵐ ξ : ℝ, ‖(𝐞 (ξ * (m : ℝ)) : ℂ)‖ ≤ 1 :=
      Filter.Eventually.of_forall (fun ξ => by rw [shannon_norm_fourierChar])
    have h1 : Integrable (fun ξ : ℝ => (𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ) :=
      hFint.bdd_mul hmeas hbd
    exact h1.const_mul (ψ (t - (m : ℝ)))
  -- summability of the integrated norms
  have hfamsum : Summable (fun m : ℤ => ∫ ξ : ℝ,
      ‖ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ)‖) := by
    have hbound : ∀ m : ℤ, (∫ ξ : ℝ,
        ‖ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ)‖)
        ≤ ‖ψ (t - (m : ℝ))‖ * (∫ ξ : ℝ, ‖𝓕 f ξ‖) := by
      intro m
      have hpt : ∀ ξ : ℝ, ‖ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ)‖
          = ‖ψ (t - (m : ℝ))‖ * ‖𝓕 f ξ‖ := by
        intro ξ
        rw [norm_mul, norm_mul, shannon_norm_fourierChar, one_mul]
      rw [show (∫ ξ : ℝ, ‖ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ)‖)
            = ∫ ξ : ℝ, ‖ψ (t - (m : ℝ))‖ * ‖𝓕 f ξ‖ from
          integral_congr_ae (Filter.Eventually.of_forall hpt)]
      rw [MeasureTheory.integral_const_mul]
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun _ => norm_nonneg _)) hbound ?_
    exact hψsumm.mul_right _
  -- Fubini
  have hInt : (∫ ξ : ℝ, ∑' m : ℤ, ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ))
      = ∑' m : ℤ, ψ (t - (m : ℝ)) * f (m : ℝ) := by
    rw [(MeasureTheory.integral_tsum_of_summable_integral_norm hfamint hfamsum).symm]
    refine tsum_congr (fun m => ?_)
    rw [MeasureTheory.integral_const_mul, (hinv ((m : ℤ) : ℝ)).symm]
  calc f t = ∫ ξ : ℝ, (𝐞 (ξ * t) : ℂ) * 𝓕 f ξ := hinv t
    _ = ∫ ξ : ℝ, ∑' m : ℤ, ψ (t - (m : ℝ)) * ((𝐞 (ξ * (m : ℝ)) : ℂ) * 𝓕 f ξ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        exact hall ξ
    _ = ∑' m : ℤ, ψ (t - (m : ℝ)) * f (m : ℝ) := hInt

end

end Work.KMTAreas.A7
