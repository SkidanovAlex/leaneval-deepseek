/-
# Sampling (Plancherel–Pólya) for integrable band-limited amplitudes

Let `0 < c0 < 1/2`, let `k` be a Schwartz function whose Fourier transform is `1` on `[-c0,c0]` and
vanishes off `[-1/2,1/2]`, and let `W` be an integrable amplitude supported in `[-c0,c0]`.  Then the
band-limited function `𝓕⁻W` is reproduced from its lattice samples:

`𝓕⁻W x = ∑'_m k (x - m) · 𝓕⁻W m`   for every `x`.

The proof is the Poisson-summation route.  The partition identity
`∑_m k (x - m) e^{2πi ξ m} = e^{2πi ξ x}` for `|ξ| ≤ c0` follows by applying
`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` to the modulated function
`t ↦ k t · e^{2πi (ξ x - ξ t)}`: its Fourier transform at `n` is `e^{2πi ξ x} · 𝓕k (n + ξ)`, which
vanishes for `n ≠ 0` because `|n + ξ| ≥ 1 - c0 > 1/2`.  Integrating the partition identity against
the amplitude `W` and interchanging the lattice sum with the frequency integral
(`MeasureTheory.integral_tsum`) gives the claim.
-/

import Mathlib
import Submission.Work.Analysis.Fourier.bandlimited_weighted_reproduction
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound
import Submission.Commons.Analysis.Fourier.schwartz_decay_real
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Work.Maximal.Decimated

noncomputable section

/-- The phase `t ↦ e^{2πi t}`, as a complex number. -/
private def E (t : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * t) * Complex.I)

private lemma E_add (a b : ℝ) : E (a + b) = E a * E b := by
  rw [E, E, E, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma E_neg (a : ℝ) : E (-a) = (E a)⁻¹ := by
  rw [E, E, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

private lemma E_sub (a b : ℝ) : E (a - b) = E a * (E b)⁻¹ := by
  rw [sub_eq_add_neg, E_add, E_neg]

private lemma E_norm (t : ℝ) : ‖E t‖ = 1 := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)

private lemma E_continuous : Continuous E := by
  unfold E
  fun_prop

private lemma E_ne_zero (t : ℝ) : E t ≠ 0 := by
  rw [← norm_pos_iff, E_norm]
  norm_num

/-- The exponential form appearing in `Real.fourier_eq'`, written with `E`. -/
private lemma E_neg_arg (s : ℝ) : Complex.exp (↑(-2 * Real.pi * s) * Complex.I) = E (-s) := by
  rw [E]
  congr 1
  push_cast
  ring

/-- The exponential form appearing in `Real.fourierInv_eq'`, written with `E`. -/
private lemma E_pos_arg (s : ℝ) : Complex.exp (↑(2 * Real.pi * s) * Complex.I) = E s := rfl

private lemma E_of_fourierChar (t : ℝ) :
    ((Real.fourierChar t : Circle) : ℂ) = E t := Real.fourierChar_apply t

private lemma E_coe_fourier (n : ℤ) (x : ℝ) : fourier n (x : UnitAddCircle) = E ((n : ℝ) * x) := by
  rw [fourier_coe_apply]
  rw [E]
  norm_num
  congr 1
  push_cast
  ring

/-- Multiplying the amplitude by a constant multiplies the Fourier transform by that constant. -/
private lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (η : ℝ) :
    FourierTransform.fourier (fun t : ℝ => c * f t) η
      = c * FourierTransform.fourier f η := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- Modulating the amplitude by `e^{-2πi a t}` translates the Fourier transform by `a`. -/
private lemma fourier_mul_E_neg (f : ℝ → ℂ) (a η : ℝ) :
    FourierTransform.fourier (fun t : ℝ => f t * E (-(a * t))) η
      = FourierTransform.fourier f (η + a) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with t
  rw [Real.inner_apply, Real.inner_apply, smul_eq_mul, smul_eq_mul]
  rw [E_neg_arg, E_neg_arg]
  rw [show -(t * (η + a)) = -(t * η) + -(a * t) by ring, E_add]
  ring

/-- **Partition of unity of the lattice translates of the window `k`.**  For `|ξ| ≤ c0`,
`∑_m k (x - m) e^{2πi ξ m} = e^{2πi ξ x}`. -/
lemma partition_of_unity {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 < 1 / 2)
    (k : SchwartzMap ℝ ℂ)
    (hk1 : ∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier (k : ℝ → ℂ) ξ = 1)
    (hk0 : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
      FourierTransform.fourier (k : ℝ → ℂ) ξ = 0)
    {ξ x : ℝ} (hξ : ξ ∈ Set.Icc (-c0) c0) :
    E (ξ * x) = ∑' m : ℤ, (k : ℝ → ℂ) (x - (m : ℝ)) * E (ξ * (m : ℝ)) := by
  have hξabs : |ξ| ≤ c0 := abs_le.mpr ⟨hξ.1, hξ.2⟩
  set g : ℝ → ℂ := fun t => E (ξ * x) * ((k : ℝ → ℂ) t * E (-(ξ * t))) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact continuous_const.mul ((k.continuous).mul (E_continuous.comp (by fun_prop)))
  have hgnorm : ∀ t : ℝ, ‖g t‖ = ‖(k : ℝ → ℂ) t‖ := by
    intro t
    rw [hg]
    simp only []
    rw [norm_mul, E_norm, one_mul, norm_mul, E_norm, mul_one]
  have hgdec : g =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(2 : ℝ))) := by
    have h2 := (k.isBigO_cocompact_rpow (-(2 : ℝ))).norm_left
    rw [show (fun t : ℝ => ‖(k : ℝ → ℂ) t‖)
        = fun t : ℝ => ‖g t‖ from funext (fun t => (hgnorm t).symm)] at h2
    exact Asymptotics.IsBigO.of_norm_left (by simpa [Real.norm_eq_abs] using h2)
  have hfour : ∀ η : ℝ, FourierTransform.fourier g η
      = E (ξ * x) * FourierTransform.fourier (k : ℝ → ℂ) (η + ξ) := by
    intro η
    rw [hg]
    rw [show (fun t : ℝ => E (ξ * x) * ((k : ℝ → ℂ) t * E (-(ξ * t))))
        = (fun t : ℝ => E (ξ * x) * ((fun s : ℝ => (k : ℝ → ℂ) s * E (-(ξ * s))) t))
        from rfl]
    rw [fourier_const_mul, fourier_mul_E_neg]
  have hzero_ne : ∀ n : ℤ, n ≠ 0 → FourierTransform.fourier g ((n : ℝ)) = 0 := by
    intro n hn
    rw [hfour (n : ℝ), hk0 ((n : ℝ) + ξ) ?_, mul_zero]
    intro hmem
    have h1 : |(n : ℝ) + ξ| ≤ 1 / 2 := abs_le.mpr ⟨hmem.1, hmem.2⟩
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have := Int.one_le_abs hn
      exact_mod_cast this
    have h3 : |(n : ℝ)| - |ξ| ≤ |(n : ℝ) + ξ| := abs_sub_abs_le_abs_add _ _
    linarith
  have hzero0 : FourierTransform.fourier g ((0 : ℤ) : ℝ) = E (ξ * x) := by
    rw [hfour ((0 : ℤ) : ℝ)]
    rw [show ((0 : ℤ) : ℝ) + ξ = ξ by norm_num, hk1 ξ hξ, mul_one]
  have hsummable : Summable (fun n : ℤ => FourierTransform.fourier g ((n : ℝ))) :=
    summable_of_ne_finset_zero (s := {0}) (fun n hn => hzero_ne n (by simpa using hn))
  have hpois := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hgc one_lt_two hgdec
    hsummable x
  have hR : (∑' n : ℤ, FourierTransform.fourier g ((n : ℝ)) * fourier n (x : UnitAddCircle))
      = E (ξ * x) := by
    rw [tsum_eq_single 0 (fun n hn => by rw [hzero_ne n hn, zero_mul])]
    rw [hzero0, fourier_zero, mul_one]
  have hL : (∑' n : ℤ, g (x + (n : ℝ)))
      = ∑' n : ℤ, (k : ℝ → ℂ) (x + (n : ℝ)) * E (-(ξ * (n : ℝ))) := by
    apply tsum_congr
    intro n
    rw [hg]
    simp only []
    rw [show -(ξ * (x + (n : ℝ))) = -(ξ * (n : ℝ)) - ξ * x by ring, E_sub]
    rw [show E (ξ * x) * ((k : ℝ → ℂ) (x + (n : ℝ)) * (E (-(ξ * (n : ℝ))) * (E (ξ * x))⁻¹))
        = (k : ℝ → ℂ) (x + (n : ℝ)) * (E (ξ * x) * (E (ξ * x))⁻¹) * E (-(ξ * (n : ℝ)))
        by ring]
    rw [mul_inv_cancel₀ (E_ne_zero _)]
    ring
  have hkey : (∑' n : ℤ, (k : ℝ → ℂ) (x + (n : ℝ)) * E (-(ξ * (n : ℝ)))) = E (ξ * x) := by
    rw [← hL, hpois, hR]
  rw [← hkey, ← Equiv.tsum_eq (Equiv.neg ℤ)
    (fun n : ℤ => (k : ℝ → ℂ) (x + (n : ℝ)) * E (-(ξ * (n : ℝ))))]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply]
  congr 1
  · push_cast
    ring_nf
  · congr 1
    push_cast
    ring_nf

/-- **Sampling/reproduction for integrable band-limited amplitudes.**  Let `0 < c0 < 1/2`, let `k`
be a Schwartz function whose Fourier transform is `1` on `[-c0,c0]` and vanishes off `[-1/2,1/2]`,
and let `W` be an integrable amplitude supported in `[-c0,c0]`.  Then for every `x`,
`𝓕⁻W x = ∑'_m k (x - m) · 𝓕⁻W m`. -/
theorem sampling_identity_integrable {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 < 1 / 2)
    (k : SchwartzMap ℝ ℂ)
    (hk1 : ∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier (k : ℝ → ℂ) ξ = 1)
    (hk0 : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2) : ℝ) (1/2) →
      FourierTransform.fourier (k : ℝ → ℂ) ξ = 0)
    (W : ℝ → ℂ) (hW : MeasureTheory.Integrable W)
    (hWsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-c0) c0 → W ξ = 0)
    (x : ℝ) :
    FourierTransformInv.fourierInv W x
      = ∑' m : ℤ, (k : ℝ → ℂ) (x - (m : ℝ)) *
          FourierTransformInv.fourierInv W ((m : ℤ) : ℝ) := by
  -- the ENNReal norm of a phase is `1`
  have hEnorm : ∀ t : ℝ, ‖E t‖ₑ = 1 := by
    intro t
    rw [← ofReal_norm, E_norm]
    norm_num
  -- the lattice norms of the window are summable, uniformly bounded
  obtain ⟨M, hMpos, hM⟩ := Commons.Analysis.Fourier.schwartz_lattice_sum_bound k
  have hsum_norm : Summable (fun m : ℤ => ‖(k : ℝ → ℂ) (x - (m : ℝ))‖) := by
    obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq k
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      ((Commons.Analysis.Fourier.summable_inv_one_add_sq_sub x).mul_left C)
    have h := hC (x - (m : ℝ))
    rw [div_eq_mul_inv] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x - (m : ℝ)), sq_nonneg ((m : ℝ) - x)]
  have hmass : (∑' m : ℤ, ‖(k : ℝ → ℂ) (x - (m : ℝ))‖ₑ) ≠ ⊤ := by
    have hreal : (∑' m : ℤ, ‖(k : ℝ → ℂ) (x - (m : ℝ))‖) ≤ M := by
      have := hM x
      simpa using this
    have h1 : (∑' m : ℤ, ‖(k : ℝ → ℂ) (x - (m : ℝ))‖ₑ)
        = ∑' m : ℤ, ENNReal.ofReal (‖(k : ℝ → ℂ) (x - (m : ℝ))‖) := by
      apply tsum_congr
      intro m
      rw [← ofReal_norm]
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) hsum_norm]
    exact ne_of_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hreal) ENNReal.ofReal_lt_top)
  have hWfin : (∫⁻ ξ : ℝ, ‖W ξ‖ₑ) ≠ ⊤ := ne_of_lt hW.hasFiniteIntegral
  -- the left-hand side as an explicit integral
  have hL : FourierTransformInv.fourierInv W x = ∫ ξ : ℝ, E (ξ * x) * W ξ := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [Real.inner_apply, smul_eq_mul, E_pos_arg]
  -- the pointwise identity obtained from the partition of unity
  have hpoint : ∀ ξ : ℝ, E (ξ * x) * W ξ
      = ∑' m : ℤ, (k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ) := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Icc (-c0) c0
    · have hp := partition_of_unity hc0 hc01 k hk1 hk0 (ξ := ξ) (x := x) hξ
      have hsumm : Summable (fun m : ℤ => (k : ℝ → ℂ) (x - (m : ℝ)) * E (ξ * (m : ℝ))) := by
        refine Summable.of_norm ?_
        have h1 : (fun m : ℤ => ‖(k : ℝ → ℂ) (x - (m : ℝ)) * E (ξ * (m : ℝ))‖)
            = fun m : ℤ => ‖(k : ℝ → ℂ) (x - (m : ℝ))‖ := by
          funext m
          rw [norm_mul, E_norm, mul_one]
        rw [h1]
        exact hsum_norm
      rw [hp]
      rw [show (∑' m : ℤ, (k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ))
            = ∑' m : ℤ, ((k : ℝ → ℂ) (x - (m : ℝ)) * E (ξ * (m : ℝ))) * W ξ
          from tsum_congr (fun m => by ring)]
      rw [Summable.tsum_mul_right (W ξ) hsumm]
    · rw [hWsupp ξ hξ, mul_zero]
      simp
  have hstep : (∫ ξ : ℝ, E (ξ * x) * W ξ)
      = ∫ ξ : ℝ, ∑' m : ℤ,
          (k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    exact hpoint ξ
  -- finiteness for the interchange
  have hfin : (∑' m : ℤ, ∫⁻ ξ : ℝ,
      ‖(k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ)‖ₑ) ≠ ⊤ := by
    have hpt : ∀ m : ℤ, (∫⁻ ξ : ℝ,
        ‖(k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ)‖ₑ)
          = ‖(k : ℝ → ℂ) (x - (m : ℝ))‖ₑ * ∫⁻ ξ : ℝ, ‖W ξ‖ₑ := by
      intro m
      have h1 : (fun ξ : ℝ => ‖(k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ)‖ₑ)
          = fun ξ : ℝ => ‖(k : ℝ → ℂ) (x - (m : ℝ))‖ₑ * ‖W ξ‖ₑ := by
        funext ξ
        rw [enorm_mul, enorm_mul, hEnorm, one_mul]
      rw [h1]
      rw [MeasureTheory.lintegral_const_mul' _ _
        (by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)]
    rw [tsum_congr hpt, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hmass hWfin
  have hmeas : ∀ m : ℤ, AEStronglyMeasurable
      (fun ξ : ℝ => (k : ℝ → ℂ) (x - (m : ℝ)) * (E (ξ * (m : ℝ)) * W ξ))
      (MeasureTheory.volume : Measure ℝ) := by
    intro m
    refine AEStronglyMeasurable.const_mul ?_ _
    exact (E_continuous.comp (by fun_prop)).aestronglyMeasurable.mul hW.aestronglyMeasurable
  rw [hL, hstep, MeasureTheory.integral_tsum hmeas hfin]
  apply tsum_congr
  intro m
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [Real.inner_apply, smul_eq_mul, E_pos_arg]

end

end Work.Maximal.Decimated
