/-
# Puig's argument (C12): the Fourier coefficients vanish at infinity

For a continuous `1`-periodic `f : ℝ → ℂ`, the `n`-th Fourier coefficient
`cF f n = ∫₀¹ e^{-2πi n x} f x dx` tends to `0` as `n → +∞` along `ℕ ⊆ ℤ`
(the Riemann–Lebesgue lemma, in the special case that matters here).

The proof is the classical "half-period translation" argument, which avoids any
approximation theory.  For `k ≥ 1` put `a = 1 / (2k)`.  Since `f` is `1`-periodic, the
shift rule `cF_shift` gives

`cF (f (· + a)) k = chr k a · cF f k = e^{2πi k a} · cF f k = - cF f k`,

so subtracting,

`2 · cF f k = cF (f - f (· + a)) k = ∫₀¹ e^{-2πi k x} (f x - f (x + a)) dx`.

Taking absolute values and using `‖chr‖ = 1` bounds this by
`∫₀¹ ‖f x - f (x + a)‖ dx ≤ sup ‖f - f (· + a)‖`, which tends to `0` by the uniform
continuity of `f` on the compact set `[0, 2]`.
-/
import Mathlib
import Submission.Work.TMPuig.FourierAux

open MeasureTheory intervalIntegral Filter
open scoped Real

noncomputable section

namespace Work.TMPuig

/-! ## Elementary facts about the characters -/

/-- Every character `chr n` has unit modulus. -/
theorem puig_chr_norm (n : ℤ) (x : ℝ) : ‖chr n x‖ = 1 := by
  rw [chr, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- `chr n x = chr 1 (n x)`. -/
theorem puig_chr_eq_chr_one_mul (n : ℤ) (x : ℝ) : chr n x = chr 1 ((n : ℝ) * x) := by
  rw [chr, chr]; congr 1; push_cast; ring

/-- The character `chr 1` at `1/2` is `-1` (the half period of `e^{2πix}`). -/
theorem puig_chr_one_half : chr 1 ((1 : ℝ) / 2) = -1 := by
  rw [chr]
  have : 2 * (Real.pi : ℂ) * Complex.I * (((1 : ℤ) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]

/-! ## A subtraction rule for `cF` -/

/-- `cF` is additive for continuous functions, hence also subtractive. -/
theorem puig_cF_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cF (fun x => f x - g x) n = cF f n - cF g n := by
  rw [cF, cF, cF]
  rw [show (∫ x in (0 : ℝ)..1, chr (-n) x * (f x - g x))
      = ∫ x in (0 : ℝ)..1, (chr (-n) x * f x - chr (-n) x * g x) from by
        apply intervalIntegral.integral_congr
        intro x _
        ring]
  rw [intervalIntegral.integral_sub]
  · exact ((continuous_chr (-n)).mul hf).intervalIntegrable 0 1
  · exact ((continuous_chr (-n)).mul hg).intervalIntegrable 0 1

/-! ## Riemann–Lebesgue for `cF` -/

theorem dual_cF_tendsto_zero {f : ℝ → ℂ} (hf : Continuous f) (hfp : ∀ x, f (x + 1) = f x) :
    Filter.Tendsto (fun k : ℕ => cF f (k : ℤ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `f` is uniformly continuous on the compact set `[0, 2]`.
  have huc : UniformContinuousOn f (Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / (2 * δ))
  refine ⟨max N₀ 1, fun k hk => ?_⟩
  have hkN₀ : (N₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hk)
  have hk1 : (1 : ℕ) ≤ k := le_trans (le_max_right _ _) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have hpos : (0 : ℝ) < 1 / (2 * δ) := by positivity
    linarith [hpos, hN₀, hkN₀]
  -- the half period `a = 1/(2k)`
  set a : ℝ := 1 / (2 * (k : ℝ)) with ha
  have ha_pos : 0 < a := by rw [ha]; positivity
  have ha_lt : a < δ := by
    rw [ha, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (k:ℝ))]
    have h2 : (1:ℝ) < 2 * δ * (k:ℝ) := by
      have h3 : 1 / (2 * δ) * (2 * δ) < (k : ℝ) * (2 * δ) :=
        mul_lt_mul_of_pos_right (lt_of_lt_of_le hN₀ hkN₀) (by positivity)
      rw [one_div_mul_cancel (by positivity : (2 * δ) ≠ 0)] at h3
      linarith
    linarith
  have ha_le : a ≤ 1/2 := by
    rw [ha, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (k:ℝ))]
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  -- the character at the half period is `-1`
  have hchr : chr (k : ℤ) a = -1 := by
    rw [puig_chr_eq_chr_one_mul]
    have : (((k : ℤ)) : ℝ) * a = 1/2 := by
      rw [ha]; push_cast; field_simp
    rw [this, puig_chr_one_half]
  have hcont_shift : Continuous (fun x : ℝ => f (x + a)) :=
    hf.comp (continuous_id.add continuous_const)
  -- the key identity `2 cF f k = cF (f - f(·+a)) k`
  have htwo : cF (fun x => f x - f (x + a)) (k : ℤ) = 2 * cF f (k : ℤ) := by
    rw [puig_cF_sub hf hcont_shift (k:ℤ), cF_shift f hfp a (k:ℤ), hchr]
    ring
  -- pointwise bound on `(0, 1]`
  have hbound : ∀ x ∈ Set.uIoc (0:ℝ) 1, ‖chr (-(k:ℤ)) x * (f x - f (x + a))‖ ≤ ε := by
    intro x hx
    rw [Set.uIoc_of_le zero_le_one] at hx
    have hxI : x ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
    have hxI2 : x ∈ Set.Icc (0:ℝ) 2 := ⟨hxI.1, by linarith [hxI.2]⟩
    have hx2 : x + a ∈ Set.Icc (0:ℝ) 2 := by
      refine ⟨by linarith [hxI.1, ha_pos.le], by linarith [hxI.2, ha_le]⟩
    have hdist : dist x (x + a) < δ := by
      rw [Real.dist_eq, show x - (x + a) = -a by ring, abs_neg, abs_of_pos ha_pos]
      exact ha_lt
    have hfd : dist (f x) (f (x + a)) < ε := hδ x hxI2 (x + a) hx2 hdist
    rw [norm_mul, puig_chr_norm, one_mul, ← dist_eq_norm]
    exact hfd.le
  have hnorm : ‖cF (fun x => f x - f (x + a)) (k:ℤ)‖ ≤ ε := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := ε) hbound
    simpa [cF] using h
  have h2 : 2 * ‖cF f (k:ℤ)‖ ≤ ε := by
    have heq : (2:ℝ) * ‖cF f (k:ℤ)‖ = ‖(2:ℂ) * cF f (k:ℤ)‖ := by
      rw [norm_mul]; norm_num
    rw [heq, ← htwo]
    exact hnorm
  rw [dist_zero_right]
  linarith

end Work.TMPuig
