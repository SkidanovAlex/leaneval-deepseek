/-
# Puig's argument (C12): Fourier helpers for the resonance lemma

The resonance argument (`resonant_false`) needs the following classical fact about the
dual almost Mathieu equation: the space of continuous `1`-periodic solutions of
`u (x + α) + u (x - α) = (E - 2λ cos 2πx) u x` is at most one dimensional.  This is proved
by comparing Fourier coefficients and using a Wronskian identity.

This file provides the elementary layer: the characters `chr n`, the Fourier coefficient
`cF` (an integral over one period of `ℝ`), their relation to `AddCircle`'s `fourierCoeff`,
and the two "calculus" rules (shift by `a`, multiply by a character).
-/
import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace Work.TMPuig

/-! ## 1. Characters -/

/-- The character `x ↦ e^{2πi n x}` of `ℝ/ℤ`, written as a function on `ℝ`.  This is
`fourier n` evaluated at `(x : AddCircle 1)` (`chr_eq_fourier`). -/
def chr (n : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)

theorem chr_zero (n : ℤ) : chr n 0 = 1 := by simp [chr]

theorem chr_add (n : ℤ) (x y : ℝ) : chr n (x + y) = chr n x * chr n y := by
  rw [chr, chr, chr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chr_one_val (n : ℤ) : chr n 1 = 1 := by
  rw [chr]
  have h : (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ) * ((1 : ℝ) : ℂ))
      = ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- `chr n` is `1`-periodic. -/
theorem chr_one (n : ℤ) (x : ℝ) : chr n (x + 1) = chr n x := by
  rw [chr_add, chr_one_val, mul_one]

theorem chr_neg_neg (n : ℤ) (a : ℝ) : chr (-n) (-a) = chr n a := by
  rw [chr, chr]
  congr 1
  push_cast
  ring

theorem chr_mul (m n : ℤ) (x : ℝ) : chr m x * chr n x = chr (m + n) x := by
  rw [chr, chr, chr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_chr (n : ℤ) : Continuous (chr n) := by
  unfold chr
  fun_prop

theorem chr_neg (n : ℤ) (x : ℝ) : chr (-n) x = (chr n x)⁻¹ := by
  rw [chr, chr, show (2 * Real.pi * Complex.I * ((-n : ℤ) : ℝ) * x)
      = -(2 * Real.pi * Complex.I * ((n : ℤ) : ℝ) * x) by push_cast; ring, Complex.exp_neg]

/-- `chr n x` is `fourier n` on the circle. -/
theorem chr_eq_fourier (n : ℤ) (x : ℝ) :
    chr n x = fourier n (x : AddCircle (1 : ℝ)) := by
  rw [chr, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-! ## 2. Fourier coefficients -/

/-- The `n`-th Fourier coefficient of a function on `ℝ`, integrated over one period. -/
def cF (f : ℝ → ℂ) (n : ℤ) : ℂ := ∫ x in (0 : ℝ)..1, chr (-n) x * f x

theorem cF_congr {f g : ℝ → ℂ} (h : ∀ x, f x = g x) (n : ℤ) : cF f n = cF g n := by
  rw [cF, cF]
  apply intervalIntegral.integral_congr
  intro x _
  show chr (-n) x * f x = chr (-n) x * g x
  rw [h x]

/-- The bridge to `AddCircle.fourierCoeff`. -/
theorem cF_eq_fourierCoeff (f : ℝ → ℂ) (n : ℤ) :
    cF f n = fourierCoeff (AddCircle.liftIco (1 : ℝ) (0 : ℝ) f) n := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [cF, fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  simp only [add_zero, zero_add, sub_zero, div_one, one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  rw [chr, fourier_coe_apply, smul_eq_mul]
  congr 1
  have h1 : (((1 : ℝ)) : ℂ) = 1 := by norm_num
  rw [show (0 : ℝ) + 1 - 0 = 1 by norm_num, h1, div_one]
  push_cast
  ring

/-- Shifting the argument by `a` multiplies the `n`-th coefficient by `e^{2πi n a}`. -/
theorem cF_shift (f : ℝ → ℂ) (hfp : ∀ x, f (x + 1) = f x) (a : ℝ) (n : ℤ) :
    cF (fun x => f (x + a)) n = chr n a * cF f n := by
  have hsub : (∫ x in (0 : ℝ)..1, chr (-n) x * f (x + a))
      = ∫ y in a..1 + a, chr (-n) (y - a) * f y := by
    simpa using intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
      (fun y => chr (-n) (y - a) * f y) a
  have hpoint : ∀ y : ℝ, chr (-n) (y - a) * f y = chr n a * (chr (-n) y * f y) := by
    intro y
    rw [show y - a = y + (-a) by ring, chr_add, chr_neg_neg]
    ring
  have hper : Function.Periodic (fun y : ℝ => chr (-n) y * f y) 1 := by
    intro y
    show chr (-n) (y + 1) * f (y + 1) = chr (-n) y * f y
    rw [chr_one, hfp]
  rw [cF, hsub]
  conv_rhs => rw [cF]
  rw [show (1 : ℝ) + a = a + 1 by ring]
  rw [show (∫ y in a..a + 1, chr (-n) (y - a) * f y)
        = ∫ y in a..a + 1, chr n a * (chr (-n) y * f y) from by
      apply intervalIntegral.integral_congr
      intro y _
      exact hpoint y]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hfin := Function.Periodic.intervalIntegral_add_eq hper 0 a
  rw [zero_add] at hfin
  exact hfin.symm

/-- Multiplying by a character shifts the index of the Fourier coefficient. -/
theorem cF_chr_mul (f : ℝ → ℂ) (k n : ℤ) :
    cF (fun x => chr k x * f x) n = cF f (n - k) := by
  rw [cF, cF]
  apply intervalIntegral.integral_congr
  intro x _
  show chr (-n) x * (chr k x * f x) = chr (-(n - k)) x * f x
  rw [show chr (-n) x * (chr k x * f x) = chr (-n + k) x * f x by
    rw [← chr_mul]; ring]
  congr 1
  ring_nf

theorem cF_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    cF (fun x => c * f x) n = c * cF f n := by
  rw [cF, cF]
  rw [show (∫ x in (0 : ℝ)..1, chr (-n) x * (c * f x))
      = ∫ x in (0 : ℝ)..1, c * (chr (-n) x * f x) from by
    apply intervalIntegral.integral_congr
    intro x _
    ring]
  rw [intervalIntegral.integral_const_mul]

theorem cF_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cF (fun x => f x + g x) n = cF f n + cF g n := by
  rw [cF, cF, cF]
  rw [show (∫ x in (0 : ℝ)..1, chr (-n) x * (f x + g x))
      = ∫ x in (0 : ℝ)..1, (chr (-n) x * f x + chr (-n) x * g x) from by
    apply intervalIntegral.integral_congr
    intro x _
    ring]
  rw [intervalIntegral.integral_add]
  · exact (((continuous_chr (-n)).mul hf).intervalIntegrable 0 1)
  · exact (((continuous_chr (-n)).mul hg).intervalIntegrable 0 1)

/-- `2 cos 2πx` is the sum of the two characters `e^{±2πix}`. -/
theorem two_mul_cos_eq (x : ℝ) :
    ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) = chr 1 x + chr (-1) x := by
  have h1 : chr 1 x = Complex.cos ((2 * Real.pi * x : ℝ) : ℂ)
      + Complex.sin ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    rw [chr, show (2 * Real.pi * Complex.I * ((1 : ℤ) : ℝ) * x)
        = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
  have h2 : chr (-1) x = Complex.cos ((2 * Real.pi * x : ℝ) : ℂ)
      - Complex.sin ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    rw [chr, show (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℝ) * x)
        = (-(((2 * Real.pi * x : ℝ) : ℂ))) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, ← Complex.ofReal_cos]
  push_cast
  ring

/-! ## 3. Lifting to the circle -/

/-- A `1`-periodic function agrees with its lift to the circle at every point. -/
theorem liftIco_coe_eq {f : ℝ → ℂ} (hfp : ∀ x, f (x + 1) = f x) (x : ℝ) :
    AddCircle.liftIco (1 : ℝ) (0 : ℝ) f (x : AddCircle (1 : ℝ)) = f x := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hy : x - (⌊x⌋ : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨?_, ?_⟩
    · linarith [Int.floor_le x]
    · rw [zero_add]
      linarith [Int.lt_floor_add_one x]
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) = (((x - ⌊x⌋ : ℝ)) : AddCircle (1 : ℝ)) := by
    rw [QuotientAddGroup.eq_iff_sub_mem]
    have h : x - (x - (⌊x⌋ : ℝ)) = ((⌊x⌋ : ℤ) : ℝ) := by ring
    rw [h]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨⌊x⌋, by simp⟩
  rw [hcoe, AddCircle.liftIco_coe_apply hy]
  have hper : Function.Periodic f 1 := hfp
  have h := hper.zsmul ⌊x⌋ (x - ⌊x⌋)
  simp only [zsmul_one] at h
  have hx : x - (⌊x⌋ : ℝ) + (⌊x⌋ : ℝ) = x := by ring
  rw [hx] at h
  exact h.symm

end Work.TMPuig
