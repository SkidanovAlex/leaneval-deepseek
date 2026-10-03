/-
# The Fourier coefficient of the sequence symbol: `coeff1 (symSeq κ) j = κ j`

`Work.KMTPlan.A6.symSeq κ x = ∑' p, κ p * e(p x)` is the symbol of the one-dimensional
kernel `κ` (`SymSeq.lean`), and `Work.KMTPlan.A6.coeff1 f j = ∫₀¹ f x e(-j x) dx` is the
`j`-th Fourier coefficient (`SymToolbox.lean`).  This module proves the elementary inversion
identity

  `coeff1 (symSeq κ) j = κ j`   for summable `κ : ℤ → ℂ`,

i.e. the Fourier inversion theorem for `1`-periodic functions that are *defined* by their
(absolute) Fourier series.  It is the one-dimensional input of the "concrete multiplier"
dictionary of §6 of Krause--Mirek--Tao.

The proof is the direct computation: exchange the interval integral with the (unconditionally
convergent) sum by `MeasureTheory.integral_tsum` applied to the restricted measure on `Ioc 0 1`,
then use the orthogonality `∫₀¹ e(n x) dx = δ_{n,0}` (`integral_eeC_int`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

noncomputable section

/-- `‖e(t)‖ = 1`: `e = exp (2 π i ·)` has unit modulus on the reals. -/
lemma norm_eeC (t : ℝ) : ‖eeC t‖ = 1 := by
  rw [eeC]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = (2 * Real.pi * t : ℝ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The exponential character is multiplicative: `e(a + b) = e(a) e(b)`. -/
lemma eeC_add (a b : ℝ) : eeC (a + b) = eeC a * eeC b := by
  unfold eeC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Orthogonality of the characters on `[0,1]`: `∫₀¹ e(n x) dx = 1` if `n = 0` and `0` otherwise. -/
lemma integral_eeC_int (n : ℤ) :
    ∫ x in (0 : ℝ)..1, eeC ((n : ℝ) * x) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [eeC]
  · have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      have hn' : (n : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using hn
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hn'
    have hpt : ∀ x : ℝ,
        eeC ((n : ℝ) * x) = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * x) := by
      intro x
      unfold eeC
      congr 1
      push_cast
      ring
    simp only [hpt, if_neg hn]
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring,
          Complex.exp_int_mul_two_pi_mul_I]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, hexp,
      Complex.exp_zero, sub_self, zero_div]

/-- Interchange of a `ℤ`-indexed sum with the interval integral `∫₀¹`, in the form needed here:
if each `F p` is a.e. strongly measurable and the sum of the `L¹`-norms is summable, then the
integral of the sum is the sum of the integrals. -/
lemma intervalIntegral_tsum {F : ℤ → ℝ → ℂ}
    (hmeas : ∀ p, AEStronglyMeasurable (F p) (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hsum : ∑' p : ℤ, ∫⁻ x, ‖F p x‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ∞) :
    ∫ x in (0 : ℝ)..1, (∑' p : ℤ, F p x) = ∑' p : ℤ, ∫ x in (0 : ℝ)..1, F p x := by
  simp only [integral_of_le zero_le_one]
  exact MeasureTheory.integral_tsum hmeas hsum

/-- **Fourier inversion for the sequence symbol.**  If `κ : ℤ → ℂ` is summable, then the `j`-th
Fourier coefficient of its symbol `symSeq κ` is `κ j`. -/
theorem SymSeq_coeff1 {κ : ℤ → ℂ} (hκ : Summable κ) (j : ℤ) :
    Work.KMTPlan.A6.coeff1 (Work.KMTPlan.A6.symSeq κ) j = κ j := by
  rw [coeff1]
  -- move the `e(-j x)` factor inside the defining series of `symSeq κ`
  have hF : ∀ x : ℝ, symSeq κ x * eeC (-(j : ℝ) * x)
      = ∑' p : ℤ, κ p * eeC (p * x) * eeC (-(j : ℝ) * x) := by
    intro x
    unfold symSeq
    rw [← tsum_mul_right]
  simp_rw [hF]
  set F : ℤ → ℝ → ℂ := fun p x => κ p * eeC (p * x) * eeC (-(j : ℝ) * x) with hFdef
  have hmeas : ∀ p : ℤ, AEStronglyMeasurable (F p) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro p
    rw [hFdef]
    exact (by simp only [eeC]; fun_prop :
      Continuous fun x : ℝ => κ p * eeC (↑p * x) * eeC (-↑j * x)).aestronglyMeasurable
  -- the `L¹`-norm of the `p`-th integrand is `‖κ p‖`, independently of the integration variable
  have hterm : ∀ p : ℤ,
      ∫⁻ x, ‖F p x‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = ‖κ p‖ₑ := by
    intro p
    have hnorm : ∀ x : ℝ, ‖F p x‖ = ‖κ p‖ := by
      intro x
      rw [hFdef]
      simp only [norm_mul, norm_eeC, mul_one]
    have hnormE : ∀ x : ℝ, ‖F p x‖ₑ = ‖κ p‖ₑ := by
      intro x
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      apply NNReal.coe_injective
      simpa using hnorm x
    simp only [hnormE]
    rw [lintegral_const]
    have hμ : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
      norm_num
    rw [hμ, mul_one]
  have hsum : ∑' p : ℤ, ∫⁻ x, ‖F p x‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ∞ := by
    simp_rw [hterm]
    have hNN : Summable (fun p : ℤ => ‖κ p‖₊) := by
      apply NNReal.summable_coe.mp
      simpa using hκ.norm
    simpa only [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr hNN
  rw [intervalIntegral_tsum (F := F) hmeas hsum]
  -- evaluate each inner integral: it is `κ p` when `p = j` and `0` otherwise
  have hterm2 : ∀ p : ℤ, ∫ x in (0 : ℝ)..1, F p x = κ p * (if p - j = 0 then 1 else 0) := by
    intro p
    have hpt : ∀ x : ℝ, F p x = κ p * eeC (((p : ℝ) - (j : ℝ)) * x) := by
      intro x
      simp only [hFdef]
      rw [mul_assoc]
      rw [show eeC (↑p * x) * eeC (-↑j * x) = eeC ((↑p - ↑j) * x) from by
        rw [← eeC_add]; congr 1; ring]
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [show ((p : ℝ) - (j : ℝ)) = ((p - j : ℤ) : ℝ) from by push_cast; ring]
    rw [integral_eeC_int]
  simp_rw [hterm2]
  rw [tsum_eq_single j (fun p hp => by
    rw [if_neg (fun h => hp (sub_eq_zero.mp h)), mul_zero])]
  simp

end

end Work.KMTPlan.A6
