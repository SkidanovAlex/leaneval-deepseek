/-
# Funnel tail expansion of `K₊^{(24)}`: the final assembly

Given the bound on the five remainder groups (`Work.Asymptotics.K24F_sm_sum_bound`), this file
proves `Work.Asymptotics.KPlus_funnel_tail_twentyfour_of_sm`, which is the funnel tail expansion
of the CKMRV kernel `K₊^{(24)}`.

The proof is the `d = 24` analogue of `Submission/Work/Asymptotics/KPlus_funnel_tail_eight.lean`
and follows the algebra of `K24F.KPlus24_diff`:

  `Δ(z)·(j τ - j z)·(K₊(τ,z) - 𝒢₊(τ,z)) = c z² (Sm1 + … + Sm5)`,

with `‖Δ(z)(j τ - j z)‖ ≥ 1/16` (`K24F.divisor_lower`), `‖c‖ = 1/(36·1728·π⁻²)`,
`‖z²‖ ≤ (1+t)²` and `e^{-2π(t-Im τ)} ≤ 16 e^{-π(t-Im τ)}`.
-/
import Mathlib
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.E4Fun_far_imagAxis_near_one

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `‖c‖ = 1/(36·1728·π⁻²)` for the constant `c = (36·1728·π⁻²·i)⁻¹` of the expansion. -/
lemma norm_c : ‖K24F.c‖ ≤ Real.pi ^ 2 / (36 * 1728) := by
  have hpi2 : ‖((Real.pi : ℂ)) ^ (-2 : ℤ)‖ = (Real.pi ^ 2)⁻¹ := by
    rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat, norm_inv, norm_pow]
    rw [show ‖((Real.pi : ℂ))‖ = Real.pi from
      (RCLike.norm_ofReal Real.pi).trans (abs_of_pos Real.pi_pos)]
  have hnorm : ‖((36 : ℂ) * 1728 * ((Real.pi : ℂ)) ^ (-2 : ℤ) * Complex.I)‖
      = 36 * 1728 * (Real.pi ^ 2)⁻¹ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_ofNat, hpi2]
  rw [K24F.c, norm_inv, hnorm, div_eq_mul_inv]
  have hne : (36 : ℝ) * 1728 * (Real.pi ^ 2)⁻¹ ≠ 0 := by positivity
  field_simp
  norm_num

/-- **Funnel tail expansion of `K₊^{(24)}`** from the bound on the five remainder groups. -/
theorem KPlus_funnel_tail_twentyfour_of_sm
    (hsm : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z + K24F.Sm5 τ z‖
          ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * (t - τ.im)))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖
          ≤ C * (scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨Cs, Ns, hCs, hNs, hsb⟩ := hsm
  have hE4b : ∀ z : UpperHalfPlane, 3 ≤ z.im → ‖E4Fun z - 1‖ ≤ 1 / 2 :=
    E4Fun_far_imagAxis_near_one
  refine ⟨16 * (Real.pi ^ 2 / (36 * 1728)) * Cs, Ns, 2, by positivity, hNs, by norm_num, ?_⟩
  intro τ z t hτ ht hz
  have him : z.im = t := K24F.im_of_coe_eq_axis hz
  have ht3 : 3 ≤ t := by have := hτ.2; linarith
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hden : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    K24F.divisor_lower τ z t hτ ht hz
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hden
    norm_num at hden
  have hE4 : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z (by rw [him]; exact ht3)
  have hΔJ : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 := mul_ne_zero hDz hJ
  have hdiff := K24F.KPlus24_diff τ z hJ hE4
  have hrepr : KPlus 24 τ z - Compact.Gplus 24 τ z
      = K24F.c * (z : ℂ) ^ 2
          * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z + K24F.Sm5 τ z)
          / (DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := by
    rw [eq_div_iff hΔJ]
    rw [show (KPlus 24 τ z - Compact.Gplus 24 τ z)
          * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))
        = DeltaFun z * (jInvariantFun τ - jInvariantFun z)
          * (KPlus 24 τ z - Compact.Gplus 24 τ z) from by ring]
    exact hdiff
  have hdenpos : 0 < ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hdeninv : (‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖)⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ hdenpos (by norm_num : (0 : ℝ) < 16)]
    have h16 : ((16 : ℝ))⁻¹ = 1 / 16 := by norm_num
    rw [h16]
    exact hden
  have hS := hsb τ z t hτ ht hz
  have hSsum : ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z + K24F.Sm5 τ z‖
      ≤ Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have a := norm_add_le (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z)
      (K24F.Sm5 τ z)
    have b := norm_add_le (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z) (K24F.Sm4 τ z)
    have c := norm_add_le (K24F.Sm1 τ z + K24F.Sm2 τ z) (K24F.Sm3 τ z)
    have d := norm_add_le (K24F.Sm1 τ z) (K24F.Sm2 τ z)
    linarith
  have hznorm : ‖(z : ℂ) ^ 2‖ ≤ (1 + t) ^ 2 := by
    have h1 : ‖(z : ℂ)‖ = t := by
      rw [hz, norm_mul, Complex.norm_I, mul_one]
      exact (RCLike.norm_ofReal t).trans (abs_of_nonneg (by linarith))
    rw [norm_pow, h1]
    nlinarith [ht3]
  have hexp : Real.exp (-(2 * Real.pi * (t - τ.im)))
      ≤ 16 * Real.exp (-(Real.pi * (t - τ.im))) := by
    have h1 : Real.exp (-(2 * Real.pi * (t - τ.im)))
        ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_pos, hτ.2, ht]
    have h2 : (0 : ℝ) < Real.exp (-(Real.pi * (t - τ.im))) := Real.exp_pos _
    nlinarith [h1, h2]
  have hstep1 : ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖
      ≤ ‖K24F.c * (z : ℂ) ^ 2
          * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
              + K24F.Sm5 τ z)‖ * 16 := by
    rw [hrepr, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hdeninv (norm_nonneg _)
  have hstep2' : ‖K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
            + K24F.Sm5 τ z)‖
      ≤ (Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im)))) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul norm_c hznorm (norm_nonneg _) (by positivity)) hSsum
      (norm_nonneg _) (by positivity)
  have hstep2 : ‖K24F.c * (z : ℂ) ^ 2
        * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
            + K24F.Sm5 τ z)‖ * 16
      ≤ ((Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im))))) * 16 :=
    mul_le_mul_of_nonneg_right hstep2' (by norm_num)
  have hstep3 : ((Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
        * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im))))) * 16
      ≤ (16 * (Real.pi ^ 2 / (36 * 1728)) * Cs) * (scale τ) ^ Ns * (1 + t) ^ 2
          * Real.exp (-(Real.pi * (t - τ.im))) := by
    have hexp' : Real.exp (-(2 * Real.pi * (t - τ.im)))
        ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_pos, hτ.2, ht]
    have hbase : (0:ℝ) ≤ (Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2 :=
      mul_nonneg (by positivity) (by positivity)
    have hbase2 : (0:ℝ) ≤ Cs * (scale τ) ^ Ns :=
      mul_nonneg hCs.le (Real.rpow_nonneg (scale_pos τ).le Ns)
    have hkey : (Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im))))
        ≤ (Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(Real.pi * (t - τ.im)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp' hbase2) hbase
    calc ((Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(2 * Real.pi * (t - τ.im))))) * 16
        ≤ ((Real.pi ^ 2 / (36 * 1728)) * (1 + t) ^ 2
          * (Cs * (scale τ) ^ Ns * Real.exp (-(Real.pi * (t - τ.im))))) * 16 :=
          mul_le_mul_of_nonneg_right hkey (by norm_num)
      _ = (16 * (Real.pi ^ 2 / (36 * 1728)) * Cs) * (scale τ) ^ Ns * (1 + t) ^ 2
          * Real.exp (-(Real.pi * (t - τ.im))) := by ring
  have hfin := le_trans hstep1 (le_trans hstep2 hstep3)
  have hrpow : (1 + t) ^ (2 : ℝ) = (1 + t) ^ 2 := by rw [Real.rpow_two, sq]
  simpa only [hrpow] using hfin

end

end Work.Asymptotics
