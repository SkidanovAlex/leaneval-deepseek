import Mathlib
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FAssembly
import Submission.Work.Kernels.KernelFacts.KPlus_S_add

namespace Work.Asymptotics.EtailE

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm

open Work.Kernels

/-! ## The `S`-transformation of the `τ`-atoms of `𝒢₊^{(24)}` -/

lemma E4Fun_Sz (τ : ℍ) : E4Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (4:ℤ) * E4Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash τ

lemma E6Fun_Sz (τ : ℍ) : E6Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (6:ℤ) * E6Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash τ

lemma E10Fun_Sz (τ : ℍ) : E10Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (10:ℤ) * E10Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E10Fun_S_slash τ

lemma E14Fun_Sz (τ : ℍ) : E14Fun (ModularGroup.S • τ) = (τ : ℂ) ^ (14:ℤ) * E14Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E14Fun_S_slash τ

lemma DeltaFun_Sz (τ : ℍ) : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ (12:ℤ) * DeltaFun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ

lemma jInvariantFun_Ssz (τ : ℍ) :
    jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
  KernelFacts.jInvariantFun_S_smul τ

lemma phi1_S_smul (τ : ℍ) : Compact.phi1 (ModularGroup.S • τ) = - Compact.phi1 τ := by
  have h := Work.Kernels.phi0_S_smul τ
  simpa [Compact.phi1, Work.Kernels.phi0] using h

lemma phi2t_S_smul (τ : ℍ) :
    Compact.phi2t (ModularGroup.S • τ) = -((τ : ℂ) ^ (2:ℤ)) * Compact.phi2t τ := by
  have h : Work.Kernels.phi2 (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * (- Work.Kernels.phi2 τ) :=
    Work.Kernels.phi2_S_smul τ
  show Work.Kernels.phi2 (ModularGroup.S • τ) = -((τ : ℂ) ^ (2:ℤ)) * Work.Kernels.phi2 τ
  rw [h, show ((τ : ℂ) ^ (2:ℤ)) = (τ : ℂ) ^ 2 from by norm_num [zpow_ofNat]]
  ring

lemma S_coe_smul (τ : ℍ) :
    ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

/-! ## `S`-transformation of the model coefficients -/

lemma A1_S_smul (τ z : ℍ) :
    K24F.A1 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * K24F.A1 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [K24F.A1]
  rw [S_coe_smul, E14Fun_Sz, phi1_S_smul, DeltaFun_Sz, jInvariantFun_Ssz, phi2t_S_smul,
    E10Fun_Sz, zpow_ofNat]
  field_simp
  ring

lemma A0_S_smul (τ z : ℍ) :
    K24F.A0 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * K24F.A0 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [K24F.A0]
  rw [S_coe_smul, E14Fun_Sz, phi1_S_smul, DeltaFun_Sz, jInvariantFun_Ssz, phi2t_S_smul,
    E10Fun_Sz, zpow_ofNat]
  field_simp
  ring

lemma B1_S_smul (τ z : ℍ) :
    K24F.B1 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * K24F.B1 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  simp only [K24F.B1]
  rw [S_coe_smul, E4Fun_Sz, phi1_S_smul, DeltaFun_Sz, E14Fun_Sz, zpow_ofNat]
  field_simp
  ring

lemma B0_S_smul (τ z : ℍ) :
    K24F.B0 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * K24F.B0 τ z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [K24F.B0]
  rw [S_coe_smul, E14Fun_Sz, phi1_S_smul, DeltaFun_Sz, jInvariantFun_Ssz, phi2t_S_smul,
    E10Fun_Sz, zpow_ofNat]
  field_simp
  ring

/-- `𝒢₊^{(24)}` is `S`-equivariant in `τ` with weight `12`. -/
lemma Gplus24_S_smul (τ z : ℍ) :
    Compact.Gplus 24 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * Compact.Gplus 24 τ z := by
  rw [K24F.Gplus24_eq (ModularGroup.S • τ) z, K24F.Gplus24_eq τ z,
    A1_S_smul, A0_S_smul, B1_S_smul, B0_S_smul]
  ring

/-- `𝒢₊^{(24)}` is `S`-equivariant in `τ` with weight `12` (`Compact.Gplus` form). -/
lemma Gplus_twentyfour_S_smul (τ z : ℍ) :
    Compact.Gplus 24 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (12:ℤ)) * Compact.Gplus 24 τ z :=
  Gplus24_S_smul τ z

/-! ## The sharp funnel tail of `K₊^{(24)}` -/

/-- **Sharp funnel tail expansion of `K₊^{(24)}`.**  The assembly of
`KPlus_funnel_tail_twentyfour_of_sm` without the final weakening of the exponential rate. -/
theorem KPlus24_funnel_tail_sharp :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖
          ≤ C * (scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨Cs, Ns, hCs, hNs, hsb⟩ := K24F_sm_sum_bound
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
  have hfin : ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖
      ≤ (16 * (Real.pi ^ 2 / (36 * 1728)) * Cs) * (scale τ) ^ Ns * (1 + t) ^ 2
          * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    refine le_trans hstep1 ?_
    refine le_trans (mul_le_mul_of_nonneg_right hstep2' (by norm_num : (0:ℝ) ≤ 16)) ?_
    exact le_of_eq (by ring)
  have hrpow : (1 + t) ^ (2 : ℝ) = (1 + t) ^ 2 := by rw [Real.rpow_two, sq]
  simpa only [hrpow] using hfin

/-! ## The `E`-region tail -/

/-- **Tail estimate for `K₊^{(24)}` on the cusp-`0` tile `E = KEpsilon`.**

`E = S(𝔽)` and both `K₊^{(24)}(·,z)` and its cusp model `𝒢₊^{(24)}(·,z)` have weight `12` in `τ`,
so on `E` the difference is the `S`-translate of the difference on the funnel.  The funnel
estimate is sharp at rate `e^{-2π(t-Im τ)}` (`KPlus24_funnel_tail_sharp`); since
`t ≥ 2 Im(S•w) + 1` on `E` we have `2 Im(S•w) ≤ t` and hence
`e^{-2π(t-Im(S•w))} ≤ e^{-πt}`, while `scale (S•w) ≤ 3 scale w` and `‖S•w‖ ≤ scale w`. -/
theorem EtailE_KPlus24 :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        Work.Asymptotics.EtailE.Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KPlus 24 w z - Work.Asymptotics.Compact.Gplus 24 w z‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C0, N0, M0, hC0, hN0, hM0, hsh⟩ := KPlus24_funnel_tail_sharp
  refine ⟨C0 * 3 ^ N0, N0 + 12, M0, by positivity, by linarith, hM0, ?_⟩
  intro w z t hw ht hz
  set τ : ℍ := ModularGroup.S • w with hτdef
  have ht2 : 2 * (ModularGroup.S • w).im + 1 ≤ t := ht
  have hτF : Work.Asymptotics.Funnel τ := by rw [hτdef]; exact E_S_mem_Funnel hw
  have him2 : 2 ≤ τ.im := by rw [hτdef]; exact hw.2
  have ht' : τ.im + 1 ≤ t := by rw [hτdef]; linarith [ht2, hw.2]
  have htwiceIm : 2 * τ.im ≤ t := by rw [hτdef]; linarith [ht2]
  have hbf := hsh τ z t hτF ht' hz
  have hSτ : ModularGroup.S • τ = w := by rw [hτdef]; exact E_S_smul_S_smul w
  have hK : KPlus 24 w z = -((τ : ℂ) ^ (12:ℤ)) * KPlus 24 τ z := by
    rw [← hSτ]
    have h := KernelFacts.KPlus_S_smul 24 (Or.inr rfl) z τ
    have h1224 : (((24:ℕ) : ℤ) / 2) = (12:ℤ) := by norm_num
    rw [h1224] at h
    exact h
  have hG : Compact.Gplus 24 w z = -((τ : ℂ) ^ (12:ℤ)) * Compact.Gplus 24 τ z := by
    rw [← hSτ]
    exact Gplus24_S_smul τ z
  rw [hK, hG]
  have hnorm : ‖-((τ : ℂ) ^ (12:ℤ)) * KPlus 24 τ z - -((τ : ℂ) ^ (12:ℤ)) * Compact.Gplus 24 τ z‖
      = ‖(τ : ℂ)‖ ^ 12 * ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖ := by
    rw [show -((τ : ℂ) ^ (12:ℤ)) * KPlus 24 τ z
          - -((τ : ℂ) ^ (12:ℤ)) * Compact.Gplus 24 τ z
        = -(((τ : ℂ) ^ (12:ℤ)) * (KPlus 24 τ z - Compact.Gplus 24 τ z)) from by ring,
      norm_neg, norm_mul, zpow_ofNat, norm_pow]
  rw [hnorm]
  have hnormτ : ‖(τ : ℂ)‖ ≤ scale w := by rw [hτdef]; exact E_norm_S_le_scale w
  have hw12 : ‖(τ : ℂ)‖ ^ 12 ≤ (scale w) ^ 12 := pow_le_pow_left₀ (norm_nonneg _) hnormτ 12
  have hw12nn : (0:ℝ) ≤ (scale w) ^ 12 := pow_nonneg (scale_pos w).le 12
  have hscaleτ : scale τ ≤ 3 * scale w := by rw [hτdef]; exact E_scale_S_le hw
  have hmain : (scale w)^12 * (C0 * (scale τ)^N0 * (1+t)^M0
        * Real.exp (-(2*Real.pi*(t-τ.im))))
      ≤ C0 * 3^N0 * (scale w)^(N0+12) * (1+t)^M0 * Real.exp (-(Real.pi * t)) := by
    have hCp : (0:ℝ) ≤ C0 := hC0.le
    have ht1 : (0:ℝ) ≤ 1 + t := by linarith [ht', him2]
    have ht1M : (0:ℝ) ≤ (1+t)^M0 := Real.rpow_nonneg ht1 M0
    have hstrN : (scale τ)^N0 ≤ 3^N0 * (scale w)^N0 := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (scale_pos w).le]
      exact Real.rpow_le_rpow (scale_pos τ).le hscaleτ hN0
    have hexp : Real.exp (-(2*Real.pi*(t-τ.im))) ≤ Real.exp (-(Real.pi*t)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, htwiceIm]
    have hstrN' : C0 * (scale τ)^N0 ≤ C0 * (3^N0 * (scale w)^N0) :=
      mul_le_mul_of_nonneg_left hstrN hCp
    have hexpM : (1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im)))
        ≤ (1+t)^M0 * Real.exp (-(Real.pi*t)) :=
      mul_le_mul_of_nonneg_left hexp ht1M
    have hL : (scale w)^12 * (C0 * (scale τ)^N0 * (1+t)^M0
          * Real.exp (-(2*Real.pi*(t-τ.im))))
        = ((scale w)^12 * (C0 * (scale τ)^N0))
            * ((1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im)))) := by ring
    have hR : C0 * 3^N0 * (scale w)^(N0+12) * (1+t)^M0 * Real.exp (-(Real.pi*t))
        = ((scale w)^12 * (C0 * (3^N0 * (scale w)^N0)))
            * ((1+t)^M0 * Real.exp (-(Real.pi*t))) := by
      rw [Real.rpow_add (scale_pos w) N0 12]
      norm_num
      ring
    rw [hL, hR]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hstrN' hw12nn) hexpM
      (mul_nonneg ht1M (Real.exp_pos _).le)
      (mul_nonneg hw12nn (mul_nonneg hCp (mul_nonneg (Real.rpow_nonneg (by norm_num) N0)
        (Real.rpow_nonneg (scale_pos w).le N0))))
  calc ‖(τ : ℂ)‖ ^ 12 * ‖KPlus 24 τ z - Compact.Gplus 24 τ z‖
      ≤ (scale w)^12 * (C0 * (scale τ)^N0 * (1+t)^M0
          * Real.exp (-(2*Real.pi*(t-τ.im)))) :=
        mul_le_mul hw12 hbf (norm_nonneg _) hw12nn
    _ ≤ C0 * 3^N0 * (scale w)^(N0+12) * (1+t)^M0 * Real.exp (-(Real.pi * t)) := hmain

end Work.Asymptotics.EtailE
