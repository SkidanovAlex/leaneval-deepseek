import Mathlib
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.KPlus_funnel_tail_eight
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Asymptotics.EtailE.KPlus8_funnel_tail_sharp

namespace Work.Asymptotics.EtailE

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm

open Work.Kernels

/-! ## The `S`-equivariance of the cusp model `𝒢₊^{(8)}`

The kernel `K_+^{(8)}(·,z)` has weight `8/2 = 4` in `τ`: `K_+^{(8)}(S•τ,z) = -τ^4 K_+^{(8)}(τ,z)`
(`Work.Kernels.KernelFacts.KPlus_S_smul`).  The model `𝒢₊^{(8)}` obeys the same law, which is
what allows the cusp-`0` tile `E = KEpsilon = S(𝔽)` to be reduced to the funnel `𝔽`. -/

/-- `𝒢₊^{(8)}` is `S`-equivariant in `τ` with weight `4`. -/
lemma Gplus8_S_smul (τ z : ℍ) :
    Compact.Gplus8 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (4:ℤ)) * Compact.Gplus8 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hE6 := E6Fun_S τ
  have hE4 := E4Fun_S τ
  have hphi0 : Work.Kernels.phi0 (ModularGroup.S • τ) = - Work.Kernels.phi0 τ := by
    have h := Work.Kernels.KernelFacts.phiVec_S_smul τ 1
    simpa [Work.Kernels.phiVec, zpow_zero, neg_one_mul] using h
  rw [Compact.Gplus8_eq_lin (ModularGroup.S • τ) z, Compact.Gplus8_eq_lin τ z]
  have key : (12 * Complex.I / (Real.pi : ℂ)) *
        (((ModularGroup.S • τ : ℍ) : ℂ) * E6Fun (ModularGroup.S • τ)
          - Work.Kernels.phi0 (ModularGroup.S • τ) * E4Fun (ModularGroup.S • τ)) * (z : ℂ)
      + 36 * ((ModularGroup.S • τ : ℍ) : ℂ) * E6Fun (ModularGroup.S • τ) / (Real.pi : ℂ) ^ 2
    = -((τ : ℂ) ^ (4:ℤ)) * ((12 * Complex.I / (Real.pi : ℂ)) *
        ((τ : ℂ) * E6Fun τ - Work.Kernels.phi0 τ * E4Fun τ) * (z : ℂ)
      + 36 * (τ : ℂ) * E6Fun τ / (Real.pi : ℂ) ^ 2) := by
    rw [hcoe, hE6, hE4, hphi0, zpow_ofNat]
    field_simp
    ring
  rw [key]
  ring

/-- `𝒢₊^{(8)}` is `S`-equivariant in `τ` with weight `4` (`Compact.Gplus` form). -/
lemma Gplus_eight_S_smul (τ z : ℍ) :
    Compact.Gplus 8 (ModularGroup.S • τ) z = -((τ : ℂ) ^ (4:ℤ)) * Compact.Gplus 8 τ z := by
  simpa [Compact.Gplus] using Gplus8_S_smul τ z

/-- **Tail estimate for `K_+^{(8)}` on the cusp-`0` tile `E = KEpsilon`.**

`E = S(𝔽)` and both `K_+^{(8)}(·,z)` and its cusp model `𝒢₊^{(8)}(·,z)` have weight `4` in `τ`,
so on `E` the difference is the `S`-translate of the difference on the funnel.  The funnel
estimate is sharp at rate `e^{-2π(t-Im τ)}`
(`Work.Asymptotics.EtailE.KPlus8_funnel_tail_sharp`); since `t ≥ 2 Im(S•w) + 1` on `E` we have
`2 Im(S•w) ≤ t` and hence `e^{-2π(t-Im(S•w))} ≤ e^{-πt}`, while `scale (S•w) ≤ 3 scale w`.
-/
theorem EtailE_KPlus8 :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        Work.Asymptotics.EtailE.Ethresh w t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KPlus 8 w z - Work.Asymptotics.Compact.Gplus 8 w z‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C0, N0, M0, hC0, hN0, hM0, hsh⟩ := KPlus8_funnel_tail_sharp
  refine ⟨C0 * 3 ^ N0, N0 + 4, M0, by positivity, by linarith, hM0, ?_⟩
  intro w z t hw ht hz
  set τ : ℍ := ModularGroup.S • w with hτdef
  have ht2 : 2 * (ModularGroup.S • w).im + 1 ≤ t := ht
  have hτF : Work.Asymptotics.Funnel τ := by rw [hτdef]; exact E_S_mem_Funnel hw
  have him2 : 2 ≤ τ.im := by rw [hτdef]; exact hw.2
  have ht' : τ.im + 1 ≤ t := by rw [hτdef]; linarith [ht2, hw.2]
  have htwiceIm : 2 * τ.im ≤ t := by rw [hτdef]; linarith [ht2]
  have hbf := hsh τ z t hτF ht' hz
  have hSτ : ModularGroup.S • τ = w := by rw [hτdef]; exact E_S_smul_S_smul w
  have hK : KPlus 8 w z = -((τ : ℂ) ^ (4:ℤ)) * KPlus 8 τ z := by
    rw [← hSτ]
    have h := Work.Kernels.KernelFacts.KPlus_S_smul 8 (Or.inl rfl) z τ
    have h84 : ((↑(8:ℕ) : ℤ) / 2) = (4:ℤ) := by norm_num
    rw [h84] at h
    exact h
  have hG : Compact.Gplus 8 w z = -((τ : ℂ) ^ (4:ℤ)) * Compact.Gplus 8 τ z := by
    rw [← hSτ]
    exact Gplus_eight_S_smul τ z
  rw [hK, hG]
  have hnorm : ‖-((τ : ℂ) ^ (4:ℤ)) * KPlus 8 τ z - -((τ : ℂ) ^ (4:ℤ)) * Compact.Gplus 8 τ z‖
      = ‖(τ : ℂ)‖ ^ 4 * ‖KPlus 8 τ z - Compact.Gplus 8 τ z‖ := by
    rw [show -((τ : ℂ) ^ (4:ℤ)) * KPlus 8 τ z - -((τ : ℂ) ^ (4:ℤ)) * Compact.Gplus 8 τ z
        = -(((τ : ℂ) ^ (4:ℤ)) * (KPlus 8 τ z - Compact.Gplus 8 τ z)) from by ring,
      norm_neg, norm_mul, zpow_ofNat, norm_pow]
  rw [hnorm]
  have hnormτ : ‖(τ : ℂ)‖ ≤ scale w := by rw [hτdef]; exact E_norm_S_le_scale w
  have hw4 : ‖(τ : ℂ)‖ ^ 4 ≤ (scale w) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hnormτ 4
  have hw4nn : (0:ℝ) ≤ (scale w) ^ 4 := pow_nonneg (scale_pos w).le 4
  have hscaleτ : scale τ ≤ 3 * scale w := by rw [hτdef]; exact E_scale_S_le hw
  have hmain : (scale w)^4 * (C0 * (scale τ)^N0 * (1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im))))
      ≤ C0 * 3^N0 * (scale w)^(N0+4) * (1+t)^M0 * Real.exp (-(Real.pi * t)) := by
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
    have hL : (scale w)^4 * (C0 * (scale τ)^N0 * (1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im))))
        = ((scale w)^4 * (C0 * (scale τ)^N0))
            * ((1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im)))) := by ring
    have hR : C0 * 3^N0 * (scale w)^(N0+4) * (1+t)^M0 * Real.exp (-(Real.pi*t))
        = ((scale w)^4 * (C0 * (3^N0 * (scale w)^N0)))
            * ((1+t)^M0 * Real.exp (-(Real.pi*t))) := by
      rw [Real.rpow_add (scale_pos w) N0 4]
      norm_num
      ring
    rw [hL, hR]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hstrN' hw4nn) hexpM
      (mul_nonneg ht1M (Real.exp_pos _).le)
      (mul_nonneg hw4nn (mul_nonneg hCp (mul_nonneg (Real.rpow_nonneg (by norm_num) N0)
        (Real.rpow_nonneg (scale_pos w).le N0))))
  calc ‖(τ : ℂ)‖ ^ 4 * ‖KPlus 8 τ z - Compact.Gplus 8 τ z‖
      ≤ (scale w)^4 * (C0 * (scale τ)^N0 * (1+t)^M0 * Real.exp (-(2*Real.pi*(t-τ.im)))) :=
        mul_le_mul hw4 hbf (norm_nonneg _) hw4nn
    _ ≤ C0 * 3^N0 * (scale w)^(N0+4) * (1+t)^M0 * Real.exp (-(Real.pi * t)) := hmain

end Work.Asymptotics.EtailE
