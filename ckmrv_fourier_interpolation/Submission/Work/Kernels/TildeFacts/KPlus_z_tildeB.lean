/-
# `K_+^{(d)}` is annihilated by `I - STS` in the `z` variable

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) Proposition
`prop:Kpmslashtilde` (Section 4.3): the kernels `K_±^{(d)}` are annihilated in the `z`
variable by the tilde ideals

  `𝓘̃_± = (T - 2I + T⁻¹ ∓ 2S)·R + (I ∓ STS)·R`.

This file proves the `I - STS` half of that statement for `K_+^{(d)}`, in the pointwise form
recorded by `Work.Kernels.TildeB`:

  `TildeB 1 (2 - d/2) (fun z ↦ K_+^{(d)}(τ,z)) = 0`.

The proof is the explicit transformation law of `K_+^{(d)}(τ,·)` under `z ↦ (STS) • z` at
weight `2 - d/2`, which is proved factor by factor: `j` is `SL(2,ℤ)`-invariant, the forms
`fk` transform in their own weights, `Δ` in weight `12`, and the "tilde" basis functions
`φ̃_j = z²(E₂|₂S)^j` transform in weight `2j-2`.
-/
import Mathlib
import Submission.Work.Kernels.TildeOps
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.KernelFacts.fk_slash

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.TildeFacts

/-- `(STS) ∈ SL(2,ℤ)` is the matrix `S * T * S = !![−1,0;1,−1]`, the second generator of the
tilde ideals `𝓘̃_±` of CKMRV (3.9). -/
abbrev sts : SL(2, ℤ) := ModularGroup.S * ModularGroup.T * ModularGroup.S

private lemma h00_sts : (sts : SL(2,ℤ)) 0 0 = -1 := by decide
private lemma h01_sts : (sts : SL(2,ℤ)) 0 1 = 0 := by decide
private lemma h10_sts : (sts : SL(2,ℤ)) 1 0 = 1 := by decide
private lemma h11_sts : (sts : SL(2,ℤ)) 1 1 = -1 := by decide

private lemma one_sub_ne_zero (z : ℍ) : 1 - (z:ℂ) ≠ 0 := by
  intro hc; have : (z:ℂ) = 1 := by linear_combination -hc
  exact z.im_ne_zero (by rw [← coe_im z, this]; norm_num)

private lemma sub_one_ne_zero (z : ℍ) : (z:ℂ) - 1 ≠ 0 := by
  intro hc; have : (z:ℂ) = 1 := by linear_combination hc
  exact z.im_ne_zero (by rw [← coe_im z, this]; norm_num)

private lemma jFun_sts (z : ℂ) : Work.Kernels.jFun sts z = z - 1 := by
  rw [Work.Kernels.jFun_apply, h10_sts, h11_sts]; push_cast; ring

private lemma coe_sts (z : ℍ) : ((sts • z : ℍ) : ℂ) = (z:ℂ) / (1 - (z:ℂ)) := by
  rw [Work.Kernels.coe_smul_eq, Work.Kernels.nFun_apply, Work.Kernels.jFun_apply,
    h00_sts, h01_sts, h10_sts, h11_sts]
  push_cast
  rw [show (-1 * (z:ℂ) + 0) = -(z:ℂ) by ring, show (1 * (z:ℂ) + -1) = (z:ℂ) - 1 by ring]
  rw [div_eq_div_iff (sub_one_ne_zero z) (one_sub_ne_zero z)]
  ring

private lemma smul_of_slash {k : ℤ} {F : ℍ → ℂ} {g : SL(2,ℤ)} (h : F ∣[k] g = F) (z : ℍ) :
    F (g • z) = (Work.Kernels.jFun g (z:ℂ))^k * F z := by
  have hz := congr_fun h z
  rw [Work.Kernels.slash_apply'] at hz
  have hne : Work.Kernels.jFun g (z:ℂ) ≠ 0 := Work.Kernels.jFun_ne_zero g z
  have h2 : (F (g • z) * (Work.Kernels.jFun g (z:ℂ))^(-k)) * (Work.Kernels.jFun g (z:ℂ))^k
      = F z * (Work.Kernels.jFun g (z:ℂ))^k := by rw [hz]
  rw [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at h2
  rw [h2, mul_comm]

private lemma S_sts_smul (z : ℍ) : ModularGroup.S • (sts • z) = ModularGroup.T • (ModularGroup.S • z) := by
  rw [← mul_smul, ← mul_smul]
  have hSS : ModularGroup.S * ModularGroup.S = (-1 : SL(2,ℤ)) := by decide
  have h : ModularGroup.S * (ModularGroup.S * ModularGroup.T * ModularGroup.S)
      = -(ModularGroup.T * ModularGroup.S) := by
    calc ModularGroup.S * (ModularGroup.S * ModularGroup.T * ModularGroup.S)
        = ModularGroup.S * ModularGroup.S * (ModularGroup.T * ModularGroup.S) := by group
      _ = (-1 : SL(2,ℤ)) * (ModularGroup.T * ModularGroup.S) := by rw [hSS]
      _ = -(ModularGroup.T * ModularGroup.S) := by rw [neg_one_mul]
  rw [show sts = ModularGroup.S * ModularGroup.T * ModularGroup.S from rfl, h, ModularGroup.SL_neg_smul]

/-- `E₄` transforms in weight `4` under `z ↦ (STS) • z`. -/
private lemma E4_smul (z : ℍ) : Work.Kernels.E4Fun (sts • z) = ((z:ℂ) - 1)^(4:ℤ) * Work.Kernels.E4Fun z := by
  rw [smul_of_slash (Work.Kernels.KernelFacts.E4Fun_slash sts) z, jFun_sts]

private lemma E6_smul (z : ℍ) : Work.Kernels.E6Fun (sts • z) = ((z:ℂ) - 1)^(6:ℤ) * Work.Kernels.E6Fun z := by
  rw [smul_of_slash (Work.Kernels.KernelFacts.E6Fun_slash sts) z, jFun_sts]

private lemma Delta_smul (z : ℍ) : Work.Kernels.DeltaFun (sts • z) = ((z:ℂ) - 1)^(12:ℤ) * Work.Kernels.DeltaFun z := by
  rw [smul_of_slash (Work.Kernels.KernelFacts.DeltaFun_slash sts) z, jFun_sts]

private lemma jInvariant_smul (z : ℍ) : Work.Kernels.jInvariantFun (sts • z) = Work.Kernels.jInvariantFun z := by
  have hne : ((z:ℂ) - 1)^(12:ℤ) ≠ 0 := zpow_ne_zero _ (sub_one_ne_zero z)
  have hE4 := E4_smul z
  have hΔ := Delta_smul z
  have hΔz : Work.Kernels.DeltaFun z ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero z
  simp only [Work.Kernels.jInvariantFun, hE4, hΔ]
  rw [show (((z:ℂ)-1)^(4:ℤ) * Work.Kernels.E4Fun z)^3
      = ((z:ℂ)-1)^(12:ℤ) * Work.Kernels.E4Fun z^3 by
    rw [mul_pow, ← zpow_natCast, ← _root_.zpow_mul]; norm_num]
  rw [mul_div_mul_left _ _ hne]

private lemma fk_smul (k : ℤ)
    (hk : k = -2 ∨ k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14)
    (z : ℍ) :
    Work.Kernels.fk k (sts • z) = ((z:ℂ) - 1)^k * Work.Kernels.fk k z := by
  rw [smul_of_slash (Work.Kernels.KernelFacts.fk_slash k hk sts) z, jFun_sts]

private lemma PiMat_smul (v : Fin 3 → ℤ)
    (hv : ∀ i, v i = -2 ∨ v i = 0 ∨ v i = 2 ∨ v i = 4 ∨ v i = 6 ∨ v i = 8 ∨ v i = 10
      ∨ v i = 12 ∨ v i = 14) (z : ℍ) :
    Work.Kernels.PiMat v (sts • z)
      = Work.Kernels.PiMat v z * Matrix.diagonal (fun i => ((z:ℂ) - 1)^(v i)) := by
  have h1 : Work.Kernels.PiMat v (sts • z)
      = Matrix.diagonal (fun i => ((z:ℂ) - 1)^(v i) * Work.Kernels.fk (v i) z) := by
    rw [Work.Kernels.PiMat]
    exact congr_arg Matrix.diagonal (funext fun i => fk_smul (v i) (hv i) z)
  rw [h1, Work.Kernels.PiMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

private lemma E2S_smul (z : ℍ) :
    Work.Kernels.E2S (sts • z) = (1 - (z:ℂ))^2 * Work.Kernels.E2S z := by
  have h1 : Work.Kernels.E2S (sts • z)
      = Work.Kernels.E2Fun (ModularGroup.S • (sts • z)) * (((sts • z : ℍ):ℂ))^(-2:ℤ) := by
    rw [Work.Kernels.E2S, Work.Kernels.slash_S_apply]
  have h2 : Work.Kernels.E2S z
      = Work.Kernels.E2Fun (ModularGroup.S • z) * (z:ℂ)^(-2:ℤ) := by
    rw [Work.Kernels.E2S, Work.Kernels.slash_S_apply]
  rw [h1, h2, S_sts_smul z, coe_sts z]
  rw [show ModularGroup.T • (ModularGroup.S • z) = (1:ℝ) +ᵥ (ModularGroup.S • z) from by
    simpa using UpperHalfPlane.modular_T_zpow_smul (ModularGroup.S • z) 1]
  rw [Work.Kernels.E2Fun_vadd_one]
  rw [show (-2:ℤ) = -((2:ℕ):ℤ) from rfl, _root_.zpow_neg, _root_.zpow_neg,
    zpow_natCast, zpow_natCast]
  rw [div_pow, inv_div, div_eq_mul_inv]
  ring

private lemma phitVec_smul (z : ℍ) (j : Fin 3) :
    Work.Kernels.phitVec (sts • z) j
      = ((z:ℂ) - 1)^(2 * ((j:ℕ):ℤ) - 2) * Work.Kernels.phitVec z j := by
  have hE := E2S_smul z
  have h1 := one_sub_ne_zero z
  fin_cases j
  · show ((sts • z : ℍ):ℂ)^2 = ((z:ℂ) - 1)^(2 * ((0:ℕ):ℤ) - 2) * (z:ℂ)^2
    rw [show (2 * ((0:ℕ):ℤ) - 2) = (-2:ℤ) by norm_num, coe_sts]
    rw [show ((z:ℂ)/(1-(z:ℂ)))^2 = ((z:ℂ)-1)^(-2:ℤ) * (z:ℂ)^2 by
      rw [show (-2:ℤ) = -((2:ℕ):ℤ) from rfl, _root_.zpow_neg, zpow_natCast, inv_eq_one_div,
        div_pow, show ((z:ℂ)-1)^2 = (1-(z:ℂ))^2 by ring]
      field_simp]
  · show ((sts • z : ℍ):ℂ)^2 * Work.Kernels.E2S (sts • z)
        = ((z:ℂ) - 1)^(2 * ((1:ℕ):ℤ) - 2) * ((z:ℂ)^2 * Work.Kernels.E2S z)
    rw [show (2 * ((1:ℕ):ℤ) - 2) = (0:ℤ) by norm_num, coe_sts, hE, zpow_zero, one_mul]
    rw [show ((z:ℂ)/(1-(z:ℂ)))^2 * ((1 - (z:ℂ))^2 * Work.Kernels.E2S z)
        = (z:ℂ)^2 * Work.Kernels.E2S z by
      rw [div_pow, ← mul_assoc, div_mul_cancel₀ ((z:ℂ)^2) (pow_ne_zero 2 h1)]]
  · show ((sts • z : ℍ):ℂ)^2 * (Work.Kernels.E2S (sts • z))^2
        = ((z:ℂ) - 1)^(2 * ((2:ℕ):ℤ) - 2) * ((z:ℂ)^2 * (Work.Kernels.E2S z)^2)
    rw [show (2 * ((2:ℕ):ℤ) - 2) = (2:ℤ) by norm_num, coe_sts, hE]
    rw [show ((z:ℂ)/(1-(z:ℂ)))^2 * ((1 - (z:ℂ))^2 * Work.Kernels.E2S z)^2
        = ((z:ℂ)-1)^(2:ℤ) * ((z:ℂ)^2 * (Work.Kernels.E2S z)^2) by
      rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, div_pow, mul_pow,
        show ((z:ℂ)-1)^2 = (1-(z:ℂ))^2 by ring]
      field_simp]

private lemma UpsilonPlus_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonPlus d τ (sts • z) i j
      = ((z:ℂ) - 1)^(4 - (d:ℤ)/2 - 2*((j:ℕ):ℤ)) * Work.Kernels.UpsilonPlus d τ z i j := by
  have hJ := jInvariant_smul z
  have hD := Delta_smul z
  have hz := sub_one_ne_zero z
  rcases hd with rfl | rfl
  · have hPi := PiMat_smul (![12,10,8] : Fin 3 → ℤ)
      (by intro i; fin_cases i <;> decide) z
    simp only [Work.Kernels.UpsilonPlus, reduceIte]
    rw [hJ, hD, hPi]
    rw [show (4 - ((8:ℕ):ℤ)/2 - 2*((j:ℕ):ℤ)) = -2*((j:ℕ):ℤ) by norm_num]
    have hinv : ((36:ℂ) * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
          * (((z:ℂ)-1)^(12:ℤ) * Work.Kernels.DeltaFun z)
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹
        = ((z:ℂ)-1)^(-12:ℤ)
          * ((36:ℂ) * (Real.pi:ℂ)^(-2:ℤ) * Complex.I * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))⁻¹ := by
      rw [show (36:ℂ) * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
            * (((z:ℂ)-1)^(12:ℤ) * Work.Kernels.DeltaFun z)
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
          = ((z:ℂ)-1)^(12:ℤ)
            * ((36:ℂ) * (Real.pi:ℂ)^(-2:ℤ) * Complex.I * Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) by ring,
        mul_inv, ← _root_.zpow_neg ((z:ℂ)-1) (12:ℤ)]
    rw [hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
    have hwe : ((z:ℂ)-1)^(-2*((j:ℕ):ℤ))
        = ((z:ℂ)-1)^(-12:ℤ) * ((z:ℂ)-1)^((![12,10,8] : Fin 3 → ℤ) j) := by
      rw [← zpow_add₀ hz]
      congr 1
      have hj : ((![12,10,8] : Fin 3 → ℤ) j) = 12 - 2*((j:ℕ):ℤ) := by
        fin_cases j <;> decide
      rw [hj]; ring
    rw [hwe]
    ring
  · have hPi := PiMat_smul (![4,2,0] : Fin 3 → ℤ)
      (by intro i; fin_cases i <;> decide) z
    simp only [Work.Kernels.UpsilonPlus, reduceIte]
    simp only [if_neg (show ¬((24:ℕ) = 8) by decide)]
    rw [hJ, hD, hPi]
    rw [show (4 - ((24:ℕ):ℤ)/2 - 2*((j:ℕ):ℤ)) = -8 - 2*((j:ℕ):ℤ) by norm_num]
    have hinv : ((36:ℂ) * Work.Kernels.c1728 * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
          * (((z:ℂ)-1)^(12:ℤ) * Work.Kernels.DeltaFun z))⁻¹
        = ((z:ℂ)-1)^(-12:ℤ)
          * ((36:ℂ) * Work.Kernels.c1728 * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
              * Work.Kernels.DeltaFun z)⁻¹ := by
      rw [show (36:ℂ) * Work.Kernels.c1728 * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
            * (((z:ℂ)-1)^(12:ℤ) * Work.Kernels.DeltaFun z)
          = ((z:ℂ)-1)^(12:ℤ)
            * ((36:ℂ) * Work.Kernels.c1728 * (Real.pi:ℂ)^(-2:ℤ) * Complex.I
              * Work.Kernels.DeltaFun z)
            by ring,
        mul_inv, ← _root_.zpow_neg ((z:ℂ)-1) (12:ℤ)]
    rw [hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Matrix.mul_assoc, Matrix.mul_diagonal]
    have hwe : ((z:ℂ)-1)^(-8 - 2*((j:ℕ):ℤ))
        = ((z:ℂ)-1)^(-12:ℤ) * ((z:ℂ)-1)^((![4,2,0] : Fin 3 → ℤ) j) := by
      rw [← zpow_add₀ hz]
      congr 1
      have hj : ((![4,2,0] : Fin 3 → ℤ) j) = 4 - 2*((j:ℕ):ℤ) := by
        fin_cases j <;> decide
      rw [hj]; ring
    rw [hwe]
    ring

private lemma KPlus_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Work.Kernels.KPlus d τ (sts • z)
      = ((z:ℂ) - 1)^(2 - (d:ℤ)/2) * Work.Kernels.KPlus d τ z := by
  have hz := sub_one_ne_zero z
  simp only [Work.Kernels.KPlus]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [UpsilonPlus_smul d hd τ z i j, phitVec_smul z j]
  have hc : ((z:ℂ)-1)^(4 - (d:ℤ)/2 - 2*((j:ℕ):ℤ)) * ((z:ℂ)-1)^(2*((j:ℕ):ℤ) - 2)
      = ((z:ℂ)-1)^(2 - (d:ℤ)/2) := by
    rw [← zpow_add₀ hz]
    congr 1
    ring
  rw [show Work.Kernels.phiVec τ i
        * (((z:ℂ)-1)^(4 - (d:ℤ)/2 - 2*((j:ℕ):ℤ)) * Work.Kernels.UpsilonPlus d τ z i j)
        * (((z:ℂ)-1)^(2*((j:ℕ):ℤ) - 2) * Work.Kernels.phitVec z j)
      = (((z:ℂ)-1)^(4 - (d:ℤ)/2 - 2*((j:ℕ):ℤ)) * ((z:ℂ)-1)^(2*((j:ℕ):ℤ) - 2))
        * (Work.Kernels.phiVec τ i * Work.Kernels.UpsilonPlus d τ z i j
          * Work.Kernels.phitVec z j) by ring]
  rw [hc]

theorem KPlus_z_tildeB (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    Work.Kernels.TildeB 1 (2 - (d : ℤ) / 2) (fun z : UpperHalfPlane => Work.Kernels.KPlus d τ z) = 0 := by
  ext z
  simp only [Work.Kernels.TildeB, Pi.zero_apply]
  rw [Work.Kernels.slash_apply', jFun_sts]
  rw [KPlus_smul d hd τ z]
  have hcancel : ((z:ℂ)-1)^(2 - (d:ℤ)/2) * ((z:ℂ)-1)^(-(2 - (d:ℤ)/2)) = 1 := by
    rw [← zpow_add₀ (sub_one_ne_zero z), add_neg_cancel, zpow_zero]
  rw [show ((1:ℤ):ℂ) * (((z:ℂ)-1)^(2 - (d:ℤ)/2) * Work.Kernels.KPlus d τ z
        * ((z:ℂ)-1)^(-(2 - (d:ℤ)/2)))
      = (((z:ℂ)-1)^(2 - (d:ℤ)/2) * ((z:ℂ)-1)^(-(2 - (d:ℤ)/2))) * Work.Kernels.KPlus d τ z
      by ring]
  rw [hcancel, one_mul, sub_self]

end Work.Kernels.TildeFacts
