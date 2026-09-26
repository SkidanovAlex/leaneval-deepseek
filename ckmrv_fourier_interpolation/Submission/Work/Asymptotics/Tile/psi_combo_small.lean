import Mathlib
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Asymptotics.EReg_identities
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.CuspPolyBounds
import Submission.Work.Asymptotics.KhatE1.E1funnel_UW_bounds

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

/-- The combination `ψ₄E₈ - ψ₂E₁₀` appearing in the target. -/
def psiCombo (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ

/-! ## The `T`-cocycle of `ψ₄E₈ - ψ₂E₁₀` -/

/-- `Xfun = ξ₄E₈ - ξ₂E₁₀` is `1`-periodic. -/
lemma Xfun_vadd_one (τ : ℍ) :
    Work.Residues.Xfun ((1 : ℝ) +ᵥ τ) = Work.Residues.Xfun τ := by
  have h := Work.Asymptotics.Xnum_vadd_one τ
  simp only [Work.Asymptotics.Xnum, Work.Residues.Xfun] at h ⊢
  linear_combination -h

/-- The `T`-cocycle: `(ψ₄E₈ - ψ₂E₁₀)(τ+1) = (ψ₄E₈ - ψ₂E₁₀)(τ) + πi·Xfun(τ)`. -/
lemma psiCombo_vadd_one (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    psiCombo ℓ ((1 : ℝ) +ᵥ τ)
      = psiCombo ℓ τ + (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun τ := by
  have h := Work.Asymptotics.dXnum ℓ τ
  simp only [psiCombo, Work.Asymptotics.Xnum, Work.Residues.Xfun] at h ⊢
  linear_combination -h

/-- The `T⁻¹`-cocycle: `(ψ₄E₈ - ψ₂E₁₀)(τ-1) = (ψ₄E₈ - ψ₂E₁₀)(τ) - πi·Xfun(τ)`. -/
lemma psiCombo_vadd_neg_one (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    psiCombo ℓ ((-1 : ℝ) +ᵥ τ)
      = psiCombo ℓ τ - (Real.pi : ℂ) * Complex.I * Work.Residues.Xfun τ := by
  have h := psiCombo_vadd_one ℓ ((-1 : ℝ) +ᵥ τ)
  have h1 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
    rw [← add_vadd]; norm_num
  rw [h1] at h
  have hX := Xfun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [h1] at hX
  rw [← hX] at h
  linear_combination -h

/-! ## The `S`-transform of `Xfun` -/

/-- `Xfun(S•τ) = (9/2)τ¹²·U(τ)W(τ)²V(τ)E₄(τ)`. -/
lemma Xfun_S_smul (τ : ℍ) :
    Work.Residues.Xfun (ModularGroup.S • τ)
      = (9 / 2 : ℂ) * (τ : ℂ) ^ 12
        * (Work.Kernels.UFun τ * Work.Kernels.WFun τ ^ 2 * Work.Kernels.VFun τ
            * Work.Kernels.E4Fun τ) := by
  have h := (Work.Asymptotics.EReg_identities (ModularGroup.S • τ)).2.2.1
  rw [h, Work.Kernels.KernelFacts.UFun_S_smul, Work.Kernels.KernelFacts.VFun_S_smul,
    Work.Kernels.KernelFacts.WFun_S_smul, Work.Asymptotics.EtailE.E4Fun_S]
  ring

/-! ## `Xfun` is `Bdd (-π)` on the cusp-`0` tile -/

lemma E_bdd_Xfun : Work.Asymptotics.EtailE.Bdd (-(Real.pi))
    (fun w : ℍ => Work.Residues.Xfun w) := by
  obtain ⟨CE, hCE, hE4b⟩ := Work.Asymptotics.exists_E4_Funnel_bound
  have hCpos : (0 : ℝ) < (9 / 2) * 41 * 41 ^ 2 * 80 * CE := by
    have h2 : (0 : ℝ) < 41 * 41 ^ 2 * 80 * CE := mul_pos (by norm_num) hCE
    nlinarith [h2]
  refine ⟨(9 / 2) * 41 * 41 ^ 2 * 80 * CE, 12, hCpos, by norm_num, fun w hw => ?_⟩
  dsimp only
  have huf : Work.Asymptotics.Funnel (ModularGroup.S • w) :=
    Work.Asymptotics.EtailE.E_S_mem_Funnel hw
  obtain ⟨hUb, hWb⟩ :=
    Work.Asymptotics.KhatE1.E1funnel_UW_bounds (ModularGroup.S • w) huf
  have ht0 : 0 ≤ Work.Residues.tpar (ModularGroup.S • w) := Work.Residues.tpar_nonneg _
  have ht1 : Work.Residues.tpar (ModularGroup.S • w) ≤ 1 := Work.Residues.tpar_le_one _
  have hUn : ‖Work.Kernels.UFun (ModularGroup.S • w)‖ ≤ 41 := by
    calc ‖Work.Kernels.UFun (ModularGroup.S • w)‖
        = ‖(Work.Kernels.UFun (ModularGroup.S • w) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.UFun (ModularGroup.S • w) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖Work.Kernels.UFun (ModularGroup.S • w) - 1‖ + 1 := by norm_num
      _ ≤ 40 * Work.Residues.tpar (ModularGroup.S • w) + 1 := by linarith
      _ ≤ 41 := by linarith
  have hWn : ‖Work.Kernels.WFun (ModularGroup.S • w)‖ ≤ 41 := by
    calc ‖Work.Kernels.WFun (ModularGroup.S • w)‖
        = ‖(Work.Kernels.WFun (ModularGroup.S • w) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.WFun (ModularGroup.S • w) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖Work.Kernels.WFun (ModularGroup.S • w) - 1‖ + 1 := by norm_num
      _ ≤ 40 * Work.Residues.tpar (ModularGroup.S • w) + 1 := by linarith
      _ ≤ 41 := by linarith
  have hVn : ‖Work.Kernels.VFun (ModularGroup.S • w)‖
      ≤ 80 * Work.Residues.tpar (ModularGroup.S • w) := by
    rw [show Work.Kernels.VFun (ModularGroup.S • w)
        = Work.Kernels.UFun (ModularGroup.S • w) - Work.Kernels.WFun (ModularGroup.S • w) by
          rw [Work.Kernels.TildeFacts.theta_quartic]; ring]
    calc ‖Work.Kernels.UFun (ModularGroup.S • w) - Work.Kernels.WFun (ModularGroup.S • w)‖
        = ‖(Work.Kernels.UFun (ModularGroup.S • w) - 1)
            - (Work.Kernels.WFun (ModularGroup.S • w) - 1)‖ := by ring_nf
      _ ≤ ‖Work.Kernels.UFun (ModularGroup.S • w) - 1‖
            + ‖Work.Kernels.WFun (ModularGroup.S • w) - 1‖ := norm_sub_le _ _
      _ ≤ 40 * Work.Residues.tpar (ModularGroup.S • w)
            + 40 * Work.Residues.tpar (ModularGroup.S • w) := add_le_add hUb hWb
      _ = 80 * Work.Residues.tpar (ModularGroup.S • w) := by ring
  have hE4n : ‖Work.Kernels.E4Fun (ModularGroup.S • w)‖ ≤ CE := hE4b _ huf
  have hW2 : ‖Work.Kernels.WFun (ModularGroup.S • w) ^ 2‖ ≤ 41 ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hWn 2
  have hbb : 0 ≤ 41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) := by
    nlinarith [ht0]
  have hcc : 0 ≤ 41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) * CE :=
    mul_nonneg hbb hCE.le
  have hA : ‖Work.Kernels.UFun (ModularGroup.S • w)
      * Work.Kernels.WFun (ModularGroup.S • w) ^ 2‖ ≤ 41 * 41 ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hUn hW2 (norm_nonneg _) (by norm_num)
  have hB : ‖Work.Kernels.UFun (ModularGroup.S • w)
      * Work.Kernels.WFun (ModularGroup.S • w) ^ 2 * Work.Kernels.VFun (ModularGroup.S • w)‖
      ≤ 41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) := by
    rw [norm_mul]
    exact mul_le_mul hA hVn (norm_nonneg _) (by norm_num)
  have hC : ‖Work.Kernels.UFun (ModularGroup.S • w)
      * Work.Kernels.WFun (ModularGroup.S • w) ^ 2 * Work.Kernels.VFun (ModularGroup.S • w)
      * Work.Kernels.E4Fun (ModularGroup.S • w)‖
      ≤ 41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) * CE := by
    rw [norm_mul]
    exact mul_le_mul hB hE4n (norm_nonneg _) hbb
  have h12 : ‖(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12‖ ≤ (Work.Kernels.scale w) ^ 12 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (Work.Asymptotics.EtailE.E_norm_S_le_scale w) 12
  have htpar : Work.Residues.tpar (ModularGroup.S • w)
      = Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    rw [Work.Residues.tpar]; congr 1; ring
  have hXeq : Work.Residues.Xfun w
      = (9 / 2 : ℂ) * (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
        * (Work.Kernels.UFun (ModularGroup.S • w) * Work.Kernels.WFun (ModularGroup.S • w) ^ 2
            * Work.Kernels.VFun (ModularGroup.S • w) * Work.Kernels.E4Fun (ModularGroup.S • w)) := by
    have h := Xfun_S_smul (ModularGroup.S • w)
    rw [Work.Asymptotics.EtailE.E_S_smul_S_smul w] at h
    exact h
  have hstep1 : ‖(9 / 2 : ℂ)‖ * ‖(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12‖
      ≤ (9 / 2) * (Work.Kernels.scale w) ^ 12 := by
    rw [show ‖(9 / 2 : ℂ)‖ = (9 / 2) by norm_num]
    exact mul_le_mul_of_nonneg_left h12 (by norm_num)
  have hstepA : ‖(9 / 2 : ℂ) * (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
        * (Work.Kernels.UFun (ModularGroup.S • w) * Work.Kernels.WFun (ModularGroup.S • w) ^ 2
            * Work.Kernels.VFun (ModularGroup.S • w) * Work.Kernels.E4Fun (ModularGroup.S • w))‖
      = ‖(9 / 2 : ℂ)‖ * ‖(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12‖
          * ‖Work.Kernels.UFun (ModularGroup.S • w)
              * Work.Kernels.WFun (ModularGroup.S • w) ^ 2
              * Work.Kernels.VFun (ModularGroup.S • w)
              * Work.Kernels.E4Fun (ModularGroup.S • w)‖ := by
    rw [norm_mul, norm_mul]
  have hstepB : ‖(9 / 2 : ℂ)‖ * ‖(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12‖
          * ‖Work.Kernels.UFun (ModularGroup.S • w)
              * Work.Kernels.WFun (ModularGroup.S • w) ^ 2
              * Work.Kernels.VFun (ModularGroup.S • w)
              * Work.Kernels.E4Fun (ModularGroup.S • w)‖
      ≤ ((9 / 2) * (Work.Kernels.scale w) ^ 12)
          * (41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) * CE) :=
    mul_le_mul hstep1 hC (norm_nonneg _)
      (mul_nonneg (by norm_num)
        (pow_nonneg (Work.Kernels.scale_pos w).le 12))
  have hstepC : ((9 / 2) * (Work.Kernels.scale w) ^ 12)
        * (41 * 41 ^ 2 * (80 * Work.Residues.tpar (ModularGroup.S • w)) * CE)
      = ((9 / 2) * 41 * 41 ^ 2 * 80 * CE) * (Work.Kernels.scale w) ^ ((12 : ℕ) : ℝ)
          * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    rw [htpar, Real.rpow_natCast]; ring
  rw [hXeq]
  exact le_trans (le_of_eq hstepA) (le_trans hstepB (le_of_eq hstepC))

/-! ## The main theorem -/

theorem psi_combo_small (ℓ : Work.Kernels.LogLambdaData) : ∃ C N δ : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 < δ ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖
        ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (-(δ * (ModularGroup.S • w).im)) := by
  obtain ⟨CZ, NZ, hCZ, hNZ, hZb⟩ := Work.Asymptotics.EtailE.E_bdd_psi4E8_sub ℓ
  obtain ⟨CX, NX, hCX, hNX, hXb⟩ := E_bdd_Xfun
  have hCpos : (0 : ℝ) < CZ + Real.pi * CX := by
    have := mul_pos Real.pi_pos hCX
    linarith
  refine ⟨CZ + Real.pi * CX, max NZ NX, Real.pi, hCpos, le_max_of_le_left hNZ,
    Real.pi_pos, fun w n hn hw => ?_⟩
  have hSnn : 0 ≤ (ModularGroup.S • w).im := Work.Asymptotics.EtailE.E_im_S_nonneg hw
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hZbw : ‖psiCombo ℓ w‖ ≤ CZ * (Work.Kernels.scale w) ^ NZ
      * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := hZb w hw
  have hXbw : ‖Work.Residues.Xfun w‖ ≤ CX * (Work.Kernels.scale w) ^ NX
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := hXb w hw
  have hexpZ : Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)
      ≤ Real.exp ((-Real.pi) * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (by nlinarith [hSnn, Real.pi_pos])
  have hZ' : ‖psiCombo ℓ w‖ ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hZbw ?_
    have h1 : CZ * (Work.Kernels.scale w) ^ NZ
        ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_left _ _)) hCZ.le
    exact mul_le_mul h1 hexpZ (Real.exp_pos _).le
      (mul_nonneg hCZ.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hX' : ‖Work.Residues.Xfun w‖ ≤ CX * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hXbw ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)) hCX.le)
      (Real.exp_pos _).le
  have hcoc : psiCombo ℓ ((n : ℝ) +ᵥ w)
      = psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
    rcases hn with h | h
    · rw [h]; push_cast; rw [one_mul]; exact psiCombo_vadd_one ℓ w
    · rw [h]; push_cast; rw [neg_one_mul]; exact psiCombo_vadd_neg_one ℓ w
  have hcn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have hk : ‖(n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
      = Real.pi * ‖Work.Residues.Xfun w‖ := by
    rw [norm_mul, norm_mul, norm_mul, hcn, one_mul, Complex.norm_I, mul_one,
      Work.Asymptotics.EtailE.norm_pi]
  have h2 : Real.pi * ‖Work.Residues.Xfun w‖
      ≤ Real.pi * (CX * (Work.Kernels.scale w) ^ (max NZ NX)
          * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) :=
    mul_le_mul_of_nonneg_left hX' Real.pi_pos.le
  have h3 : ‖psiCombo ℓ w‖ + Real.pi * ‖Work.Residues.Xfun w‖
      ≤ (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    have h4 : CZ * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
          + Real.pi * (CX * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im))
        = (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
    exact le_trans (add_le_add hZ' h2) (le_of_eq h4)
  have hstep1 : ‖psiCombo ℓ ((n : ℝ) +ᵥ w)‖
      = ‖psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖ := by
    rw [hcoc]
  have hstep2 : ‖psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
      ≤ ‖psiCombo ℓ w‖ + Real.pi * ‖Work.Residues.Xfun w‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [hk]
  have hstep4 : (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
      = (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp (-(Real.pi * (ModularGroup.S • w).im)) := by
    rw [neg_mul]
  exact le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans h3 (le_of_eq hstep4)))

end

end Work.Asymptotics.Tile
