import Mathlib
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaDecay

namespace Work.Residues

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## Uniform bounds for the `τ`-factors appearing in `bracket24`

`bracket24 ℓ z τ` is a sum of three terms, each of which is a `z`-dependent factor times a
`τ`-dependent factor.  The `τ`-factors are all of "cusp type": modular forms (or the log
functions `𝓛`, `𝓛_S`) which grow at most linearly in `‖τ‖` on the region `Im τ ≥ H`.  We
record the individual bounds here and combine them.
-/

/-- From `CuspBound f 0 k` we get a uniform bound, since `tpar τ ≤ 1`. -/
lemma CuspBound.const_bdd {f : UpperHalfPlane → ℂ} {k : ℕ} (h : CuspBound f 0 k) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖f τ‖ ≤ C := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨H, C, hC, fun τ hτ => ?_⟩
  have h1 := hb τ hτ
  rw [pow_zero, mul_one] at h1
  have hk : tpar τ ^ k ≤ 1 := pow_le_one₀ (tpar_nonneg τ) (tpar_le_one τ)
  nlinarith [h1, hC.le, hk, tpar_nonneg τ]

/-- Linear growth bound for `ℓ.L`. -/
lemma L_lin (ℓ : LogLambdaData) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖ℓ.L τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨H, C, hC, h⟩ := L_cusp ℓ
  refine ⟨H, C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  simpa [pow_one, pow_zero, mul_one] using h1

/-- Uniform bound for `ℓ.L_S`. -/
lemma LS_bdd (ℓ : LogLambdaData) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖ℓ.L_S τ‖ ≤ C :=
  CuspBound.const_bdd (LS_cusp ℓ)

lemma X_bdd :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖Xfun τ‖ ≤ C :=
  CuspBound.const_bdd X_cusp

lemma Y_bdd :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖Yfun τ‖ ≤ C :=
  CuspBound.const_bdd Y_cusp

lemma Delta_bdd :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖DeltaFun τ‖ ≤ C :=
  CuspBound.const_bdd Delta_cusp

lemma B0core_bdd :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖B0core τ‖ ≤ C :=
  CuspBound.const_bdd B0core_cusp

lemma Ccore_bdd (ℓ : LogLambdaData) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im → ‖Ccore ℓ τ‖ ≤ C :=
  CuspBound.const_bdd (Ccore_cusp ℓ)

/-! ## Elementary norm lemmas -/

lemma norm_add_sub3_le (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc ‖a + b - c‖ ≤ ‖a + b‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
        have := norm_add_le a b; linarith
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring

lemma norm_add5_le (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

/-! ## The bound for `B'` -/

/-- `‖B' ℓ z τ‖ ≤ (A0 + A1 ‖j(z)‖) (1 + ‖τ‖)` for `Im τ ≥ H`, with `A0, A1` depending only
on `ℓ`. -/
lemma Bprime_bound (ℓ : LogLambdaData) :
    ∃ H A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧
      ∀ z τ : UpperHalfPlane, H ≤ τ.im →
        ‖Bprimefun ℓ z τ‖ ≤ (A0 + A1 * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨HL, CL, hCL, hL⟩ := L_lin ℓ
  obtain ⟨HS, CS, hCS, hS⟩ := LS_bdd ℓ
  obtain ⟨HB, CB, hCB, hB⟩ := B0core_bdd
  obtain ⟨HC, CC, hCC, hC⟩ := Ccore_bdd ℓ
  obtain ⟨HX, CX, hCX, hX⟩ := X_bdd
  obtain ⟨HY, CY, hCY, hY⟩ := Y_bdd
  obtain ⟨HD, CD, hCD, hD⟩ := Delta_bdd
  refine ⟨max HL (max HS (max HB (max HC (max HX (max HY (max HD 0)))))), CL * CB + CC,
      (2 * CL * CX + 2 * CS * CY + 3456 * CD), ?_, ?_, ?_⟩
  · have := mul_nonneg hCL.le hCB.le; linarith [hCC.le, this]
  · have h1 := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hCL.le hCX.le)
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hCS.le hCY.le)
    have h3 := mul_nonneg (by norm_num : (0:ℝ) ≤ 3456) hCD.le
    linarith
  intro z τ hτ
  simp only [max_le_iff] at hτ
  obtain ⟨hτL, hτS, hτB, hτC, hτX, hτY, hτD, _⟩ := hτ
  have h1 : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := hL τ hτL
  have h2 : ‖ℓ.L_S τ‖ ≤ CS := hS τ hτS
  have h3 : ‖B0core τ‖ ≤ CB := hB τ hτB
  have h4 : ‖Ccore ℓ τ‖ ≤ CC := hC τ hτC
  have h5 : ‖Xfun τ‖ ≤ CX := hX τ hτX
  have h6 : ‖Yfun τ‖ ≤ CY := hY τ hτY
  have h7 : ‖DeltaFun τ‖ ≤ CD := hD τ hτD
  have hz : (0 : ℝ) ≤ ‖jInvariantFun z‖ := norm_nonneg _
  have hS1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := one_le_one_add_norm τ
  have hS1n : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have e1 : ‖ℓ.L τ * B0core τ‖ ≤ CL * CB * (1 + ‖(τ : ℂ)‖) := by
    rw [norm_mul]
    calc ‖ℓ.L τ‖ * ‖B0core τ‖ ≤ (CL * (1 + ‖(τ : ℂ)‖)) * CB :=
          mul_le_mul h1 h3 (norm_nonneg _) (mul_nonneg hCL.le hS1n)
      _ = CL * CB * (1 + ‖(τ : ℂ)‖) := by ring
  have e2 : ‖2 * jInvariantFun z * (ℓ.L τ * Xfun τ)‖
      ≤ 2 * ‖jInvariantFun z‖ * CL * CX * (1 + ‖(τ : ℂ)‖) := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    calc (2 * ‖jInvariantFun z‖) * (‖ℓ.L τ‖ * ‖Xfun τ‖)
        ≤ (2 * ‖jInvariantFun z‖) * ((CL * (1 + ‖(τ : ℂ)‖)) * CX) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h5 (norm_nonneg _) (mul_nonneg hCL.le hS1n))
            (mul_nonneg (by norm_num) hz)
      _ = 2 * ‖jInvariantFun z‖ * CL * CX * (1 + ‖(τ : ℂ)‖) := by ring
  have e4 : ‖2 * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖
      ≤ 2 * ‖jInvariantFun z‖ * CS * CY := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    calc (2 * ‖jInvariantFun z‖) * (‖ℓ.L_S τ‖ * ‖Yfun τ‖)
        ≤ (2 * ‖jInvariantFun z‖) * (CS * CY) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h6 (norm_nonneg _) hCS.le)
            (mul_nonneg (by norm_num) hz)
      _ = 2 * ‖jInvariantFun z‖ * CS * CY := by ring
  have e5 : ‖3456 * DeltaFun τ * jInvariantFun z‖ ≤ 3456 * CD * ‖jInvariantFun z‖ := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    calc (3456 * ‖DeltaFun τ‖) * ‖jInvariantFun z‖ ≤ (3456 * CD) * ‖jInvariantFun z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (by norm_num)) hz
      _ = 3456 * CD * ‖jInvariantFun z‖ := by ring
  calc ‖Bprimefun ℓ z τ‖
      ≤ ‖ℓ.L τ * B0core τ‖ + ‖2 * jInvariantFun z * (ℓ.L τ * Xfun τ)‖ + ‖Ccore ℓ τ‖
        + ‖2 * jInvariantFun z * (ℓ.L_S τ * Yfun τ)‖ + ‖3456 * DeltaFun τ * jInvariantFun z‖ := by
          simp only [Bprimefun]
          exact norm_add5_le _ _ _ _ _
    _ ≤ CL * CB * (1 + ‖(τ : ℂ)‖) + 2 * ‖jInvariantFun z‖ * CL * CX * (1 + ‖(τ : ℂ)‖) + CC
        + 2 * ‖jInvariantFun z‖ * CS * CY + 3456 * CD * ‖jInvariantFun z‖ := by
          linarith [e1, e2, h4, e4, e5]
    _ ≤ (CL * CB + CC + (2 * CL * CX + 2 * CS * CY + 3456 * CD) * ‖jInvariantFun z‖)
          * (1 + ‖(τ : ℂ)‖) := by
          have hbCC : CC ≤ CC * (1 + ‖(τ : ℂ)‖) := le_mul_of_one_le_right hCC.le hS1
          have hb2 : (2 * ‖jInvariantFun z‖ * CS * CY)
              ≤ (2 * ‖jInvariantFun z‖ * CS * CY) * (1 + ‖(τ : ℂ)‖) :=
            le_mul_of_one_le_right
              (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hz) hCS.le) hCY.le) hS1
          have hb3 : (3456 * CD * ‖jInvariantFun z‖)
              ≤ (3456 * CD * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖) :=
            le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3456) hCD.le) hz) hS1
          nlinarith [hbCC, hb2, hb3]

/-! ## The bound for `psi₄E₈ - psi₂E₁₀` -/

lemma P_bound (ℓ : LogLambdaData) :
    ∃ H K : ℝ, 0 ≤ K ∧ ∀ τ : UpperHalfPlane, H ≤ τ.im →
      ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ ≤ K * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨HL, CL, hCL, hL⟩ := L_lin ℓ
  obtain ⟨HS, CS, hCS, hS⟩ := LS_bdd ℓ
  obtain ⟨HX, CX, hCX, hX⟩ := X_bdd
  obtain ⟨HY, CY, hCY, hY⟩ := Y_bdd
  refine ⟨max HL (max HS (max HX (max HY 0))), CL * CX + CS * CY, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hCL.le hCX.le) (mul_nonneg hCS.le hCY.le)
  intro τ hτ
  rw [psi4E8_sub]
  simp only [max_le_iff] at hτ
  obtain ⟨hτL, hτS, hτX, hτY, _⟩ := hτ
  have h1 : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := hL τ hτL
  have h2 : ‖ℓ.L_S τ‖ ≤ CS := hS τ hτS
  have h3 : ‖Xfun τ‖ ≤ CX := hX τ hτX
  have h4 : ‖Yfun τ‖ ≤ CY := hY τ hτY
  have hS1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := one_le_one_add_norm τ
  have hS1n : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have e1 : ‖ℓ.L τ * Xfun τ‖ ≤ CL * CX * (1 + ‖(τ : ℂ)‖) := by
    rw [norm_mul]
    calc ‖ℓ.L τ‖ * ‖Xfun τ‖ ≤ (CL * (1 + ‖(τ : ℂ)‖)) * CX :=
          mul_le_mul h1 h3 (norm_nonneg _) (mul_nonneg hCL.le hS1n)
      _ = CL * CX * (1 + ‖(τ : ℂ)‖) := by ring
  have e2 : ‖ℓ.L_S τ * Yfun τ‖ ≤ CS * CY := by
    rw [norm_mul]
    exact mul_le_mul h2 h4 (norm_nonneg _) hCS.le
  calc ‖ℓ.L τ * Xfun τ + ℓ.L_S τ * Yfun τ‖
      ≤ ‖ℓ.L τ * Xfun τ‖ + ‖ℓ.L_S τ * Yfun τ‖ := norm_add_le _ _
    _ ≤ CL * CX * (1 + ‖(τ : ℂ)‖) + CS * CY := add_le_add e1 e2
    _ ≤ (CL * CX + CS * CY) * (1 + ‖(τ : ℂ)‖) := by
          have hcc : CS * CY ≤ CS * CY * (1 + ‖(τ : ℂ)‖) :=
            le_mul_of_one_le_right (mul_nonneg hCS.le hCY.le) hS1
          nlinarith [hcc]

theorem bracket24_uniform (ℓ : Work.Kernels.LogLambdaData) :
    ∃ H K0 K1 K2 K3 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ K3 ∧
      ∀ (z τ : UpperHalfPlane), H ≤ τ.im →
        ‖Work.Residues.bracket24 ℓ z τ‖ ≤
          (K0 * ‖Work.Kernels.WFun z‖
            + K1 * ‖Work.Kernels.WFun z‖ * ‖Work.Kernels.jInvariantFun z‖
            + K2 * ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z‖
                * ‖Work.Kernels.UFun z ^ 2 - Work.Kernels.VFun z ^ 2‖
            + K3 * ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z‖
                * ‖ℓ.L z‖) * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨Hb, A0, A1, hA0, hA1, hb⟩ := Bprime_bound ℓ
  obtain ⟨Hp, K2c, hK2c, hp⟩ := P_bound ℓ
  obtain ⟨Hd, CD, hCD, hD⟩ := Delta_bdd
  refine ⟨max Hb (max Hp Hd), A0, A1, K2c, 3456 * CD, hA0, hA1, hK2c,
      mul_nonneg (by norm_num) hCD.le, ?_⟩
  intro z τ hτ
  have hτb : Hb ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτpd : max Hp Hd ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hτp : Hp ≤ τ.im := le_trans (le_max_left _ _) hτpd
  have hτd : Hd ≤ τ.im := le_trans (le_max_right _ _) hτpd
  have hbnd := hb z τ hτb
  have hpnd := hp τ hτp
  have hdbnd : ‖DeltaFun τ‖ ≤ CD := hD τ hτd
  have hS1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := one_le_one_add_norm τ
  have hAB : ‖bracket24 ℓ z τ‖ ≤
      ‖WFun z * BprimeExp ℓ z τ‖
        + ‖(E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)
            * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
        + ‖3456 * DeltaFun τ * (E14Fun z / DeltaFun z) * ℓ.L z‖ := by
    simp only [bracket24]
    exact norm_add_sub3_le _ _ _
  have hT1 : ‖WFun z * BprimeExp ℓ z τ‖
      ≤ (A0 * ‖WFun z‖ + A1 * ‖WFun z‖ * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖) := by
    rw [← Bprimefun_eq ℓ z τ, norm_mul]
    calc ‖WFun z‖ * ‖Bprimefun ℓ z τ‖
        ≤ ‖WFun z‖ * ((A0 + A1 * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖)) :=
          mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
      _ = (A0 * ‖WFun z‖ + A1 * ‖WFun z‖ * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖) := by ring
  have hT2 : ‖(E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)
        * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ (K2c * ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖) * (1 + ‖(τ : ℂ)‖) := by
    rw [norm_mul, norm_mul]
    calc ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖
          * ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
        ≤ ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖ * (K2c * (1 + ‖(τ : ℂ)‖)) :=
          mul_le_mul_of_nonneg_left hpnd (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (K2c * ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖) * (1 + ‖(τ : ℂ)‖) := by ring
  have hT3 : ‖3456 * DeltaFun τ * (E14Fun z / DeltaFun z) * ℓ.L z‖
      ≤ (3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖) * (1 + ‖(τ : ℂ)‖) := by
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    calc 3456 * ‖DeltaFun τ‖ * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖
        ≤ 3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖ := by gcongr
      _ ≤ 3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖ * (1 + ‖(τ : ℂ)‖) :=
          le_mul_of_one_le_right
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCD.le) (norm_nonneg _))
              (norm_nonneg _)) hS1
      _ = (3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖) * (1 + ‖(τ : ℂ)‖) := by ring
  calc ‖bracket24 ℓ z τ‖
      ≤ ‖WFun z * BprimeExp ℓ z τ‖
          + ‖(E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)
              * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          + ‖3456 * DeltaFun τ * (E14Fun z / DeltaFun z) * ℓ.L z‖ := hAB
    _ ≤ (A0 * ‖WFun z‖ + A1 * ‖WFun z‖ * ‖jInvariantFun z‖) * (1 + ‖(τ : ℂ)‖)
          + (K2c * ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖) * (1 + ‖(τ : ℂ)‖)
          + (3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖) * (1 + ‖(τ : ℂ)‖) :=
          add_le_add (add_le_add hT1 hT2) hT3
    _ = (A0 * ‖WFun z‖ + A1 * ‖WFun z‖ * ‖jInvariantFun z‖
          + K2c * ‖E10Fun z / DeltaFun z‖ * ‖UFun z ^ 2 - VFun z ^ 2‖
          + 3456 * CD * ‖E14Fun z / DeltaFun z‖ * ‖ℓ.L z‖) * (1 + ‖(τ : ℂ)‖) := by ring

end

end Work.Residues
