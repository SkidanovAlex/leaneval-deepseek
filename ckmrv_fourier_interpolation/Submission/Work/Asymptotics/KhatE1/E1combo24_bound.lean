/-
# The `E¹`-coefficient of the `d = 24` funnel bracket is `O(‖q‖)`

The sharp funnel bound for the `d = 24` tail (`Khat_funnel_tail_sharp_core`) needs the
coefficient `E1combo24 = kmfd_c1` of the first power of `Ept z` in the reference bracket
`kmfd_BR` to be `O(‖q(τ)‖ (scale τ)^N)` on the funnel -- one power of `q` *better* than the
individual `τ`-atoms `ψ₂E₁₀`, `ψ₄E₈`, `jΔ`, `Δ` are bounded by.

The mechanism is a cusp cancellation: with `Z = Ept τ = e^{πiτ}` (`‖Z‖ = tpar τ` and
`‖q(τ)‖ = tpar τ²`) the first-order coefficient splits as

  `E1combo24 = 27648·E₄³ - 20570112·Δ + 𝓛·A₁ + 𝓛_S·A₂`,

and after multiplication by `Δ` (which turns `Δj` into `E₄³`)

  `Δ·E1combo24 = Num1 + 𝓛·Num2`

with `Num2 = -8E₄²Ñ - 15744ΔX` and `Num1` as in `Num1` below.  Expanding `Num1` in the cusp
parameter `Z` (`Num1_decomp`) exhibits `Num1` as a sum of products each carrying at least four
powers of `Z`; then `CuspBound_Num1`, `CuspBound_Num2` and the library `CuspBound` calculus
give `‖Δ·E1combo24‖ ≤ C (scale τ) (tpar τ)⁴`, and dividing by `Δ` (bounded below by `tpar²`
on the funnel) yields the claim.
-/
import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.KMinusFunnelJAtoms
import Submission.Work.Asymptotics.Yfun_third_order
import Submission.Work.Asymptotics.Delta_xi4prime_E8_third_order
import Submission.Work.Asymptotics.Funnel24Tail.Tref24FunnelBound

set_option linter.unusedVariables false

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## The two combinations `Num1`, `Num2` -/

/-- `ξ₄' = (ξ₄|₄S) = U² + V² - 2W²`. -/
def Xi4S (τ : ℍ) : ℂ := UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2

/-- `Δ - Z²` with `Z = Ept τ`. -/
def DeltaRem (τ : ℍ) : ℂ := DeltaFun τ - (Work.Residues.Ept τ) ^ 2

/-- `E₄³ - 1`. -/
def E4cubeRem (τ : ℍ) : ℂ := E4Fun τ ^ 3 - 1

/-- `𝓛_S + 16Z`. -/
def LSRem (ℓ : LogLambdaData) (τ : ℍ) : ℂ := ℓ.L_S τ + 16 * Work.Residues.Ept τ

/-- `Y - (72Z - 576Z²)`. -/
def YRem (τ : ℍ) : ℂ := Work.Residues.Yfun τ
  - (72 * Work.Residues.Ept τ - 576 * (Work.Residues.Ept τ) ^ 2)

/-- `Δ·ξ₄'E₈ + Z²`. -/
def DxiRem (τ : ℍ) : ℂ := DeltaFun τ * (Xi4S τ * E8Fun τ) + (Work.Residues.Ept τ) ^ 2

/-- The `𝓛`-coefficient of `Δ·E1combo24`, namely `-8E₄²Ñ - 15744ΔX`. -/
def Num2 (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  -8 * E4Fun τ ^ 2 * Work.Residues.Ntfun τ - 15744 * DeltaFun τ * Work.Residues.Xfun τ

/-- The `𝓛`-free part of `Δ·E1combo24`. -/
def Num1 (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  DeltaFun τ * (27648 * E4Fun τ ^ 3 - 20570112 * DeltaFun τ)
    + ℓ.L_S τ * ((24 * E4Fun τ ^ 3 - 15744 * DeltaFun τ) * Work.Residues.Yfun τ
        - 13824 * DeltaFun τ * (Xi4S τ * E8Fun τ))

/-- **The decomposition of `Δ·E1combo24`.**  With `X = ξ₄E₈ - ξ₂E₁₀`,
`Y = ξ₄'E₈ + (U+V)E₁₀` and `Ñ = 3ξ₂E₄²E₆ - 2ξ₄E₄³ - ξ₄E₆²` (the library's `Xfun`,
`Yfun`, `Ntfun`), the quantity `E1combo24` splits as `Num1 + 𝓛·Num2` after multiplication
by `Δ`: the `j`-factors are absorbed by `jΔ = E₄³`, and the relation `1728Δ = E₄³ - E₆²`
turns the `𝓛`-coefficient into a combination of `X` and `Ñ`. -/
lemma Delta_mul_E1combo24 (ℓ : LogLambdaData) (τ : ℍ) :
    DeltaFun τ * E1combo24 ℓ τ = Num1 ℓ τ + ℓ.L τ * Num2 ℓ τ := by
  have hrel : (1728 : ℂ) * DeltaFun τ = E4Fun τ ^ 3 - E6Fun τ ^ 2 := Work.Residues.discr_eq τ
  have hΔeq : DeltaFun τ = (E4Fun τ ^ 3 - E6Fun τ ^ 2) / 1728 := by
    rw [eq_div_iff (by norm_num : (1728 : ℂ) ≠ 0)]
    linear_combination hrel
  have ha : psi2 ℓ τ * E10Fun τ
      = (xi2Fun τ * E10Fun τ) * ℓ.L τ - ((UFun τ + VFun τ) * E10Fun τ) * ℓ.L_S τ := by
    simp only [psi2, Work.Residues.xi2Fun_slash_S_apply]
    ring
  have hb : psi4 ℓ τ * E8Fun τ
      = (xi4Fun τ * E8Fun τ) * ℓ.L τ + (Xi4S τ * E8Fun τ) * ℓ.L_S τ := by
    simp only [psi4, Xi4S, Work.Residues.xi4Fun_slash_S_apply]
    ring
  have hX : Work.Residues.Xfun τ = xi4Fun τ * E8Fun τ - xi2Fun τ * E10Fun τ := rfl
  have hY : Work.Residues.Yfun τ
      = Xi4S τ * E8Fun τ + (UFun τ + VFun τ) * E10Fun τ := by
    simp only [Work.Residues.Yfun, Xi4S, Work.Residues.xi4Fun_slash_S_apply,
      Work.Residues.xi2Fun_slash_S_apply]
    ring
  have hN : Work.Residues.Ntfun τ
      = -2 * xi4Fun τ * E4Fun τ ^ 3 + 3 * xi2Fun τ * E4Fun τ ^ 2 * E6Fun τ
        - xi4Fun τ * E6Fun τ ^ 2 := rfl
  rw [E1combo24]
  rw [show DeltaFun τ * (27648 * (jInvariantFun τ * DeltaFun τ)
        - 24 * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
        + 24 * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)) - 20570112 * DeltaFun τ
        + 15744 * (psi2 ℓ τ * E10Fun τ) - 29568 * (psi4 ℓ τ * E8Fun τ))
      = 27648 * (DeltaFun τ * jInvariantFun τ) * DeltaFun τ
        - 24 * (DeltaFun τ * jInvariantFun τ) * (psi2 ℓ τ * E10Fun τ)
        + 24 * (DeltaFun τ * jInvariantFun τ) * (psi4 ℓ τ * E8Fun τ)
        - 20570112 * DeltaFun τ ^ 2
        + 15744 * DeltaFun τ * (psi2 ℓ τ * E10Fun τ)
        - 29568 * DeltaFun τ * (psi4 ℓ τ * E8Fun τ) from by ring]
  rw [ClassicalFacts.DeltaFun_mul_jInvariantFun τ]
  simp only [Num1, Num2, ha, hb, hX, hY, hN, Xi4S, E8Fun, E10Fun,
    xi2Fun, xi4Fun, UFun, WFun, VFun]
  rw [hΔeq]
  ring

/-- **The cusp decomposition of `Num1`.**  With `ρ = Δ - Z²`, `τ₃ = 𝓛_S + 16Z`,
`υ = Y - (72Z - 576Z²)` and `ω = Δ·ξ₄'E₈ + Z²`, the coefficient `Num1` of `Δ·E1combo24`
equals

`221184(E₄³-1)Z³ + 24E₄³(1152ρ + τ₃Y - 16Zυ) + 221184Zω + 13824τ₃Z² - 13824τ₃ω - 20570112Δ² - 15744𝓛_SΔY`,

a sum of products each carrying at least four powers of `Z`: the terms of order `Z²` and `Z³`
present before the regrouping cancel exactly. -/
lemma Num1_decomp (ℓ : LogLambdaData) (τ : ℍ) :
    Num1 ℓ τ
      = 221184 * (E4cubeRem τ * (Work.Residues.Ept τ) ^ 3)
        + (24 * (E4Fun τ ^ 3 * ((1152 * DeltaRem τ + LSRem ℓ τ * Work.Residues.Yfun τ)
              + (-16) * (Work.Residues.Ept τ * YRem τ)))
          + (221184 * (Work.Residues.Ept τ * DxiRem τ)
            + (13824 * (LSRem ℓ τ * (Work.Residues.Ept τ) ^ 2)
              + ((-13824) * (LSRem ℓ τ * DxiRem τ)
                + ((-20570112) * (DeltaFun τ * DeltaFun τ)
                  + ((-15744) * (ℓ.L_S τ * (DeltaFun τ * Work.Residues.Yfun τ)))))))) := by
  simp only [Num1, DeltaRem, E4cubeRem, LSRem, YRem, DxiRem]
  ring

/-! ## The cusp atoms and their `CuspBound`s -/

lemma CuspBound_Ept : Work.Residues.CuspBound (fun τ : ℍ => Work.Residues.Ept τ) 0 1 := by
  refine ⟨1, 1, one_pos, fun τ _ => ?_⟩
  simp only [pow_zero, pow_one, mul_one, one_mul, Work.Residues.tpar_eq_norm_Ept, le_refl]

lemma CuspBound_ept_pow (n : ℕ) :
    Work.Residues.CuspBound (fun τ : ℍ => (Work.Residues.Ept τ) ^ n) 0 n := by
  induction n with
  | zero =>
      refine ⟨1, 1, one_pos, fun τ _ => ?_⟩
      simp only [pow_zero, mul_one, norm_one, le_refl]
  | succ k ih =>
      have h := Work.Residues.CuspBound.mul ih CuspBound_Ept
      simpa [pow_succ] using h

lemma CuspBound_DeltaRem : Work.Residues.CuspBound DeltaRem 0 4 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.DeltaExpansion
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  rw [pow_zero, mul_one]
  calc ‖DeltaRem τ‖ = ‖DeltaFun τ - (Work.Residues.Ept τ) ^ 2‖ := rfl
    _ ≤ C * ‖Work.Residues.Ept τ‖ ^ 4 := h τ hτ
    _ = C * Work.Residues.tpar τ ^ 4 := by rw [Work.Residues.tpar_eq_norm_Ept]

lemma CuspBound_E4cubeRem : Work.Residues.CuspBound E4cubeRem 0 2 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4cube_cusp_second
  have hC0 : (0 : ℝ) ≤ C := hC.le
  refine ⟨1, 720 + C, by positivity, fun τ hτ => ?_⟩
  rw [pow_zero, mul_one]
  have ht1 : Work.Residues.tpar τ ≤ 1 := Work.Residues.tpar_le_one τ
  have ht0 : 0 ≤ Work.Residues.tpar τ := Work.Residues.tpar_nonneg τ
  have hq : ‖qParamFun τ‖ = Work.Residues.tpar τ ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, ← Work.Residues.tpar_pow_two]
  have hkey : E4cubeRem τ
      = (E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) + 720 * qParamFun τ := by
    simp only [E4cubeRem]; ring
  have h1 := h τ hτ
  rw [hq] at h1
  have h2 : ‖720 * qParamFun τ‖ = 720 * Work.Residues.tpar τ ^ 2 := by
    rw [norm_mul, hq, Complex.norm_ofNat]
  have h3 : Work.Residues.tpar τ ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
  have h4 : (Work.Residues.tpar τ ^ 2) ^ 2 ≤ Work.Residues.tpar τ ^ 2 := by
    nlinarith [h3, sq_nonneg (Work.Residues.tpar τ ^ 2)]
  rw [hkey]
  calc ‖(E4Fun τ ^ 3 - 1 - 720 * qParamFun τ) + 720 * qParamFun τ‖
      ≤ ‖E4Fun τ ^ 3 - 1 - 720 * qParamFun τ‖ + ‖720 * qParamFun τ‖ := norm_add_le _ _
    _ ≤ C * (Work.Residues.tpar τ ^ 2) ^ 2 + 720 * Work.Residues.tpar τ ^ 2 := by
        rw [h2]; exact add_le_add h1 le_rfl
    _ ≤ (720 + C) * Work.Residues.tpar τ ^ 2 := by nlinarith [h4, hC0, ht0]

lemma CuspBound_LSRem (ℓ : LogLambdaData) : Work.Residues.CuspBound (LSRem ℓ) 0 3 := by
  obtain ⟨C, hC, h⟩ := (Work.Residues.ThetaExpansion).2.2.2 ℓ
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  rw [pow_zero, mul_one]
  calc ‖LSRem ℓ τ‖ = ‖ℓ.L_S τ + 16 * Work.Residues.Ept τ‖ := rfl
    _ ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := h τ hτ
    _ = C * Work.Residues.tpar τ ^ 3 := by rw [Work.Residues.tpar_eq_norm_Ept]

lemma CuspBound_YRem : Work.Residues.CuspBound YRem 0 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.Yfun_third_order
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  rw [pow_zero, mul_one]
  calc ‖YRem τ‖ = ‖Work.Residues.Yfun τ
        - (72 * Work.Residues.Ept τ - 576 * (Work.Residues.Ept τ) ^ 2)‖ := rfl
    _ ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := h τ hτ
    _ = C * Work.Residues.tpar τ ^ 3 := by rw [Work.Residues.tpar_eq_norm_Ept]

lemma CuspBound_DxiRem : Work.Residues.CuspBound DxiRem 0 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.Delta_xi4prime_E8_third_order
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  rw [pow_zero, mul_one]
  calc ‖DxiRem τ‖ = ‖DeltaFun τ
        * ((UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2) * E8Fun τ)
        + (Work.Residues.Ept τ) ^ 2‖ := rfl
    _ ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := h τ hτ
    _ = C * Work.Residues.tpar τ ^ 3 := by rw [Work.Residues.tpar_eq_norm_Ept]

lemma CuspBound_E4cube : Work.Residues.CuspBound (fun τ : ℍ => E4Fun τ ^ 3) 0 0 := by
  have h := Work.Residues.CuspBound.mul
    (Work.Residues.CuspBound.mul Work.Residues.E4_cusp Work.Residues.E4_cusp)
    Work.Residues.E4_cusp
  convert h using 1
  funext τ; ring

lemma CuspBound_E4sq : Work.Residues.CuspBound (fun τ : ℍ => E4Fun τ * E4Fun τ) 0 0 :=
  Work.Residues.CuspBound.mul Work.Residues.E4_cusp Work.Residues.E4_cusp

/-! ## The bounds for `Num1` and `Num2` -/

lemma CuspBound_Num1 (ℓ : LogLambdaData) : Work.Residues.CuspBound (Num1 ℓ) 0 4 := by
  have h1 : Work.Residues.CuspBound (fun τ : ℍ =>
      221184 * (E4cubeRem τ * (Work.Residues.Ept τ) ^ 3)) 0 4 :=
    Work.Residues.CuspBound.mono
      (Work.Residues.CuspBound.const_mul 221184
        (Work.Residues.CuspBound.mul CuspBound_E4cubeRem (CuspBound_ept_pow 3)))
      (le_refl 0) (by norm_num)
  have hbr : Work.Residues.CuspBound (fun τ : ℍ =>
      (1152 * DeltaRem τ + LSRem ℓ τ * Work.Residues.Yfun τ)
        + (-16) * (Work.Residues.Ept τ * YRem τ)) 0 4 :=
    Work.Residues.CuspBound.add
      (Work.Residues.CuspBound.add
        (Work.Residues.CuspBound.const_mul 1152 CuspBound_DeltaRem)
        (Work.Residues.CuspBound.mul (CuspBound_LSRem ℓ) Work.Residues.Y_cusp))
      (Work.Residues.CuspBound.const_mul (-16)
        (Work.Residues.CuspBound.mul CuspBound_Ept CuspBound_YRem))
  have h2 : Work.Residues.CuspBound (fun τ : ℍ =>
      24 * (E4Fun τ ^ 3 * ((1152 * DeltaRem τ + LSRem ℓ τ * Work.Residues.Yfun τ)
        + (-16) * (Work.Residues.Ept τ * YRem τ)))) 0 4 :=
    Work.Residues.CuspBound.const_mul 24
      (Work.Residues.CuspBound.mul CuspBound_E4cube hbr)
  have h3 : Work.Residues.CuspBound (fun τ : ℍ =>
      221184 * (Work.Residues.Ept τ * DxiRem τ)) 0 4 :=
    Work.Residues.CuspBound.const_mul 221184
      (Work.Residues.CuspBound.mul CuspBound_Ept CuspBound_DxiRem)
  have h4 : Work.Residues.CuspBound (fun τ : ℍ =>
      13824 * (LSRem ℓ τ * (Work.Residues.Ept τ) ^ 2)) 0 4 :=
    Work.Residues.CuspBound.mono
      (Work.Residues.CuspBound.const_mul 13824
        (Work.Residues.CuspBound.mul (CuspBound_LSRem ℓ) (CuspBound_ept_pow 2)))
      (le_refl 0) (by norm_num)
  have h5 : Work.Residues.CuspBound (fun τ : ℍ =>
      (-13824) * (LSRem ℓ τ * DxiRem τ)) 0 4 :=
    Work.Residues.CuspBound.mono
      (Work.Residues.CuspBound.const_mul (-13824)
        (Work.Residues.CuspBound.mul (CuspBound_LSRem ℓ) CuspBound_DxiRem))
      (le_refl 0) (by norm_num)
  have h6 : Work.Residues.CuspBound (fun τ : ℍ =>
      (-20570112) * (DeltaFun τ * DeltaFun τ)) 0 4 :=
    Work.Residues.CuspBound.const_mul (-20570112)
      (Work.Residues.CuspBound.mul Work.Residues.Delta_cusp Work.Residues.Delta_cusp)
  have h7 : Work.Residues.CuspBound (fun τ : ℍ =>
      (-15744) * (ℓ.L_S τ * (DeltaFun τ * Work.Residues.Yfun τ))) 0 4 :=
    Work.Residues.CuspBound.const_mul (-15744)
      (Work.Residues.CuspBound.mul (Work.Residues.LS_cusp ℓ)
        (Work.Residues.CuspBound.mul Work.Residues.Delta_cusp Work.Residues.Y_cusp))
  have hall := Work.Residues.CuspBound.add h1 (Work.Residues.CuspBound.add h2
    (Work.Residues.CuspBound.add h3 (Work.Residues.CuspBound.add h4
      (Work.Residues.CuspBound.add h5 (Work.Residues.CuspBound.add h6 h7)))))
  rw [show Num1 ℓ = fun τ : ℍ =>
        221184 * (E4cubeRem τ * (Work.Residues.Ept τ) ^ 3)
          + (24 * (E4Fun τ ^ 3 * ((1152 * DeltaRem τ + LSRem ℓ τ * Work.Residues.Yfun τ)
                + (-16) * (Work.Residues.Ept τ * YRem τ)))
            + (221184 * (Work.Residues.Ept τ * DxiRem τ)
              + (13824 * (LSRem ℓ τ * (Work.Residues.Ept τ) ^ 2)
                + ((-13824) * (LSRem ℓ τ * DxiRem τ)
                  + ((-20570112) * (DeltaFun τ * DeltaFun τ)
                    + ((-15744) * (ℓ.L_S τ * (DeltaFun τ * Work.Residues.Yfun τ))))))))
      from funext fun τ => Num1_decomp ℓ τ]
  exact hall

lemma CuspBound_Num2 (ℓ : LogLambdaData) : Work.Residues.CuspBound (Num2 ℓ) 0 4 := by
  have h1 : Work.Residues.CuspBound (fun τ : ℍ =>
      (-8) * (E4Fun τ * E4Fun τ * Work.Residues.Ntfun τ)) 0 4 :=
    Work.Residues.CuspBound.const_mul (-8)
      (Work.Residues.CuspBound.mul CuspBound_E4sq Work.Residues.Nt_cusp)
  have h2 : Work.Residues.CuspBound (fun τ : ℍ =>
      (-15744) * (DeltaFun τ * Work.Residues.Xfun τ)) 0 4 :=
    Work.Residues.CuspBound.const_mul (-15744)
      (Work.Residues.CuspBound.mul Work.Residues.Delta_cusp Work.Residues.X_cusp)
  have hall := Work.Residues.CuspBound.add h1 h2
  rw [show Num2 ℓ = fun τ : ℍ => (-8) * (E4Fun τ * E4Fun τ * Work.Residues.Ntfun τ)
        + (-15744) * (DeltaFun τ * Work.Residues.Xfun τ) from by
    funext τ; simp only [Num2]; ring]
  exact hall

lemma CuspBound_Delta_mul_E1combo24 (ℓ : LogLambdaData) :
    Work.Residues.CuspBound (fun τ : ℍ => DeltaFun τ * E1combo24 ℓ τ) 1 4 := by
  have hall := Work.Residues.CuspBound.add (CuspBound_Num1 ℓ)
    (Work.Residues.CuspBound.mul (Work.Residues.L_cusp ℓ) (CuspBound_Num2 ℓ))
  rw [show (fun τ : ℍ => DeltaFun τ * E1combo24 ℓ τ)
        = fun τ : ℍ => Num1 ℓ τ + ℓ.L τ * Num2 ℓ τ from
      funext fun τ => Delta_mul_E1combo24 ℓ τ]
  exact hall

lemma CuspBound_E1combo24 (ℓ : LogLambdaData) :
    Work.Residues.CuspBound (E1combo24 ℓ) 1 2 := by
  obtain ⟨H, C, hC, h⟩ := Work.Residues.CuspBound.div_of_lower
    (f := fun τ : ℍ => DeltaFun τ * E1combo24 ℓ τ)
    (g := fun τ : ℍ => DeltaFun τ) (m := 1) (k := 4) (H0 := 2) (c := 1 / 2)
    (by norm_num) (CuspBound_Delta_mul_E1combo24 ℓ) (by norm_num)
    (fun τ hτ => by
      have hlow := (Work.FunnelNumerics.Delta_funnel_bounds).1 τ hτ
      rw [Work.Asymptotics.norm_qParamFun, ← Work.Residues.tpar_pow_two] at hlow
      exact hlow)
  refine ⟨H, C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have heq : (fun τ : ℍ => DeltaFun τ * E1combo24 ℓ τ / DeltaFun τ) τ = E1combo24 ℓ τ := by
    show DeltaFun τ * E1combo24 ℓ τ / DeltaFun τ = E1combo24 ℓ τ
    exact mul_div_cancel_left₀ (E1combo24 ℓ τ) (ClassicalFacts.DeltaFun_ne_zero τ)
  rw [heq] at h1
  simpa using h1


/-! ## The sharp estimate and the final bound -/

/-- The sharp estimate: on `{Im τ ≥ H}` (for suitable `H`) the coefficient `E1combo24` is
`O((scale τ) ‖q(τ)‖)`. -/
lemma E1combo24_sharp (ℓ : LogLambdaData) :
    ∃ H C : ℝ, 2 ≤ H ∧ 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
      ‖E1combo24 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) * Work.Residues.tpar τ ^ 2 := by
  obtain ⟨H, C, hC, h⟩ := CuspBound_E1combo24 ℓ
  exact ⟨max H 2, C, le_max_right _ _, hC, fun τ hτ =>
    by simpa [pow_one] using h τ (le_trans (le_max_left _ _) hτ)⟩

/-- The crude bound on the funnel: `E1combo24 = R24_p0` is bounded by a power of `scale`. -/
lemma E1combo24_crude (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖E1combo24 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.Funnel24Tail.R24_p0_bound ℓ
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  have heq : E1combo24 ℓ τ = Compact.R24_p0 ℓ τ := by
    simp only [E1combo24, Compact.R24_p0]
    ring
  rw [heq]
  exact h τ hτ

/-- **The sharp funnel bound for the `d = 24` `E¹`-coefficient.** -/
theorem E1combo24_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.E1combo24 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C₀, N₀, hC₀, hN₀, hcrude⟩ := E1combo24_crude ℓ
  obtain ⟨H, C₁, hH, hC₁, hsharp⟩ := E1combo24_sharp ℓ
  have hExp : 0 < Real.exp (2 * Real.pi * H) := Real.exp_pos _
  refine ⟨max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1, max N₀ 1,
    by positivity, by positivity, fun τ hτ => ?_⟩
  have hscale1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hscale0 : (0 : ℝ) ≤ scale τ := (scale_pos τ).le
  have hq : ‖qParamFun τ‖ = Work.Residues.tpar τ ^ 2 := by
    rw [Work.Asymptotics.norm_qParamFun, ← Work.Residues.tpar_pow_two]
  have hN1 : (1 : ℝ) ≤ max N₀ 1 := le_max_right _ _
  have hscaleN : scale τ ≤ (scale τ) ^ (max N₀ 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hscale1 hN1
    rwa [Real.rpow_one] at h
  have hCN : C₁ ≤ max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1 := by
    have := le_max_left C₁ (C₀ * Real.exp (2 * Real.pi * H)); linarith
  have hC0N : C₀ * Real.exp (2 * Real.pi * H)
      ≤ max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1 := by
    have := le_max_right C₁ (C₀ * Real.exp (2 * Real.pi * H)); linarith
  rcases le_or_gt H τ.im with hHi | hHi
  · have h1 := hsharp τ hHi
    have hS : (1 : ℝ) + ‖(τ : ℂ)‖ ≤ scale τ := by
      have h2 : (0 : ℝ) ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
      simp only [scale]; linarith
    have ht2 : (0 : ℝ) ≤ Work.Residues.tpar τ ^ 2 := by positivity
    have hstep : C₁ * scale τ ≤ (max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1)
        * (scale τ) ^ (max N₀ 1) := by
      calc C₁ * scale τ ≤ C₁ * (scale τ) ^ (max N₀ 1) :=
            mul_le_mul_of_nonneg_left hscaleN hC₁.le
        _ ≤ (max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1) * (scale τ) ^ (max N₀ 1) :=
            mul_le_mul_of_nonneg_right hCN (Real.rpow_nonneg hscale0 _)
    calc ‖E1combo24 ℓ τ‖ ≤ C₁ * (1 + ‖(τ : ℂ)‖) * Work.Residues.tpar τ ^ 2 := h1
      _ ≤ C₁ * scale τ * Work.Residues.tpar τ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hC₁.le) ht2
      _ = C₁ * scale τ * ‖qParamFun τ‖ := by rw [hq]
      _ ≤ (max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1)
            * (scale τ) ^ (max N₀ 1) * ‖qParamFun τ‖ :=
            mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  · have h1 := hcrude τ hτ
    have him : τ.im ≤ H := le_of_lt hHi
    have hqge : Real.exp (-(2 * Real.pi * H)) ≤ ‖qParamFun τ‖ := by
      rw [hq, Work.Residues.tpar_pow_two, Real.exp_le_exp]
      nlinarith [Real.pi_pos, him]
    have hone : (1 : ℝ) ≤ Real.exp (2 * Real.pi * H) * ‖qParamFun τ‖ := by
      have h2 : Real.exp (2 * Real.pi * H) * Real.exp (-(2 * Real.pi * H)) = 1 := by
        rw [← Real.exp_add]
        norm_num
      calc (1 : ℝ) = Real.exp (2 * Real.pi * H) * Real.exp (-(2 * Real.pi * H)) := h2.symm
        _ ≤ Real.exp (2 * Real.pi * H) * ‖qParamFun τ‖ :=
              mul_le_mul_of_nonneg_left hqge hExp.le
    have hscaleN' : (scale τ) ^ N₀ ≤ (scale τ) ^ (max N₀ 1) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left _ _)
    have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
    have hs0 : (0 : ℝ) ≤ (scale τ) ^ (max N₀ 1) := Real.rpow_nonneg hscale0 _
    have hmid : C₀ * (scale τ) ^ (max N₀ 1) * (Real.exp (2 * Real.pi * H) * ‖qParamFun τ‖)
        = (C₀ * Real.exp (2 * Real.pi * H)) * (scale τ) ^ (max N₀ 1) * ‖qParamFun τ‖ := by
      ring
    calc ‖E1combo24 ℓ τ‖ ≤ C₀ * (scale τ) ^ N₀ := h1
      _ ≤ C₀ * (scale τ) ^ (max N₀ 1) := mul_le_mul_of_nonneg_left hscaleN' hC₀.le
      _ ≤ C₀ * (scale τ) ^ (max N₀ 1)
            * (Real.exp (2 * Real.pi * H) * ‖qParamFun τ‖) := by
          have hpos : 0 < C₀ * (scale τ) ^ (max N₀ 1) :=
            mul_pos hC₀ (Real.rpow_pos_of_pos (scale_pos τ) (max N₀ 1))
          exact le_mul_of_one_le_right hpos.le hone
      _ = (C₀ * Real.exp (2 * Real.pi * H)) * (scale τ) ^ (max N₀ 1)
            * ‖qParamFun τ‖ := hmid
      _ ≤ (max C₁ (C₀ * Real.exp (2 * Real.pi * H)) + 1) * (scale τ) ^ (max N₀ 1)
            * ‖qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0N hs0) hq0

end

end Work.Asymptotics.KhatE1
