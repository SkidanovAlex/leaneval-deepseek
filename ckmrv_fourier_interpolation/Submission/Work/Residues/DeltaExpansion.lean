import Mathlib
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Residues.NormCubeSubSqSharp
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder

/-!
# The second-order cusp expansion of `Δ`

We prove that on the region `Im τ ≥ 1` the discriminant `Δ` differs from the leading term
`E(τ) ^ 2 = e ^ (2 π i τ)` of its `q`-expansion by `O(‖E τ‖ ^ 4)`.

The two ingredients are the second-order cusp expansions
`E₄ = 1 + 240 E² + O(‖E‖⁴)`, `E₆ = 1 - 504 E² + O(‖E‖⁴)` (`E4FunSecondOrder`,
`E6FunSecondOrder`, proved from the `q`-expansion coefficients via `qExpansion_tail_bound`)
and `Δ = (E₄³ - E₆²)/1728`, together with the elementary expansion
`NormCubeSubSqSharp`.
-/

namespace Work.Residues

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold Modular ModularForm

noncomputable section

theorem DeltaExpansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2‖ ≤
        C * ‖Work.Residues.Ept τ‖ ^ 4 := by
  obtain ⟨A, hA0, hA⟩ := E4FunSecondOrder
  obtain ⟨B, hB0, hB⟩ := E6FunSecondOrder
  set ρ : ℝ := Real.exp (-(2 * Real.pi)) with hρdef
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  set K : ℝ := 3 * A + 2 * B + 3 * (|(240:ℝ)| + A * ρ) ^ 2 + ρ * (|(240:ℝ)| + A * ρ) ^ 3
      + (|(-504:ℝ)| + B * ρ) ^ 2 with hKdef
  refine ⟨K / 1728 + 1, by positivity, fun τ hτ => ?_⟩
  have hqE : Work.Kernels.qParamFun τ = Work.Residues.Ept τ ^ 2 := by
    rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
    congr 1; ring
  have hqnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hqE, norm_pow, Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  have hqle : ‖Work.Kernels.qParamFun τ‖ ≤ ρ := by
    rw [hqnorm, hρdef, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  have hz : ‖Work.Kernels.E4Fun τ - 1 - (240:ℝ) * Work.Kernels.qParamFun τ‖
      ≤ A * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    convert hA τ hτ using 2 <;> norm_num
  have hw : ‖Work.Kernels.E6Fun τ - 1 - (-504:ℝ) * Work.Kernels.qParamFun τ‖
      ≤ B * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    convert hB τ hτ using 2 <;> push_cast <;> ring
  have hkey : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
      - (1728:ℂ) * Work.Kernels.qParamFun τ‖ ≤ K * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    have h1 := NormCubeSubSqSharp hA0.le hB0.le hρ0 hρ1 hqle hz hw
    rw [hKdef]
    convert h1 using 3 <;> norm_num
  have hD : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  have hΔ : Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
          - 1728 * Work.Kernels.qParamFun τ) / 1728 := by
    rw [hD, hqE]; ring
  have hq2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Work.Residues.Ept τ‖ ^ 4 := by
    rw [hqE, norm_pow]; ring
  rw [hΔ, norm_div, Complex.norm_ofNat]
  have hs : (0:ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 4 := by positivity
  have h1 : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
      - 1728 * Work.Kernels.qParamFun τ‖ / 1728 ≤ K * ‖Work.Kernels.qParamFun τ‖ ^ 2 / 1728 :=
    div_le_div_of_nonneg_right hkey (by norm_num)
  have h2 : K * ‖Work.Kernels.qParamFun τ‖ ^ 2 / 1728
      ≤ (K / 1728 + 1) * ‖Work.Residues.Ept τ‖ ^ 4 := by
    rw [hq2]; nlinarith [hs]
  linarith [h1, h2]

end

end Work.Residues
