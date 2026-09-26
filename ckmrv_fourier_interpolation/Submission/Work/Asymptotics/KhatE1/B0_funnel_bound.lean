import Mathlib
import Submission.Work.Asymptotics.KhatE1.B0Defs
import Submission.Work.Asymptotics.KhatE1.B0AuxDefs
import Submission.Work.Asymptotics.KhatE1Core.psi_combo_first_order
import Submission.Work.Asymptotics.KhatE1Core.psi_individual_first_order
import Submission.Work.FunnelNumerics.Lamb_funnel_bound

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `S = 2ψ₂ + ψ₄ - 6Λ₀ + (192Λ₀ - 72)q`, the first-order combination of `ψ₂, ψ₄`. -/
def B0S (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  2 * psi2 ℓ τ + psi4 ℓ τ - 6 * Lam0 ℓ τ
    + (192 * Lam0 ℓ τ - 72) * qParamFun τ

/-- `P₂ = ψ₂ - 2Λ₀`, the individual deviation of `ψ₂`. -/
def B0P2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := psi2 ℓ τ - 2 * Lam0 ℓ τ

/-- **The clearing identity.** Multiplying `Delta_mul_B0` by `3456π` and writing the `ψ`-part
through `S` and `P₂` gives
`3456π·(Δ·B0) = cuspC·V₁ + iτ·V₂ + V₃ + (b·S + (a - 2b)·P₂)`. -/
lemma B0_cleared (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    (3456 : ℂ) * (Real.pi : ℂ) * (DeltaFun τ * B0 ℓ τ)
      = Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ
        + (Complex.I * (τ : ℂ)) * B0V2 τ + B0V3 τ
        + (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ) := by
  rw [Delta_mul_B0]
  simp only [B0S, B0P2, Lam0, B0V1, B0V2, B0V3, B0a, B0b]
  field_simp
  ring

/-- `‖Δ·B0‖ = O(scale^N ‖q‖²)` on the funnel. -/
lemma B0_Delta_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖DeltaFun τ * B0 ℓ τ‖ ≤ C * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := B0V1_isBigOq
  obtain ⟨C2, hC2pos, hC2⟩ := B0V2_isBigOq
  obtain ⟨C3, hC3pos, hC3⟩ := B0V3_isBigOq
  obtain ⟨Cb, hCbpos, hCb⟩ := B0b_isBigOq
  obtain ⟨Ca, hCapos, hCa⟩ := B0a_sub_2B0b_isBigOq
  obtain ⟨CS, NS, hCSpos, hNS, hS⟩ := Work.Asymptotics.KhatE1Core.psi_combo_first_order ℓ
  obtain ⟨Cp, Np, hCppos, hNp, hP2i⟩ :=
    Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp + 1,
    max (max NS Np) 1, ?_, ?_, fun τ hτ => ?_⟩
  · positivity
  · exact le_trans (by norm_num) (le_max_right (max NS Np) 1)
  · set N : ℝ := max (max NS Np) 1 with hNdef
    have hNge : (0 : ℝ) ≤ N := by
      rw [hNdef]; exact le_trans (by norm_num) (le_max_right _ _)
    have h1N : (1 : ℝ) ≤ N := by rw [hNdef]; exact le_max_right _ _
    have hτ1 : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) hτ.2
    have hscale1 : (1 : ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
    have hscalepos : (0 : ℝ) < scale τ := Work.Kernels.scale_pos τ
    have hone : (1 : ℝ) ≤ (scale τ) ^ N := Real.one_le_rpow hscale1 hNge
    have hS0 : (0 : ℝ) ≤ (scale τ) ^ N := le_trans zero_le_one hone
    have hNSle : NS ≤ N := by
      rw [hNdef]; exact le_trans (le_max_left NS Np) (le_max_left _ _)
    have hNple : Np ≤ N := by
      rw [hNdef]; exact le_trans (le_max_right NS Np) (le_max_left _ _)
    have hscaleNS : (scale τ) ^ NS ≤ (scale τ) ^ N :=
      Real.rpow_le_rpow_of_exponent_le hscale1 hNSle
    have hscaleNp : (scale τ) ^ Np ≤ (scale τ) ^ N :=
      Real.rpow_le_rpow_of_exponent_le hscale1 hNple
    have hg0 : (0 : ℝ) ≤ ‖qParamFun τ‖ ^ 2 := sq_nonneg _
    have hq0 : (0 : ℝ) ≤ ‖qParamFun τ‖ := norm_nonneg _
    -- bound for each of the five summands
    have b1 : ‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ‖
        ≤ (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      rw [norm_mul]
      calc ‖Work.Asymptotics.Compact.cuspC ℓ‖ * ‖B0V1 τ‖
          ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ * (C1 * ‖qParamFun τ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hC1 τ hτ1) (norm_nonneg _)
        _ = (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * ‖qParamFun τ‖ ^ 2 := by ring
        _ ≤ (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
            have hnn : (0 : ℝ) ≤ (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * ‖qParamFun τ‖ ^ 2 :=
              by positivity
            calc (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * ‖qParamFun τ‖ ^ 2
                = ((‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * ‖qParamFun τ‖ ^ 2) * 1 := by ring
              _ ≤ ((‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * ‖qParamFun τ‖ ^ 2)
                    * (scale τ) ^ N := mul_le_mul_of_nonneg_left hone hnn
              _ = (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * (scale τ) ^ N
                    * ‖qParamFun τ‖ ^ 2 := by ring
    have b2 : ‖(Complex.I * (τ : ℂ)) * B0V2 τ‖ ≤ C2 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      rw [norm_mul, show ‖Complex.I * (τ : ℂ)‖ = ‖(τ : ℂ)‖ by
        rw [norm_mul, Complex.norm_I, one_mul]]
      calc ‖(τ : ℂ)‖ * ‖B0V2 τ‖ ≤ (scale τ) * (C2 * ‖qParamFun τ‖ ^ 2) :=
            mul_le_mul (Work.Kernels.coe_norm_le_scale τ) (hC2 τ hτ1)
              (norm_nonneg _) hscalepos.le
        _ = C2 * scale τ * ‖qParamFun τ‖ ^ 2 := by ring
        _ ≤ C2 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
            have hle : scale τ ≤ (scale τ) ^ N := by
              have h := Real.rpow_le_rpow_of_exponent_le hscale1 h1N
              rwa [Real.rpow_one] at h
            have h : C2 * scale τ ≤ C2 * (scale τ) ^ N :=
              mul_le_mul_of_nonneg_left hle hC2pos.le
            calc C2 * scale τ * ‖qParamFun τ‖ ^ 2
                = (C2 * scale τ) * ‖qParamFun τ‖ ^ 2 := by ring
              _ ≤ (C2 * (scale τ) ^ N) * ‖qParamFun τ‖ ^ 2 := mul_le_mul_of_nonneg_right h hg0
              _ = C2 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring
    have b3 : ‖B0V3 τ‖ ≤ C3 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      refine le_trans (hC3 τ hτ1) ?_
      have hnn : (0 : ℝ) ≤ C3 * ‖qParamFun τ‖ ^ 2 := by positivity
      calc C3 * ‖qParamFun τ‖ ^ 2 = (C3 * ‖qParamFun τ‖ ^ 2) * 1 := by ring
        _ ≤ (C3 * ‖qParamFun τ‖ ^ 2) * (scale τ) ^ N := mul_le_mul_of_nonneg_left hone hnn
        _ = C3 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring
    have hS' : ‖B0S ℓ τ‖ ≤ CS * (scale τ) ^ NS * ‖qParamFun τ‖ ^ 2 := by
      simpa only [B0S, Lam0] using hS τ hτ
    have hCb' : ‖B0b τ‖ ≤ Cb := by simpa using hCb τ hτ1
    have b4 : ‖B0b τ * B0S ℓ τ‖ ≤ (Cb * CS) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      rw [norm_mul]
      calc ‖B0b τ‖ * ‖B0S ℓ τ‖ ≤ Cb * (CS * (scale τ) ^ NS * ‖qParamFun τ‖ ^ 2) :=
            mul_le_mul hCb' hS' (norm_nonneg _) hCbpos.le
        _ = Cb * CS * (scale τ) ^ NS * ‖qParamFun τ‖ ^ 2 := by ring
        _ ≤ Cb * CS * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
            have h : Cb * CS * (scale τ) ^ NS ≤ Cb * CS * (scale τ) ^ N :=
              mul_le_mul_of_nonneg_left hscaleNS (by positivity)
            calc Cb * CS * (scale τ) ^ NS * ‖qParamFun τ‖ ^ 2
                = (Cb * CS * (scale τ) ^ NS) * ‖qParamFun τ‖ ^ 2 := by ring
              _ ≤ (Cb * CS * (scale τ) ^ N) * ‖qParamFun τ‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right h hg0
              _ = Cb * CS * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring
    have hP2' : ‖B0P2 ℓ τ‖ ≤ Cp * (scale τ) ^ Np * ‖qParamFun τ‖ := by
      simpa only [B0P2, Lam0] using (hP2i τ hτ).1
    have hCa' : ‖B0a τ - 2 * B0b τ‖ ≤ Ca * ‖qParamFun τ‖ := by simpa using hCa τ hτ1
    have b5 : ‖(B0a τ - 2 * B0b τ) * B0P2 ℓ τ‖
        ≤ (Ca * Cp) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      rw [norm_mul]
      calc ‖B0a τ - 2 * B0b τ‖ * ‖B0P2 ℓ τ‖
          ≤ (Ca * ‖qParamFun τ‖) * (Cp * (scale τ) ^ Np * ‖qParamFun τ‖) :=
            mul_le_mul hCa' hP2' (norm_nonneg _) (by positivity)
        _ = Ca * Cp * (scale τ) ^ Np * ‖qParamFun τ‖ ^ 2 := by ring
        _ ≤ Ca * Cp * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
            have h : Ca * Cp * (scale τ) ^ Np ≤ Ca * Cp * (scale τ) ^ N :=
              mul_le_mul_of_nonneg_left hscaleNp (by positivity)
            calc Ca * Cp * (scale τ) ^ Np * ‖qParamFun τ‖ ^ 2
                = (Ca * Cp * (scale τ) ^ Np) * ‖qParamFun τ‖ ^ 2 := by ring
              _ ≤ (Ca * Cp * (scale τ) ^ N) * ‖qParamFun τ‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right h hg0
              _ = Ca * Cp * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring
    have hthat : ‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ
        + B0V3 τ + (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ)‖
        ≤ (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp)
            * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by
      have t1 := norm_add_le
        (Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ + B0V3 τ)
        (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ)
      have t2 := norm_add_le
        (Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ) (B0V3 τ)
      have t3 := norm_add_le (Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ)
        ((Complex.I * (τ : ℂ)) * B0V2 τ)
      have t4 := norm_add_le (B0b τ * B0S ℓ τ) ((B0a τ - 2 * B0b τ) * B0P2 ℓ τ)
      calc ‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ
            + B0V3 τ + (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ)‖
          ≤ ‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ
              + B0V3 τ‖
            + ‖B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ‖ := t1
        _ ≤ (‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ + (Complex.I * (τ : ℂ)) * B0V2 τ‖
              + ‖B0V3 τ‖) + (‖B0b τ * B0S ℓ τ‖ + ‖(B0a τ - 2 * B0b τ) * B0P2 ℓ τ‖) :=
            add_le_add t2 t4
        _ ≤ ((‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ‖
                + ‖(Complex.I * (τ : ℂ)) * B0V2 τ‖) + ‖B0V3 τ‖)
              + (‖B0b τ * B0S ℓ τ‖ + ‖(B0a τ - 2 * B0b τ) * B0P2 ℓ τ‖) := by
            linarith [t3]
        _ ≤ (((‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2
                + C2 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2) + C3 * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2)
              + ((Cb * CS) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2
                + (Ca * Cp) * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2) := by
            exact add_le_add (add_le_add (add_le_add b1 b2) b3) (add_le_add b4 b5)
        _ = (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp)
            * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring
    -- the cleared identity
    have hc : (3456 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (by norm_num) hpi
    have hcast : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hDB : DeltaFun τ * B0 ℓ τ
        = (((3456 : ℂ) * (Real.pi : ℂ))⁻¹) * (Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ
            + (Complex.I * (τ : ℂ)) * B0V2 τ + B0V3 τ
            + (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ)) := by
      rw [← B0_cleared ℓ τ, inv_mul_cancel_left₀ hc]
    rw [hDB, norm_mul, norm_inv, hcast]
    have hinv1 : (3456 * Real.pi)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
    have hSg : (0 : ℝ) ≤ (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := mul_nonneg hS0 hg0
    calc (3456 * Real.pi)⁻¹ * ‖Work.Asymptotics.Compact.cuspC ℓ * B0V1 τ
            + (Complex.I * (τ : ℂ)) * B0V2 τ + B0V3 τ
            + (B0b τ * B0S ℓ τ + (B0a τ - 2 * B0b τ) * B0P2 ℓ τ)‖
        ≤ 1 * ((‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp)
            * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2) :=
          mul_le_mul hinv1 hthat (norm_nonneg _) (by norm_num)
      _ = (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp)
            * ((scale τ) ^ N * ‖qParamFun τ‖ ^ 2) := by rw [one_mul]; ring
      _ ≤ (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp + 1)
            * ((scale τ) ^ N * ‖qParamFun τ‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hSg
          linarith
      _ = (‖Work.Asymptotics.Compact.cuspC ℓ‖ * C1 + C2 + C3 + Cb * CS + Ca * Cp + 1)
            * (scale τ) ^ N * ‖qParamFun τ‖ ^ 2 := by ring

/-- The `z⁰`-coefficient
`B0 ℓ τ = -iτE₆(τ)(j(τ)-240) + (3456π)⁻¹(cuspC ℓ · R8_q1 ℓ τ + R8_p1 ℓ τ)` (see
`Submission/Work/Asymptotics/KhatE1/B0Defs.lean`) satisfies the funnel bound
`O((scale τ)^N ‖q(τ)‖)`.

Route: `Delta_mul_B0` (`B0Defs`) writes `Δ·B0` as a sum of `τ`-atoms and of `ψ₂, ψ₄`; the purely
atomic part is `O(q²)` since each of `E₆E₄³-1-216q`, `ΔE₆-q`, `E₄Δ-q`, `E₄⁴-1-960q` is `O(q²)`
(use the `IsBigOq` two-term expansions of `E₄, E₆, Δ`, e.g. via
`Work.Asymptotics.E4Fun_isBigOq`, `E6Fun_isBigOq`, `DeltaFun_isBigOq`,
`Work.Asymptotics.qParamFun_isBigOq`, or an explicit route with
`Work.Asymptotics.E4Fun_sub_one_explicit`), and the `ψ`-part, after adding the explicit
`Λ₀ := πiτ+cuspC` term `3456Λ₀ + 576(-192Λ₀+72)q + 27648Λ₀q`, is `O(q²)` by
`Work.Asymptotics.KhatE1Core.psi_combo_first_order`
(`‖2ψ₂+ψ₄-6Λ₀+(192Λ₀-72)q‖ ≤ C (scale τ)^N ‖q‖²`); the individual bound
`‖ψ₄ - 2Λ₀‖ ≤ C (scale τ)^N ‖q‖` (resp. for `ψ₂`) is
`Work.Asymptotics.KhatE1Core.psi_individual_first_order` (or follows by combining
`psi_combo_first_order` with `Work.FunnelNumerics.Lamb_funnel_bound`
(`ΔΛ₀ = ψ₄E₄³ - ψ₂E₁₄`), solved as a 2×2 linear system).
Finally `‖Δ τ‖ ≥ c‖q(τ)‖` (`Work.Asymptotics.exists_Delta_Funnel_lower`, both on the funnel)
gives `‖B0‖ ≤ C (scale τ)^N ‖q‖`. -/
theorem B0_funnel_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.KhatE1.B0 ℓ τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨Cd, Nd, hCdpos, hNd, hDb⟩ := B0_Delta_bound ℓ
  obtain ⟨cd, hcdpos, hdlow⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  refine ⟨Cd / cd + 1, Nd, by positivity, hNd, fun τ hτ => ?_⟩
  have hDne : DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hqpos : 0 < ‖qParamFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]; exact Real.exp_pos _
  have hscalepos : (0 : ℝ) < scale τ := Work.Kernels.scale_pos τ
  have hDpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (mul_pos hcdpos hqpos) (by
    have h := hdlow τ hτ
    rwa [← Work.Asymptotics.norm_qParamFun] at h)
  have hlow : cd * ‖qParamFun τ‖ ≤ ‖DeltaFun τ‖ := by
    have h := hdlow τ hτ
    rwa [← Work.Asymptotics.norm_qParamFun] at h
  have hDbd := hDb τ hτ
  have heq : (DeltaFun τ * B0 ℓ τ) / DeltaFun τ = B0 ℓ τ := by
    rw [mul_div_cancel_left₀ _ hDne]
  rw [← heq, norm_div]
  have hstep : ‖DeltaFun τ * B0 ℓ τ‖ / ‖DeltaFun τ‖
      ≤ (Cd * (scale τ) ^ Nd * ‖qParamFun τ‖ ^ 2) / (cd * ‖qParamFun τ‖) := by
    rw [div_le_div_iff₀ hDpos (mul_pos hcdpos hqpos)]
    calc ‖DeltaFun τ * B0 ℓ τ‖ * (cd * ‖qParamFun τ‖)
        ≤ (Cd * (scale τ) ^ Nd * ‖qParamFun τ‖ ^ 2) * (cd * ‖qParamFun τ‖) :=
          mul_le_mul_of_nonneg_right hDbd (mul_nonneg hcdpos.le hqpos.le)
      _ ≤ (Cd * (scale τ) ^ Nd * ‖qParamFun τ‖ ^ 2) * ‖DeltaFun τ‖ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  have hsimp : (Cd * (scale τ) ^ Nd * ‖qParamFun τ‖ ^ 2) / (cd * ‖qParamFun τ‖)
      = (Cd / cd) * (scale τ) ^ Nd * ‖qParamFun τ‖ := by
    field_simp
  rw [hsimp] at hstep
  calc ‖DeltaFun τ * B0 ℓ τ‖ / ‖DeltaFun τ‖
      ≤ (Cd / cd) * (scale τ) ^ Nd * ‖qParamFun τ‖ := hstep
    _ ≤ (Cd / cd + 1) * (scale τ) ^ Nd * ‖qParamFun τ‖ := by
        have hX : (0 : ℝ) ≤ (scale τ) ^ Nd * ‖qParamFun τ‖ :=
          mul_nonneg (Real.rpow_nonneg hscalepos.le Nd) (norm_nonneg _)
        nlinarith [hX]

end

end Work.Asymptotics.KhatE1
