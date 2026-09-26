/-
# Prerequisites for the funnel tail estimates `funnelKernelTail`

This file collects the elementary facts about the *funnel* region

  `Funnel = {τ ∈ 𝒟 : 2 ≤ Im τ}`

of the CKMRV interpolation problem, together with the growth of the `τ`-atoms on it.

Main results:

* `Funnel.im_one`, `Funnel.re_abs_lt_one` : on the funnel the semicircle conditions of `𝒟` are
  automatic, so that `Funnel τ ↔ |Re τ| < 1 ∧ 2 ≤ Im τ`;
* `exists_Delta_Funnel_lower`, `exists_jInvariantFun_Funnel_bound`,
  `exists_E14_div_Delta_Funnel`, `exists_E10_div_Delta_Funnel` : the growth of the `τ`-atoms.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA
import Submission.Work.Asymptotics.cusp_inv_divisor_second
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.cusp_L_second

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-! ## The funnel region -/

/-- The *funnel* `{τ ∈ 𝒟 : 2 ≤ Im τ}` of the tail estimates. -/
def Funnel (τ : ℍ) : Prop := τ ∈ DomainD ∧ 2 ≤ τ.im

namespace Funnel

lemma im_one {τ : ℍ} (h : Funnel τ) : 1 ≤ τ.im := le_trans (by norm_num) h.2

lemma im_two {τ : ℍ} (h : Funnel τ) : 2 ≤ τ.im := h.2

lemma mem_DomainD {τ : ℍ} (h : Funnel τ) : τ ∈ DomainD := h.1

lemma re_abs_lt_one {τ : ℍ} (h : Funnel τ) : |τ.re| < 1 := by
  have h1 := h.1
  rw [Work.Asymptotics.mem_DomainD] at h1
  rw [abs_lt]
  exact ⟨h1.1, h1.2.1⟩

lemma im_le_t {τ : ℍ} {t : ℝ} (h : Funnel τ) (ht : τ.im + 1 ≤ t) : τ.im ≤ t := by
  linarith [h.2]

end Funnel

/-! ## Growth of the `τ`-atoms on the funnel -/

/-- Quotient estimate: `‖f/g‖ ≤ B/(c x)` if `‖f‖ ≤ B` and `c x ≤ ‖g‖`. -/
lemma norm_div_le_of_lower {f g : ℂ} {B c x : ℝ} (hf : ‖f‖ ≤ B) (hg : c * x ≤ ‖g‖)
    (hc : 0 < c) (hx : 0 < x) : ‖f / g‖ ≤ B / (c * x) := by
  rw [norm_div]
  have hcx : 0 < c * x := mul_pos hc hx
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le hcx hg
  have h1 : (‖g‖)⁻¹ ≤ (c * x)⁻¹ := (inv_le_inv₀ hgpos hcx).mpr hg
  calc ‖f‖ / ‖g‖ = ‖f‖ * (‖g‖)⁻¹ := by ring
    _ ≤ B * (c * x)⁻¹ := mul_le_mul hf h1 (inv_nonneg.mpr hgpos.le)
          (le_trans (norm_nonneg f) hf)
    _ = B / (c * x) := by ring

/-- `‖Δ τ‖ ≥ c exp (-2π Im τ)` on the funnel. -/
theorem exists_Delta_Funnel_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, Funnel τ →
      c * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  obtain ⟨c, hc, h⟩ := DeltaFun_lower
  refine ⟨c, hc, fun τ hτ => ?_⟩
  have h1 := h τ (Funnel.im_one hτ)
  rwa [norm_qParamFun] at h1

/-- `‖E₄ τ‖` is bounded on the funnel. -/
theorem exists_E4_Funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E4Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E4Fun_bound
  exact ⟨C, hC, fun τ hτ => h τ (Funnel.im_one hτ)⟩

/-- `‖E₆ τ‖` is bounded on the funnel. -/
theorem exists_E6_Funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E6Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E6Fun_bound
  exact ⟨C, hC, fun τ hτ => h τ (Funnel.im_one hτ)⟩

/-- `‖E₂ τ‖` is bounded on the funnel. -/
theorem exists_E2_Funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E2Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  exact ⟨C, hC, fun τ hτ => h τ (Funnel.im_one hτ)⟩

/-- `‖j τ‖ ≤ C exp (2π Im τ)` on the funnel. -/
theorem exists_jInvariantFun_Funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨B, hB, hB4⟩ := exists_E4_Funnel_bound
  obtain ⟨c, hc, hΔ⟩ := exists_Delta_Funnel_lower
  refine ⟨B ^ 3 / c + 1, by positivity, fun τ hτ => ?_⟩
  have hcoe : Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := rfl
  rw [hcoe]
  have hf : ‖Work.Kernels.E4Fun τ ^ 3‖ ≤ B ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hB4 τ hτ) 3
  have h := norm_div_le_of_lower hf (hΔ τ hτ) hc (Real.exp_pos _)
  have heq : B ^ 3 / (c * Real.exp (-(2 * Real.pi * τ.im)))
      = (B ^ 3 / c) * Real.exp (2 * Real.pi * τ.im) := by
    rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [heq] at h
  calc ‖Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ‖
      ≤ (B ^ 3 / c) * Real.exp (2 * Real.pi * τ.im) := h
    _ ≤ (B ^ 3 / c + 1) * Real.exp (2 * Real.pi * τ.im) := by
        have := Real.exp_pos (2 * Real.pi * τ.im)
        nlinarith [div_nonneg (pow_nonneg hB.le 3) hc.le]

/-- `‖E₁₄ τ / Δ τ‖ ≤ C exp (2π Im τ)` on the funnel. -/
theorem exists_E14_div_Delta_Funnel :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨B4, hB4, h4⟩ := exists_E4_Funnel_bound
  obtain ⟨B6, hB6, h6⟩ := exists_E6_Funnel_bound
  obtain ⟨c, hc, hΔ⟩ := exists_Delta_Funnel_lower
  refine ⟨(B4 ^ 2 * B6) / c + 1, by positivity, fun τ hτ => ?_⟩
  have hf : ‖Work.Kernels.E14Fun τ‖ ≤ B4 ^ 2 * B6 := by
    have heq : Work.Kernels.E14Fun τ = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ := rfl
    rw [heq, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h4 τ hτ) 2) (h6 τ hτ)
      (norm_nonneg _) (by positivity)
  have h := norm_div_le_of_lower hf (hΔ τ hτ) hc (Real.exp_pos _)
  have heq : (B4 ^ 2 * B6) / (c * Real.exp (-(2 * Real.pi * τ.im)))
      = ((B4 ^ 2 * B6) / c) * Real.exp (2 * Real.pi * τ.im) := by
    rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [heq] at h
  calc ‖Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ‖
      ≤ ((B4 ^ 2 * B6) / c) * Real.exp (2 * Real.pi * τ.im) := h
    _ ≤ ((B4 ^ 2 * B6) / c + 1) * Real.exp (2 * Real.pi * τ.im) := by
        have := Real.exp_pos (2 * Real.pi * τ.im)
        nlinarith [div_nonneg (mul_nonneg (pow_nonneg hB4.le 2) hB6.le) hc.le]

/-- `‖E₁₀ τ / Δ τ‖ ≤ C exp (2π Im τ)` on the funnel. -/
theorem exists_E10_div_Delta_Funnel :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
      ‖Work.Kernels.E10Fun τ / Work.Kernels.DeltaFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨B4, hB4, h4⟩ := exists_E4_Funnel_bound
  obtain ⟨B6, hB6, h6⟩ := exists_E6_Funnel_bound
  obtain ⟨c, hc, hΔ⟩ := exists_Delta_Funnel_lower
  refine ⟨(B4 * B6) / c + 1, by positivity, fun τ hτ => ?_⟩
  have hf : ‖Work.Kernels.E10Fun τ‖ ≤ B4 * B6 := by
    have heq : Work.Kernels.E10Fun τ = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ := rfl
    rw [heq, norm_mul]
    exact mul_le_mul (h4 τ hτ) (h6 τ hτ) (norm_nonneg _) hB4.le
  have h := norm_div_le_of_lower hf (hΔ τ hτ) hc (Real.exp_pos _)
  have heq : (B4 * B6) / (c * Real.exp (-(2 * Real.pi * τ.im)))
      = ((B4 * B6) / c) * Real.exp (2 * Real.pi * τ.im) := by
    rw [div_eq_mul_inv, mul_inv, Real.exp_neg, inv_inv]; ring
  rw [heq] at h
  calc ‖Work.Kernels.E10Fun τ / Work.Kernels.DeltaFun τ‖
      ≤ ((B4 * B6) / c) * Real.exp (2 * Real.pi * τ.im) := h
    _ ≤ ((B4 * B6) / c + 1) * Real.exp (2 * Real.pi * τ.im) := by
        have := Real.exp_pos (2 * Real.pi * τ.im)
        nlinarith [div_nonneg (mul_nonneg hB4.le hB6.le) hc.le]

end

end Work.Asymptotics
