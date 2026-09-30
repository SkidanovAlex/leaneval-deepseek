import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Uniform lower bound with exponential decay (reflection formula), for
`0 < σ < 1`: `c(σ)·(1+|t|)^{σ−1}·e^{−π|t|/2} ≤ |Γ(σ + i t)|` for all real `t`. -/
theorem gamma_vertical_exp_decay_lower (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|) ≤
        ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by
  -- Euler reflection `Γ(z)·Γ(1-z) = π/sin(πz)` plus the peer *upper* bound
  -- `‖Γ(α + i t)‖ ≤ C(1+|t|)^α·e^{-π|t|/2}` at `α = 1-σ` (a colleague's lemma),
  -- combined with `‖sin(π z)‖ ≤ e^{π|t|}`.  Since `(1+|t|)^{1-σ}·(1+|t|)^{σ-1} = 1`
  -- the two exponential halves match up and give exactly the claimed constant.
  let α : ℝ := 1 - σ
  have hα0 : 0 < α := by
    dsimp [α]
    linarith
  obtain ⟨C, hC0, hC⟩ := gamma_vertical_exp_decay α hα0
  let c : ℝ := Real.pi / C
  have hc0 : 0 < c := by
    dsimp [c]
    exact div_pos Real.pi_pos hC0
  refine ⟨c, hc0, ?_⟩
  intro t
  let z : ℂ := (σ : ℂ) + I * (t : ℂ)
  let E : ℝ := Real.exp (-(Real.pi / 2) * |t|)
  let P : ℝ := 1 + |t|
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hPpowpos : 0 < P ^ (1 - σ) := Real.rpow_pos_of_pos hPpos _
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hCne : C ≠ 0 := ne_of_gt hC0
  -- (1) upper bound on ‖Γ(1 - z)‖, from the peer upper bound at real part α = 1 - σ
  have hB : ‖Complex.Gamma (1 - z)‖ ≤ C * P ^ (1 - σ) * E := by
    have ht' := hC (-t)
    have harg : Complex.Gamma ((α : ℂ) + I * ((-t : ℝ) : ℂ)) =
        Complex.Gamma (1 - z) := by
      congr 1
      dsimp [α, z]
      norm_num
      ring
    have hb : 1 + |(-t : ℝ)| = 1 + |t| := by rw [abs_neg]
    have hpow : (1 + |(-t : ℝ)|) ^ α = P ^ (1 - σ) := by
      dsimp [P, α]
      rw [hb]
    have hexp : Real.exp (-(Real.pi / 2) * |(-t : ℝ)|) = E := by
      dsimp [E]
      rw [abs_neg]
    calc
      ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma ((α : ℂ) + I * ((-t : ℝ) : ℂ))‖ := by rw [harg]
      _ ≤ C * (1 + |(-t : ℝ)|) ^ α * Real.exp (-(Real.pi / 2) * |(-t : ℝ)|) := ht'
      _ = C * P ^ (1 - σ) * E := by rw [hpow, hexp]
  -- (2) |sin(π z)| ≤ exp(π |t|)
  have hS : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |t|) := by
    have h1 := norm_sin_le_exp_abs_im ((Real.pi : ℂ) * z)
    have him : (((Real.pi : ℂ) * z).im) = Real.pi * t := by
      dsimp [z]
      rw [Complex.im_ofReal_mul]
      simp
    calc
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp |(((Real.pi : ℂ) * z).im)| := h1
      _ = Real.exp (Real.pi * |t|) := by
        rw [him]
        congr 1
        rw [abs_mul, abs_of_pos Real.pi_pos]
  -- (3) reflection identity gives ‖Γ z‖·‖Γ(1-z)‖ = π/‖sin(π z)‖ ≥ π·exp(-π|t|)
  have hAB : Real.pi * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by
    have hn := Gamma_mul_Gamma_one_sub_norm z
    have hInv : Real.exp (-(Real.pi * |t|)) ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
      have hstep : (Real.exp (Real.pi * |t|))⁻¹ ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
        have hspos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
          refine norm_pos_iff.mpr ?_
          by_cases ht0 : t = 0
          · intro hs
            have hz0 : z = (σ : ℂ) := by
              dsimp [z]
              rw [ht0]
              simp
            rw [hz0] at hs
            have hsin_real : Complex.sin ((Real.pi : ℂ) * (σ : ℂ)) =
                ((Real.sin (Real.pi * σ) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_mul]
              rw [Complex.ofReal_sin]
            rw [hsin_real] at hs
            have hne : Real.sin (Real.pi * σ) ≠ 0 := by
              have hrange : Real.pi * σ ∈ Set.Ioo 0 Real.pi := by
                constructor <;> nlinarith [Real.pi_pos, Real.pi_gt_three, hσ0, hσ1]
              exact ne_of_gt (Real.sin_pos_of_mem_Ioo hrange)
            exact hne (by exact_mod_cast congrArg Complex.re hs)
          · have hz_im : z.im = t := by simp [z]
            have him : ((Real.pi : ℂ) * z).im ≠ 0 := by
              rw [Complex.im_ofReal_mul, hz_im]
              exact mul_ne_zero (ne_of_gt Real.pi_pos) ht0
            exact sin_ne_zero_of_im_ne_zero him
        simpa using (one_div_le_one_div_of_le hspos hS)
      simpa [Real.exp_neg] using hstep
    calc
      Real.pi * Real.exp (-(Real.pi * |t|)) ≤ Real.pi * (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hInv (le_of_lt Real.pi_pos)
      _ = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by ring
      _ = ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by
        rw [← hn]
  -- (4) since ‖Γ(1-z)‖ ≤ Bmax, we get π·exp(-π|t|) ≤ ‖Γ z‖·Bmax
  have hA0 : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hBmax : C * P ^ (1 - σ) * E > 0 := by
    exact mul_pos (mul_pos hC0 hPpowpos) hEpos
  have hAfin : Real.pi * Real.exp (-(Real.pi * |t|)) ≤
      ‖Complex.Gamma z‖ * (C * P ^ (1 - σ) * E) := by
    calc
      Real.pi * Real.exp (-(Real.pi * |t|)) ≤ ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := hAB
      _ ≤ ‖Complex.Gamma z‖ * (C * P ^ (1 - σ) * E) := by
        exact mul_le_mul_of_nonneg_left hB hA0
  have hdiv : (Real.pi * Real.exp (-(Real.pi * |t|))) / (C * P ^ (1 - σ) * E) ≤
      ‖Complex.Gamma z‖ := by
    exact (div_le_iff₀ hBmax).mpr hAfin
  -- (5) the left-hand side of the claimed bound is exactly this fraction
  have hPr : P ^ (σ - 1) * P ^ (1 - σ) = 1 := by
    have h0 : (σ - 1) + (1 - σ) = 0 := by ring
    rw [← Real.rpow_add hPpos (σ - 1) (1 - σ)]
    rw [h0, Real.rpow_zero]
  have hE2 : E * E = Real.exp (-(Real.pi * |t|)) := by
    dsimp [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hden_ne : C * P ^ (1 - σ) * E ≠ 0 := ne_of_gt hBmax
  have hmain : (Real.pi / C) * P ^ (σ - 1) * E * (C * P ^ (1 - σ) * E)
      = Real.pi * Real.exp (-(Real.pi * |t|)) := by
    calc
      (Real.pi / C) * P ^ (σ - 1) * E * (C * P ^ (1 - σ) * E)
          = (Real.pi / C) * C * (P ^ (σ - 1) * P ^ (1 - σ)) * (E * E) := by ring
      _ = (Real.pi / C) * C * 1 * Real.exp (-(Real.pi * |t|)) := by
        rw [hPr, hE2]
      _ = Real.pi * Real.exp (-(Real.pi * |t|)) := by
        rw [div_mul_cancel₀ Real.pi hCne]
        ring
  have hgoalLHS : c * P ^ (σ - 1) * E =
      (Real.pi * Real.exp (-(Real.pi * |t|))) / (C * P ^ (1 - σ) * E) := by
    dsimp [c]
    rw [eq_div_iff hden_ne]
    rw [hmain]
  -- (6) conclusion
  rw [show ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ = ‖Complex.Gamma z‖ by rfl]
  rw [hgoalLHS]
  exact hdiv

end Commons.Analysis.SpecialFunctions.Gamma
