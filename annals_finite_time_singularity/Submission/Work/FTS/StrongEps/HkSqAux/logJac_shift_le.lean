import Mathlib.Analysis.Complex.Exponential
import Submission.Work.FTS.StrongEps.HkSqAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open scoped Real

namespace Work.FTS.StrongEps.HkSqAux

/-- **The pure angular core of the shift bound.**  The ratio

  `kappa ζ / kappa (ζ - p) = e^p (1 + e^{2ζ-2p}) / (1 + e^{2ζ})`

is bounded by `e^{|p|} = max (e^p) (e^{-p})` (the function `t ↦ (1 + t e^{-2p})/(1+t)` is monotone
and interpolates between `1` and `e^{-2p}`), whence `kappa ζ ≤ e^{2|p|+p} kappa (ζ - p)`.

Concretely, with `D₁ = 1 + e^{2ζ}`, `D₂ = 1 + e^{2(ζ-p)}`, the claim is `1/D₁ ≤ e^{2|p|}/D₂`, i.e.
`D₂ ≤ e^{2|p|} D₁`, which follows from `e^{-2p} ≤ e^{2|p|}` and `1 ≤ e^{2|p|}`. -/
theorem kappa_shift_core (ζ p : ℝ) :
    kappa ζ ≤ Real.exp (2 * |p| + p) * kappa (ζ - p) := by
  have hD1 : 0 < 1 + Real.exp (2 * ζ) := by positivity
  have hD2 : 0 < 1 + Real.exp (2 * (ζ - p)) := by positivity
  have hE : Real.exp (-(2 * p)) ≤ Real.exp (2 * |p|) := by
    rw [Real.exp_le_exp]
    nlinarith [neg_le_abs p]
  have hkey : 1 + Real.exp (2 * (ζ - p)) ≤ Real.exp (2 * |p|) * (1 + Real.exp (2 * ζ)) := by
    have heq : Real.exp (2 * (ζ - p)) = Real.exp (2 * ζ) * Real.exp (-(2 * p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    have h1 : Real.exp (2 * ζ) * Real.exp (-(2 * p)) ≤ Real.exp (2 * ζ) * Real.exp (2 * |p|) :=
      mul_le_mul_of_nonneg_left hE (Real.exp_pos (2 * ζ)).le
    have h2 : (1 : ℝ) ≤ Real.exp (2 * |p|) := Real.one_le_exp (by positivity)
    have h5 : Real.exp (2 * |p|) * Real.exp (2 * ζ) = Real.exp (2 * ζ) * Real.exp (2 * |p|) := by
      ring
    nlinarith [h1, h2, h5]
  have hfrac : (1 : ℝ) / (1 + Real.exp (2 * ζ))
      ≤ Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p))) := by
    rw [div_le_div_iff₀ hD1 hD2]
    linarith [hkey]
  have hmul := mul_le_mul_of_nonneg_left hfrac (Real.exp_pos ζ).le
  have hnum : Real.exp ζ * Real.exp (2 * |p|) = Real.exp (2 * |p| + p) * Real.exp (ζ - p) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [kappa, kappa]
  calc Real.exp ζ / (1 + Real.exp (2 * ζ))
      = Real.exp ζ * (1 / (1 + Real.exp (2 * ζ))) := by rw [div_eq_mul_one_div]
    _ ≤ Real.exp ζ * (Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p)))) := hmul
    _ = Real.exp ζ * Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p))) := by
        rw [mul_div_assoc]
    _ = Real.exp (2 * |p| + p) * Real.exp (ζ - p) / (1 + Real.exp (2 * (ζ - p))) := by
        rw [hnum]
    _ = Real.exp (2 * |p| + p) * (Real.exp (ζ - p) / (1 + Real.exp (2 * (ζ - p)))) := by
        rw [mul_div_assoc]

theorem logJac_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s ζ p₁ p₂ : ℝ,
      Work.FTS.StrongEps.HkSqAux.logJac s ζ
        ≤ Real.exp (C * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂) := by
  refine ⟨4, by norm_num, fun s ζ p₁ p₂ => ?_⟩
  have hκ := kappa_shift_core ζ p₂
  -- the exponent gap left over from the two shifts is absorbed by `C = 4`
  have hexpmono : Real.exp (2 * |p₂| + p₂) ≤ Real.exp (4 * (|p₁| + |p₂|) - p₁) := by
    rw [Real.exp_le_exp]
    nlinarith [le_abs_self p₁, le_abs_self p₂, abs_nonneg p₁, abs_nonneg p₂]
  have hstep : kappa ζ ≤ Real.exp (4 * (|p₁| + |p₂|) - p₁) * kappa (ζ - p₂) :=
    le_trans hκ (mul_le_mul_of_nonneg_right hexpmono (kappa_nonneg _))
  have hE4 : Real.exp s * Real.exp (4 * (|p₁| + |p₂|) - p₁)
      = Real.exp (4 * (|p₁| + |p₂|)) * Real.exp (s - p₁) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [logJac, logJac]
  calc Real.exp s * kappa ζ
      ≤ Real.exp s * (Real.exp (4 * (|p₁| + |p₂|) - p₁) * kappa (ζ - p₂)) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos s).le
    _ = (Real.exp s * Real.exp (4 * (|p₁| + |p₂|) - p₁)) * kappa (ζ - p₂) := by ring
    _ = (Real.exp (4 * (|p₁| + |p₂|)) * Real.exp (s - p₁)) * kappa (ζ - p₂) := by rw [hE4]
    _ = Real.exp (4 * (|p₁| + |p₂|)) * (Real.exp (s - p₁) * kappa (ζ - p₂)) := by ring

end Work.FTS.StrongEps.HkSqAux
