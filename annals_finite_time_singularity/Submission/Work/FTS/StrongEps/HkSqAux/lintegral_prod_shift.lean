/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/lintegral_prod_shift`

Translation invariance of the (iterated) Lebesgue `lintegral` over `ℝ × ℝ`: shifting both
variables by constants does not change the integral.  This is the two-variable form of
`MeasureTheory.lintegral_sub_right_eq_self`, used in the shift estimate `integral_shift_le`,
where the weight `logJac` is compared with its translate by `(p.1, p.2)`.

The second form, `lintegral_prod_shift_mul`, is the shape in which the lemma is consumed: it
moves the shift from the second factor onto the first, i.e.

  `∫⁻ s ∫⁻ ζ, A s ζ * B (s - p₁) (ζ - p₂) = ∫⁻ s ∫⁻ ζ, A (s + p₁) (ζ + p₂) * B s ζ`.
-/
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false

/-- **Double translation invariance of the Lebesgue integral on `ℝ × ℝ`** (iterated form):
`∫⁻ s ∫⁻ ζ, F (s - p₁) (ζ - p₂) = ∫⁻ s ∫⁻ ζ, F s ζ` for an arbitrary `ENNReal`-valued `F`
(no measurability hypothesis is needed, the `lintegral` is defined for every function). -/
theorem lintegral_prod_shift (F : ℝ → ℝ → ENNReal) (p₁ p₂ : ℝ) :
    (∫⁻ s, ∫⁻ ζ, F (s - p₁) (ζ - p₂)) = ∫⁻ s, ∫⁻ ζ, F s ζ := by
  have h1 : (fun s : ℝ => ∫⁻ ζ, F (s - p₁) (ζ - p₂)) = fun s => ∫⁻ ζ, F (s - p₁) ζ :=
    funext fun s => MeasureTheory.lintegral_sub_right_eq_self (fun ζ => F (s - p₁) ζ) p₂
  rw [h1]
  exact MeasureTheory.lintegral_sub_right_eq_self (fun s => ∫⁻ ζ, F s ζ) p₁

/-- The two-factor form used in `integral_shift_le`: the shift can be moved from the second
factor onto the first. -/
theorem lintegral_prod_shift_mul (A B : ℝ → ℝ → ENNReal) (p₁ p₂ : ℝ) :
    (∫⁻ s, ∫⁻ ζ, A s ζ * B (s - p₁) (ζ - p₂)) = ∫⁻ s, ∫⁻ ζ, A (s + p₁) (ζ + p₂) * B s ζ := by
  have h := lintegral_prod_shift (fun s ζ => A (s + p₁) (ζ + p₂) * B s ζ) p₁ p₂
  simpa [sub_add_cancel] using h

end Work.FTS.StrongEps.HkSqAux
