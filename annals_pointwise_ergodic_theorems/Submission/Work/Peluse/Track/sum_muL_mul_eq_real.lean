import Mathlib
import Submission.Work.Peluse.VanDerCorput.sum_muL_mul_eq

/-!
# The real-valued van der Corput weight identity

This is the real-valued form of `Work.Peluse.VanDerCorput.sum_muL_mul_eq`: for a real-valued test
function `φ`, the `μ_L`-weighted average of `φ` over `[-L,L]` equals `L⁻²` times the average of
`φ` over the differences `h₁ - h₂` of pairs in `[L]²`.

The statement is obtained by casting the (already proved) complex-valued identity along
`ℝ → ℂ` and using that `Complex.ofReal` is injective.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Track

/-- **Van der Corput weight, real form.**  For `H > 0` and any `φ : ℤ → ℝ`,
`∑_{a ∈ [-H,H]} μ_H(a) φ(a) = H⁻² ∑_{p ∈ [H]²} φ(p.1 - p.2)`. -/
theorem sum_muL_mul_eq_real {H : ℕ} (hH : 0 < H) (φ : ℤ → ℝ) :
    ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * φ a
      = ((H : ℝ) ^ 2)⁻¹ *
          ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H), φ ((p.1 : ℤ) - (p.2 : ℤ)) := by
  -- The complex-valued identity, applied to the complexification of `φ`.
  have h := Work.Peluse.VanDerCorput.sum_muL_mul_eq (H := H) hH (fun a : ℤ => (φ a : ℂ))
  -- Both sides, cast to `ℂ`, agree; conclude by injectivity of `ℝ → ℂ`.
  have hcast :
      ((∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * φ a : ℝ) : ℂ)
        = (((H : ℝ) ^ 2)⁻¹ *
            ∑ p ∈ (Finset.Icc 1 H).product (Finset.Icc 1 H),
              φ ((p.1 : ℤ) - (p.2 : ℤ)) : ℝ) := by
    push_cast
    exact h
  exact Complex.ofReal_inj.mp hcast

end Work.Peluse.Track
