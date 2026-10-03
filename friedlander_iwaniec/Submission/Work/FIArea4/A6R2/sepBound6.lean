import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6psi.psiSum6_le_expLog6

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The round-6 coefficient of `A6R2.Defs` is (definitionally) the `A6psi` one: both are
`2 β_{z₁} conj β_{z₂} (φ(d)/d)(z₂/z₁|d)`, the only difference being the names of the auxiliary
constants `w6` / `S15w6`. -/
lemma coef6_eq_S15coef6 (β : GaussianInt → ℂ) (i : S15Id) :
    coef6 β i = Work.FIArea4.A6psi.S15coef6 β i := rfl

/-- `A6R2.expLog6` is definitionally the `A6psi` exponential sum. -/
lemma expLog6_eq_S15expLog6 (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (u t : ℝ) :
    expLog6 Pa X j β u t = Work.FIArea4.A6psi.S15expLog6 Pa X j β u t := rfl

/-- `A6R2.psiSum6` is definitionally the `A6psi` `ψ`-cut sum. -/
lemma psiSum6_eq_S15psiSum6 (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ)
    (β : GaussianInt → ℂ) :
    psiSum6 Pa X j ψ β = Work.FIArea4.A6psi.S15psiSum6 Pa X j ψ β := rfl

/-- **The separation step** (`FI` (12.13)–(12.14)) for the round-6 ratio symbol, in the `A6R2`
normalisation: `psiSum6` is bounded by `(log N + 1)^2` times a uniform bound for `expLog6`.

This is `Work.FIArea4.A6psi.psiSum6_le_expLog6` (the Fourier–Mellin separation of variables,
`S15red.sep_uniform`), transported along the definitional identifications above. -/
theorem sepBound6 : Work.FIArea4.A6R2.SepBound6 := by
  intro ψ hψ hψsup
  obtain ⟨C, hC, h⟩ := Work.FIArea4.A6psi.psiSum6_le_expLog6 hψ hψsup
  refine ⟨C, hC, ?_⟩
  intro Pa X j φ β M hβ hX hM
  rw [psiSum6_eq_S15psiSum6 Pa X j ψ β]
  exact h Pa X j φ β M hβ hX (fun u t => by
    rw [← expLog6_eq_S15expLog6 Pa X j β u t]
    exact hM u t)

end

end Work.FIArea4.A6R2
