import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Defs
import Submission.Commons.NumberTheory.Chen.bombieri_vinogradov_theta_shift

/-!
# Level of distribution for the shifted `θ`-function, in the `APSwitchUpper` vocabulary

The `APSwitchUpper` remainder sum `bvSum x K` is the Bombieri–Vinogradov remainder

`bvSum x K = Σ_{1 ≤ d ≤ K, d odd} |θ_d(x) − x/φ(d)|`,
   `θ_d(x) = Σ_{p ≤ x, p prime, d ∣ p + 2} log p`,

so the statement below is *verbatim* the `θ`-shifted Bombieri–Vinogradov theorem at
level `√x / (log x)^B`, which is available sorry-free in the commons as
`Commons.NumberTheory.Chen.bombieri_vinogradov_theta_shift` (itself derived from the
family-form Bombieri–Vinogradov theorem and the Chebyshev estimate `ψ − θ = O(√x)`).

The only work here is the definitional comparison: `Work.…bvSum` and
`ChenEight.rD`/`ChenEight.thetaD` unfold to exactly the summand appearing in the
commons statement.
-/

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- The `APSwitchUpper` Bombieri–Vinogradov remainder at level `√x/(log x)^B` is
bounded by `x/(log x)^A` for a suitable `B`, for every `A > 0`. -/
theorem level_of_distribution_theta_shift :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      Work.NumberTheory.Chen.APSwitchUpper.bvSum x
          ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B, hB, h⟩ := Commons.NumberTheory.Chen.bombieri_vinogradov_theta_shift A hA
  exact ⟨B, hB, h⟩

end Work.NumberTheory.Chen.APSwitchUpper
