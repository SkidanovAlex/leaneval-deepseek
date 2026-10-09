import Mathlib
import Submission.NK.ShimizuRank.rankGamma_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ShimizuRank

/-
**`NK.Reconstruct.RankFormulaInput K K ℓ δ` is unsatisfiable** (for every number field `K`, prime
`ℓ` and `δ : ℕ`).

Its `formula` field reads `rankGamma K K ℓ = rComplex K + 1 + δ`, but the left-hand side is `0`
(`NK.ShimizuRank.rankGamma_self`: the ℓ-adic abelianisation of the trivial extension `K/K` is
trivial) while the right-hand side is at least `1`.

Consequence (worth stating in the chapter's report): `NK.Reconstruct.RankFormulaInput K K' ℓ δ` is
only meaningful when `K'` is large enough — for this development, when `K' = Ω` also contains
`K^{(∞,ℓ)}`; it must not be read as an input "for all Galois `K'/K`".

Please declare the result in namespace `NK.ShimizuRank` (module
`Submission.NK.ShimizuRank.not_rankFormulaInput_self`).
-/
theorem not_rankFormulaInput_self (K : Type*) [Field K] [NumberField K] (ℓ δ : ℕ) [Fact ℓ.Prime] :
    ¬ NK.Reconstruct.RankFormulaInput K K ℓ δ := by
  intro h
  have hf := h.formula
  rw [rankGamma_self K ℓ] at hf
  omega

end NK.ShimizuRank
