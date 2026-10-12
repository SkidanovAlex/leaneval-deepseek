import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.SubstHyp` — the algebra-only hypotheses of the substitution

FS `lem:EstimatesOnQ3-js` rewrites `Q₃` in the squeezed modes
`b_k = a_k + α_k a_{−k}†` via `a_k = (1−α_k²)⁻¹(b_k − α_k b_{−k}†)`
(`eq:asInTermsOfbs`).  That step is pure algebra; the *only* inputs are

* FS `eq:Commutator_general` (`hasKernel`), which makes `[b_{s−k},b_{−k}†]` a
  scalar and identifies the two squeezed commutators;
* the parities of `χ̂`, `χ̂²` and `α` (which is what makes the two squeezed
  commutators *equal*, hence the leftover of the two cubic monomials a single
  commutator term `−α_k[b_{s−k},b_{−k}†]∘(ã_s†+ã_s)`);
* the non-vanishing of the substitution denominators `1−α_k²`, `1−α_{s−k}²` on
  the pairs `(s,k)` that occur (i.e. `f_L(s) ≠ 0`, `k ∈ P_H`).

`SubstHyp` collects exactly these, so that the ported algebra
(`Q3T_split`) is proved once and for all; the *derivation* of `SubstHyp` from
the kernel interface `Q3Kernel` at small `t` (nodes `N2`) is a separate,
threshold-carrying step (`Q3Kernel.substHyp`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7

/-- The algebra-only hypotheses of the Bogoliubov substitution
`a_k = (1−α_k²)⁻¹(b_k − α_k b_{−k}†)`: FS's commutator kernel, the parities, and
the non-vanishing of the denominators on the pairs used. -/
structure SubstHyp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
  /-- FS `eq:Commutator_general`. -/
  hasKernel : ∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  /-- `χ̂` is even. -/
  hatChi_even : ∀ s : Mode, E.hatChi (-s) = E.hatChi s
  /-- `χ̂²` is even. -/
  hatChiSq_even : ∀ s : Mode, E.hatChiSq (-s) = E.hatChiSq s
  /-- `α` is even (`α = ℬ/(𝒜+√(𝒜²−ℬ²))` with `𝒜, ℬ` even). -/
  alpha_even : ∀ k : Mode, E.alpha (-k) = E.alpha k
  /-- the substitution denominators do not vanish on the pairs used. -/
  denom_ne : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E →
    1 - E.alpha k ^ 2 ≠ 0 ∧ 1 - E.alpha (s - k) ^ 2 ≠ 0

end Work.BoseB7A
