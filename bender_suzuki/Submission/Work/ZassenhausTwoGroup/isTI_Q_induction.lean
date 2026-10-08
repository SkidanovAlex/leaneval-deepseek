import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Q` is TI in the vocabulary of the delivered induction library

`Work.Induction.indFun_TI_apply` — the TI double-coset formula
`|Q| · Ind_Q^G ζ y = ∑_{x ∈ N_G(Q)} ζ(x y x⁻¹)` (`y ≠ 1`) — needs `Q` to be TI in the sense
`Q ⊓ xQx⁻¹ = ⊥` for `x ∉ N_G(Q)`.  That is exactly `isTI_Q` (`x ∉ H`) plus `N_G(Q) = H`
(`normalizer_Q_eq`), so the two area lemmas are exported here in the form the character-theoretic
computations of Feit's §3 (displays (18) and (20)) consume.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- `Q` is TI in the vocabulary of `Work.Induction`, so the TI double-coset formula
`indFun_TI_apply` is available for the Frobenius kernel `Q`. -/
theorem isTI_Q_induction {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (hQ : Q ≠ ⊥) : Work.Induction.IsTI Q := by
  intro x hx
  have hxH : x ∉ H := by
    rw [← normalizer_Q_eq h hQ]
    exact hx
  exact isTI_Q h hz x hxH

end Work.ZassenhausTwoGroup
